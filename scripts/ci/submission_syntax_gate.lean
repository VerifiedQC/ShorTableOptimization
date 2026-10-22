/-
Structural gate on a submission's Lean sources.

`verifier.py`'s banned-token scan is a regex blocklist over text with the
comments stripped by hand. That approach has to re-implement Lean's lexer, and
every construct where a quote or a comment opener is data rather than a
delimiter is a chance to desynchronise from it. Five such constructs were found
and patched by hand; there is no argument that a sixth does not exist.

This gate asks Lean instead. It parses each file with the stock grammar and
judges the resulting syntax tree, so comments, string literals, character
literals, raw strings and guillemet identifiers are handled by the same code
that will later compile the file. It PARSES ONLY -- nothing in the submitted
file is elaborated, so no `#eval`, `initialize` or macro in it runs.

It does NOT replace the blocklist, and the two are not nested: `sorry`,
`axiom`, `unsafe`, `extern`, `implemented_by` and `native_decide` are all a
`declaration` or an attribute inside one, so this gate admits them and the
blocklist is still the only thing refusing them. What this adds, and the
blocklist cannot have, is three allowlists:

* imports, read from the parsed header. The regex in `verify_submission_imports`
  matches one import per line; Lean accepts `import A import B` on one line and
  takes both. Reading the header's parse tree closes that.

* command kinds. A submission is declarations, namespaces, sections, `open`,
  `set_option` and module docs. Anything else -- `#eval`, `macro`, `elab`,
  `syntax`, `initialize`, `notation`, `attribute` -- is refused by exact kind,
  so a command form a future Lean adds is refused rather than admitted.

* options, with ceilings, at EVERY syntactic position. `set_option` is a
  command, a term and a tactic; the three are distinct syntax kinds and a check
  that looks at commands alone leaves the other two unbounded. Ceilings are the
  archive's own maxima. This is what refuses `debug.skipKernelTC`: that option
  makes `addDecl` skip kernel typechecking, and the propext-only axiom audit
  does NOT catch it, because the audit then reports the axioms of a term the
  kernel never checked.

Ceilings are read from the parsed numeral, so `0x7FFFFFFF`, a value on the next
line and any spacing are all handled; the regex sees none of those.

Usage: lake env lean --run submission_syntax_gate.lean FILE [FILE...]
Exit 0 if every file is clean, 1 otherwise, with one line per violation.
-/
import Lean
open Lean Parser

/-- Module prefixes a submitted file may import. Mirrors
    `ALLOWED_IMPORT_PREFIXES` in `verifier.py`; a trailing dot means the
    prefix itself is not importable, only modules under it. -/
def allowedImportPrefixes : List String :=
  [ "TableGeneration.Basic"
  , "TableGeneration.Language"
  , "TableGeneration.Spec"
  , "TableGeneration.Metrics"
  , "TableGeneration.Policy"
  , "TableGeneration.Baseline"
  , "TableGeneration.Submission.Policy"
  , "TableGeneration.Policies.Accepted." ]

def importAllowed (m : String) : Bool :=
  allowedImportPrefixes.any fun p =>
    if p.endsWith "." then m.startsWith p
    else m == p || m.startsWith (p ++ ".")

/-- Command kinds a submission may contain. Matched by exact kind: anything
    not listed here is refused, whatever namespace it lives in. -/
def allowedCommands : List Name :=
  [ ``Lean.Parser.Command.declaration
  , ``Lean.Parser.Command.namespace
  , ``Lean.Parser.Command.section
  , ``Lean.Parser.Command.end
  , ``Lean.Parser.Command.open
  , ``Lean.Parser.Command.variable
  , ``Lean.Parser.Command.universe
  , ``Lean.Parser.Command.mutual
  , ``Lean.Parser.Command.set_option
  , ``Lean.Parser.Command.in
  , ``Lean.Parser.Command.moduleDoc
  , ``Lean.Parser.Command.eoi ]

/-- The three syntax kinds `set_option` has. All three share a shape: the
    option name is child 1 and its value is child 3. -/
def setOptionKinds : List Name :=
  [ ``Lean.Parser.Command.set_option
  , ``Lean.Parser.Term.set_option
  , ``Lean.Parser.Tactic.set_option ]

/-- Options a submission may set, with the largest value it may give. Each
    ceiling is the archive's own maximum, deliberately not above it: Lean
    aborts with a stack overflow well below `maxRecDepth 10^6`, so a looser
    ceiling would admit a value that crashes the toolchain. -/
def optionCeilings : List (Name × Nat) :=
  [ (`maxHeartbeats, 1000000000)
  , (`maxRecDepth, 100000)
  , (`exponentiation.threshold, 512) ]

partial def allNodes (s : Syntax) : Array Syntax :=
  s.getArgs.foldl (fun acc c => acc ++ allNodes c) #[s]

/-- The commands a top-level syntax actually introduces. `set_option x in decl`
    parses as one `Command.in` wrapping both, so unwrap it rather than walking
    the whole tree: a declaration's internal nodes are also named
    `Lean.Parser.Command.*` and are not commands. -/
partial def topCommands (stx : Syntax) : Array Syntax :=
  match stx with
  | .node _ k args =>
      if k == ``Lean.Parser.Command.in then
        args.foldl (fun acc c => acc ++ topCommands c) #[]
      else
        #[stx]
  -- The literal `in` separating the two is an atom, and an atom's kind is its
  -- own text. Only nodes are commands.
  | _ => #[]

def lineOf (ictx : InputContext) (n : Syntax) : Nat :=
  match n.getPos? with
  | some p => (ictx.fileMap.toPosition p).line
  | none   => 0

/-- Refuse any `set_option` outside the allowlist, at any syntactic position. -/
def checkOptions (ictx : InputContext) (path : String) (stx : Syntax) : Array String := Id.run do
  let mut out : Array String := #[]
  for n in allNodes stx do
    if setOptionKinds.contains n.getKind then
      let name := n[1].getId
      let line := lineOf ictx n
      match optionCeilings.find? (fun p => p.1 == name) with
      | none =>
          out := out.push s!"{path}:{line}: set_option `{name}` is not permitted in a submission"
      | some (_, ceiling) =>
          match n[3].isNatLit? with
          | some v =>
              -- 0 means "no ceiling" for both maxHeartbeats and maxRecDepth.
              if v == 0 || v > ceiling then
                out := out.push s!"{path}:{line}: set_option `{name} {v}` exceeds the ceiling {ceiling}"
          | none =>
              out := out.push s!"{path}:{line}: set_option `{name}` must be given a numeric literal"
  return out

/-- The parser environment, built once from a FIXED list of trusted modules.

Deliberately NOT built from each file's own header. The gate only needs the
notation of the contract modules in order to read a file; it never elaborates,
so it does not need the file's imports to resolve. Using the file's header
would mean a submission's own `Policy/` helper modules had to be compiled
first, which they are not -- this gate runs before the build, and the restored
cache is keyed off the base branch, so a new helper module can never be in it.
Every multi-file submission would then be rejected for a missing olean.

It is also what keeps the parse-only guarantee true of the step and not just of
the file. `Elab.processHeader` imports for real and module initializers run, so
a header the submission chose would be a header the submission executes. This
one is fixed and trusted, and the file's own header is checked as data. -/
unsafe def trustedEnv : IO Environment := do
  let header := "import TableGeneration.Policy\nimport TableGeneration.Baseline\nimport TableGeneration.Metrics\nimport TableGeneration.Spec\n"
  let ictx := mkInputContext header "<gate-trusted-header>"
  let (hdr, _, msgs) ← parseHeader ictx
  let (env, _) ← Elab.processHeader hdr {} msgs ictx
  return env

unsafe def checkFile (env : Environment) (path : String) : IO (Array String) := do
  let input ← IO.FS.readFile path
  let ictx := mkInputContext input path
  let (header, state, msgs) ← parseHeader ictx
  let pmctx : ParserModuleContext :=
    { env := env, options := {}, currNamespace := .anonymous, openDecls := [] }
  let mut out : Array String := #[]
  -- The header, as Lean reads it rather than as a line-anchored regex does.
  for n in allNodes header do
    if n.getKind == ``Lean.Parser.Module.import then
      let m := (n.getArgs.findSome? fun a => if a.isIdent then some a.getId else none).getD .anonymous
      if !importAllowed m.toString then
        out := out.push s!"{path}:{lineOf ictx n}: import `{m}` is not permitted in a submission"
  let mut st := state
  let mut log := msgs
  repeat
    let (stx, st', log') := parseCommand ictx pmctx st log
    for n in topCommands stx do
      if !(allowedCommands.contains n.getKind) then
        out := out.push
          s!"{path}:{lineOf ictx n}: command `{n.getKind}` is not permitted in a submission"
    out := out ++ checkOptions ictx path stx
    if Parser.isTerminalCommand stx then break
    -- `parseCommand` either consumes input or returns the terminal `eoi`, so
    -- this cannot fire. It is here because the alternative to proving that is a
    -- CI job that hangs, and because a bound on how much of a file is read is
    -- exactly the kind of thing a submission would otherwise get to choose.
    if st'.pos == st.pos then
      out := out.push s!"{path}:{(ictx.fileMap.toPosition st.pos).line}: the parser stopped making progress"
      break
    st := st'; log := log'
  -- A file that will not parse under the stock grammar is refused: the gate
  -- cannot judge what it cannot read.
  for m in log.toList do
    if m.severity == MessageSeverity.error then
      out := out.push s!"{path}:{m.pos.line}: parse error: {(← m.data.toString)}"
  return out

unsafe def main (args : List String) : IO UInt32 := do
  if args.isEmpty then
    IO.eprintln "usage: submission_syntax_gate.lean FILE [FILE...]"
    return 2
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let env ← trustedEnv
  let mut failures : Array String := #[]
  for a in args do
    failures := failures ++ (← checkFile env a)
  if failures.isEmpty then
    IO.println s!"submission syntax gate: {args.length} file(s) clean"
    return 0
  for f in failures do
    IO.println f
  IO.println s!"submission syntax gate: {failures.size} violation(s)"
  return 1
