/- Prefix-scoped trusted kernel replay for the banded-policy mirror.

Adapted from autoformalizer `lean/trusted/Replay.lean` (2026-10-11 version, toolkit
`_toolkit/autoformalizer`), which is hard-wired to `Paper.*` modules. The kernel part is
unchanged: each module in scope is re-added declaration by declaration through the kernel
with checking ON (`Lean.Environment.replay`) on top of an environment holding only its
imports, loaded with `loadExts := false` (no environment extensions or initializers run);
every stored constant must be present in the replayed environment and structurally equal to
what the kernel accepted (`firstMismatch`); axioms are read from the KERNEL-accepted
environment (`collectAxioms`).

Differences from the autoformalizer script, all scoping:
* the modules replayed are every module in the import closure of the requested modules
  whose name starts with one of the given prefixes (default use: `TableGeneration`, i.e.
  all of STO plus the mirror), not `Paper.*`;
* the run-library location checks (stray oleans, `Paper/` root) are dropped: the oleans
  live in this Lake project's `.lake/build`;
* the strong constant hashing / statement pin is not computed; the JSON reports, per
  theorem, the pretty-printed type and its axioms.

Usage (cwd = project root):
  lake env lean --run scripts/trusted/ReplayPrefix.lean -- <nonce> <prefix,prefix,...> <module> [<module> ...]
-/
import Lean
open Lean Meta

structure ConstRep where
  name : String
  module : String
  kind : String
  typeHash : String
  valueHash : String

structure DeclReport where
  name : String
  kind : String
  typeFull : String
  axioms : Array String
  hasSorry : Bool
  nameN : Name := .anonymous
  consts : Array ConstRep := #[]

def isPaper (n : Name) : Bool := n.getRoot == `Paper

/-- Case-insensitive on the extension: `X.OLEAN` is the same file as `X.olean` on Windows. -/
def isOlean (p : System.FilePath) : Bool := p.extension.map String.toLower == some "olean"

/-- Every `.olean` under `lib` must live under `lib/Paper/`. -/
partial def walkOleans (p : System.FilePath) : IO (Array String) := do
  let mut acc := #[]
  for e in (← p.readDir) do
    if (← e.path.isDir) then acc := acc ++ (← walkOleans e.path)
    else if isOlean e.path then acc := acc.push e.path.toString
  return acc

def strayOleans (lib : System.FilePath) : IO (Array String) := do
  let mut out := #[]
  for e in (← lib.readDir) do
    if (← e.path.isDir) then
      if e.fileName != "Paper" then
        out := out ++ (← walkOleans e.path)
    else if isOlean e.path then
      out := out.push e.path.toString
  return out

def kindOf : ConstantInfo → String
  | .thmInfo _ => "theorem" | .defnInfo _ => "def" | .axiomInfo _ => "axiom" | .opaqueInfo _ => "opaque"
  | .inductInfo _ => "inductive" | .ctorInfo _ => "ctor" | .recInfo _ => "rec" | .quotInfo _ => "quot"

def skippable (ci : ConstantInfo) : Bool := ci.isUnsafe || ci.isPartial

/-- `(type_hash, value_hash)` of a constant: `Expr.hash` of the type mixed with the universe parameter names, and of the
value (`""` when the constant has none: axioms, inductives, constructors, recursors, quotients). -/
def hashesOf (ci : ConstantInfo) : String × String :=
  let th := mixHash (hash ci.levelParams) ci.type.hash
  let vh := match ci.value? (allowOpaque := true) with
    | some v => toString v.hash
    | none => ""
  (toString th, vh)

/-- Length-prefixed (unambiguous) rendering of a name: `.<bytes>:<str>` per string component, `#<k>` per numeric one. -/
def nameKey : Name → String
  | .anonymous => "_"
  | .str p s => nameKey p ++ "." ++ toString s.utf8ByteSize ++ ":" ++ s
  | .num p k => nameKey p ++ "#" ++ toString k

def levelKey : Level → String
  | .zero => "0"
  | .succ l => "s(" ++ levelKey l ++ ")"
  | .max a b => "m(" ++ levelKey a ++ "," ++ levelKey b ++ ")"
  | .imax a b => "i(" ++ levelKey a ++ "," ++ levelKey b ++ ")"
  | .param n => "p(" ++ nameKey n ++ ")"
  | .mvar m => "?(" ++ nameKey m.name ++ ")"

structure RenderState where
  ids : Std.HashMap Expr Nat := {}
  out : String := ""
  next : Nat := 0
  over : Bool := false

/-- Hash-consed rendering of an `Expr`: every distinct subterm (up to `Expr.eqv`, i.e. alpha-equivalence; binder names and
binder info are not rendered, mdata is transparent) gets one line `<id>=<node>` in post-order, children by id. Two
renderings are equal iff the terms are alpha-equivalent; the size is linear in the DAG, never exponential. -/
partial def renderE (cap : Nat) (e : Expr) : StateM RenderState Nat := do
  let st ← get
  if st.over then return 0
  if let some i := st.ids[e]? then return i
  if let .mdata _ x := e then
    let i ← renderE cap x
    modify fun st => { st with ids := st.ids.insert e i }
    return i
  let body ← match e with
    | .bvar i => pure s!"B{i}"
    | .fvar f => pure s!"F{nameKey f.name}"
    | .mvar m => pure s!"M{nameKey m.name}"
    | .sort l => pure s!"S{levelKey l}"
    | .const n ls => pure s!"C{nameKey n}[{",".intercalate (ls.map levelKey)}]"
    | .app f a => do let i ← renderE cap f; let j ← renderE cap a; pure s!"A{i},{j}"
    | .lam _ t b _ => do let i ← renderE cap t; let j ← renderE cap b; pure s!"L{i},{j}"
    | .forallE _ t b _ => do let i ← renderE cap t; let j ← renderE cap b; pure s!"P{i},{j}"
    | .letE _ t v b nd => do
        let i ← renderE cap t; let j ← renderE cap v; let k ← renderE cap b; pure s!"D{i},{j},{k},{nd}"
    | .lit (.natVal n) => pure s!"N{n}"
    | .lit (.strVal x) => pure s!"T{x.utf8ByteSize}:{x}"
    | .proj sn i x => do let j ← renderE cap x; pure s!"J{nameKey sn},{i},{j}"
    | .mdata _ x => renderE cap x >>= fun i => pure s!"I{i}"            -- unreachable (handled above)
  let st ← get                                           -- after the children: their ids are already assigned
  let id := st.next
  let out := st.out ++ s!"{id}={body}\n"
  set { st with ids := st.ids.insert e id, out, next := id + 1, over := st.over || out.utf8ByteSize > cap }
  return id

/-- The rendering of one or more expressions (sharing one id table), or `none` when it exceeds `cap` bytes. -/
def renderAll (cap : Nat) (header : String) (es : List Expr) : Option String :=
  let act : StateM RenderState (List Nat) := es.mapM (renderE cap)
  let (roots, st) := act.run { out := header ++ "\n" }
  let out := st.out ++ "roots " ++ ",".intercalate (roots.map toString) ++ "\n"
  if st.over || out.utf8ByteSize > cap then none else some out

/-- `(type_render, value_render)` of a constant (`none` = oversized). The type rendering carries the kind, the universe
parameters, the safety flag and the type; the value rendering carries the value (definitions, theorems, opaques) and the
structural fields of inductives / constructors / recursors / quotients. -/
def renderConst (cap : Nat) (ci : ConstantInfo) : Option (String × String) := do
  let lps := ",".intercalate (ci.levelParams.map nameKey)
  let t ← renderAll cap s!"{kindOf ci} lps[{lps}] unsafe={ci.isUnsafe} partial={ci.isPartial}" [ci.type]
  let names (ns : List Name) := ",".intercalate (ns.map nameKey)
  let v ← match ci with
    | .defnInfo d => renderAll cap "defn" [d.value]
    | .thmInfo _ => some ""                              -- proof irrelevance: a theorem is its type (value_hash "irrelevant")
    | .opaqueInfo d => renderAll cap s!"opaque {d.isUnsafe}" [d.value]
    | .axiomInfo d => some s!"axiom {d.isUnsafe}\n"
    | .quotInfo d =>
        some ("quot " ++ (match d.kind with | .type => "type" | .ctor => "ctor" | .lift => "lift" | .ind => "ind") ++ "\n")
    | .inductInfo d => some s!"ind {d.numParams} {d.numIndices} all[{names d.all}] ctors[{names d.ctors}] {d.numNested} {d.isRec} {d.isReflexive}\n"
    | .ctorInfo d => some s!"ctor {nameKey d.induct} {d.cidx} {d.numParams} {d.numFields}\n"
    | .recInfo d =>
        renderAll cap (s!"rec all[{names d.all}] {d.numParams} {d.numIndices} {d.numMotives} {d.numMinors} {d.k} rules[" ++
          ",".intercalate (d.rules.map fun r => s!"{nameKey r.ctor}/{r.nfields}") ++ "]") (d.rules.map (·.rhs))
  return (t, v)

def moduleOf (env : Environment) (n : Name) : Name :=
  match env.getModuleIdxFor? n with
  | some i => env.header.moduleNames[i.toNat]!
  | none => .anonymous

/-- The transitive constant closure of `roots` (see the header): expanded only through `Paper.*`-module constants. -/
def constClosure (env : Environment) (roots : Array Name) : Array ConstRep := Id.run do
  let mut seen : NameSet := {}
  let mut work := roots
  let mut out : Array ConstRep := #[]
  while !work.isEmpty do
    let n := work.back!
    work := work.pop
    if seen.contains n then continue
    seen := seen.insert n
    let m := moduleOf env n
    match env.find? n with
    | none =>
      out := out.push { name := n.toString, module := m.toString, kind := "missing", typeHash := "", valueHash := "" }
    | some ci =>
      -- a Paper.* constant's hashes are filled by Python (sha256 of its `module_consts` rendering)
      let (th, vh) := if isPaper m then ("", "") else hashesOf ci
      out := out.push { name := n.toString, module := m.toString, kind := kindOf ci, typeHash := th, valueHash := vh }
      if isPaper m then
        work := work ++ ci.type.getUsedConstants
        -- a theorem's value (its proof) never enters the closure: by proof irrelevance only its type is bound
        if kindOf ci != "theorem" then
          if let some v := ci.value? (allowOpaque := true) then
            work := work ++ v.getUsedConstants
        match ci with
        | .inductInfo v => work := work ++ v.ctors.toArray
        | .ctorInfo v => work := work.push v.induct
        | _ => pure ()
  return out

/-- Every constant a module stores with its type/value RENDERINGS (in the `typeHash`/`valueHash` slots; emitted as
`type_render`/`value_render`), or the name of the first constant whose rendering exceeds `cap`. -/
def moduleConsts (cap : Nat) (data : ModuleData) : Except String (Array ConstRep) := do
  let mut out := #[]
  for ci in data.constants do
    let some (tr, vr) := renderConst cap ci | throw ci.name.toString
    out := out.push { name := ci.name.toString, module := "", kind := if skippable ci then "unchecked" else kindOf ci,
                      typeHash := tr, valueHash := vr }
  return out

/-- Re-add the module's own constants to a fresh environment holding only its imports, kernel-checked. -/
def replayModule (data : ModuleData) : IO (Except String Environment) := do
  let env0 ← importModules data.imports {} 0 (loadExts := false)
  let mut consts : Std.HashMap Name ConstantInfo := {}
  for ci in data.constants do
    consts := consts.insert ci.name ci
  try
    return .ok (← env0.replay consts)
  catch e =>
    return .error (toString e)

/-- Structural equality of a stored constant and the constant the kernel accepted under the same name. -/
def sameConst (stored kernel : ConstantInfo) : Bool :=
  kindOf stored == kindOf kernel && stored.levelParams == kernel.levelParams && stored.type == kernel.type &&
  stored.value? (allowOpaque := true) == kernel.value? (allowOpaque := true) && stored.isUnsafe == kernel.isUnsafe &&
  match stored, kernel with
  | .inductInfo a, .inductInfo b =>
      a.numParams == b.numParams && a.numIndices == b.numIndices && a.all == b.all && a.ctors == b.ctors &&
      a.numNested == b.numNested && a.isRec == b.isRec && a.isReflexive == b.isReflexive
  | .ctorInfo a, .ctorInfo b => a == b
  | .recInfo a, .recInfo b => a == b
  | _, _ => true

/-- `Environment.replay` trusts the stored `InductiveVal.all` lists and skips unsafe/partial constants, so a crafted
olean can make it skip a declaration without an error. Every stored constant must therefore be present in the replayed
environment and structurally equal to what the kernel accepted. The one exception: an unsafe or partial constant
(e.g. the `f._unsafe_rec` Lean adds for every compiled recursive `def`), which `replay` skips by design, may be absent;
it is reported `unchecked`. Sound because nothing the kernel accepted can reference a constant absent from the replayed
environment, and a theorem is never unsafe/partial. Returns the first offender. -/
def firstMismatch (env : Environment) (data : ModuleData) : Option Name :=
  data.constants.findSome? fun ci => match env.find? ci.name with
    | some kc => if sameConst ci kc then none else some ci.name
    | none => if skippable ci then none else some ci.name

/-- Reports read from the KERNEL-accepted constant (`env.find?`), never from the olean's stored `ConstantInfo`. -/
def report (env : Environment) (data : ModuleData) : MetaM (Array DeclReport) := do
  let mut out := #[]
  for stored in data.constants do
    let some ci := env.find? stored.name
      | if skippable stored then
          out := out.push { name := stored.name.toString, kind := "unchecked", typeFull := "", axioms := #[],
                            hasSorry := false, nameN := stored.name }
          continue
        else throwError "{stored.name}: not in the replayed environment"
    let kind := kindOf ci
    let axs ← collectAxioms ci.name
    let fmt ← ppExpr ci.type
    out := out.push { name := ci.name.toString, kind, typeFull := fmt.pretty 100000,
                      axioms := axs.map (·.toString), hasSorry := axs.contains ``sorryAx, nameN := ci.name }
  return out


def underPrefix (pfx : List Name) (n : Name) : Bool := pfx.any (·.isPrefixOf n)

def main (args : List String) : IO UInt32 := do
  let args := match args with | "--" :: rest => rest | _ => args
  let nonce :: pfxArg :: mods := args | IO.eprintln "usage: nonce prefixes module..."; return 2
  let pfx := (pfxArg.splitOn ",").map String.toName
  let requested := mods.map String.toName
  initSearchPath (← findSysroot)
  IO.println s!"AF_TRUSTED_{nonce}"
  try
    let env ← importModules (requested.toArray.map fun m => ({ module := m } : Import)) {} 0 (loadExts := false)
    let names := env.header.moduleNames
    let datas := env.header.moduleData
    let mut done : Array String := #[]
    let mut thms : Array Json := #[]
    let mut ndecls := 0
    for h : i in [0:names.size] do
      let n := names[i]
      if !underPrefix pfx n then continue
      let some data := datas[i]? | throw (IO.userError s!"{n}: no module data")
      let t0 ← IO.monoMsNow
      match ← replayModule data with
      | .error e =>
          IO.println (Json.mkObj [("verdict", Json.str s!"rejected: {n}: {e}"), ("modules", Json.arr (done.map Json.str))]).compress
          return 1
      | .ok env' =>
        if let some bad := firstMismatch env' data then
          IO.println (Json.mkObj [("verdict", Json.str s!"rejected: {n}: {bad}: replayed constant differs from stored")]).compress
          return 1
        let ds ← (report env' data).run' {} {} |>.toIO'
          { fileName := "<replay>", fileMap := default } { env := env' }
        ndecls := ndecls + ds.size
        for r in ds do
          if r.kind == "theorem" then
            let mirror := (`TableGeneration.RecursiveCost.BandedPolicy).isPrefixOf n || (`TableGeneration.RecursiveCost.PTP).isPrefixOf n
            thms := thms.push (Json.mkObj [("name", Json.str r.name), ("module", Json.str n.toString),
              ("axioms", Json.arr (r.axioms.map Json.str)), ("sorry", Json.bool r.hasSorry),
              ("type", Json.str (if mirror then r.typeFull else ""))])
        let t1 ← IO.monoMsNow
        done := done.push s!"{n} ({ds.size} decls, {t1 - t0} ms)"
    IO.println (Json.mkObj [("verdict", Json.str "replayed"), ("modules", Json.arr (done.map Json.str)),
      ("decls", Json.num ndecls), ("closure_has_init", Json.bool (names.contains `Init.Prelude)),
      ("theorems", Json.arr thms)]).compress
    return 0
  catch e =>
    IO.println (Json.mkObj [("verdict", Json.str s!"rejected: {e}")]).compress
    return 1
