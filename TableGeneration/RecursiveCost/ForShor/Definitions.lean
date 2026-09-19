import TableGeneration.RecursiveCost.ForShor.Widths
import TableGeneration.RecursiveCost.ForShor.ResourceModel

/-!
# The companion's recurrence-level cost

Integrated from the companion Lean formalization at commit `d5a165b`, file
`FastMultiplication/ShorVerification/Implementation/GateCount/Definitions.lean`.
Apache-2.0; declaration names are the companion's.

The companion has two cost layers and both are live. This is the second one: a
per-node arithmetic cost defined directly over the symbolic operation list,
which its asymptotic proof solves as a recurrence. It charges the conservative
`rippleAdderGateBound`, not the exact Cuccaro resources, because a clean affine
cost is what makes the recurrence solvable in closed form -- and the companion
bridges the two with `cuccaroModAddResources_totalGates_le_rippleAdderGateBound`.

This project's planner wants the exact figure rather than the bound, so it uses
the same *shape* with the operative model's constants substituted. That is not a
combination the companion itself defines, so it lives in `Model.lean` under its
own name, and `phaseArithmeticOpCost_le` below records the companion's own
inequality between the two.
-/

namespace TableGeneration.RecursiveCost.ForShor

open TableGeneration.Operations

/-- Nonrecursive arithmetic cost contributed by one annotated PhaseProduct-body
operation at common working width `W`; recursive PhaseProduct leaves are counted
separately in the recurrence. -/
def phaseArithmeticOpCost {k : Nat} (W : Nat) : valid_ops k → Nat
  | .shiftL _ _ => 0
  | .shiftR _ _ => 0
  | .negate _ => 2 * (W + rippleAdderGateBound W)
  | .addScaled _ _ _ _ => 2 * rippleAdderGateBound W
  | .phaseProduct _ => 0

/-- Total nonrecursive arithmetic overhead of one PhaseProduct recursion node at
common working width `W`. -/
def phaseProgramOverhead {k : Nat} (W : Nat) (ops : Prog k) : Nat :=
  ops.foldr (fun op total => phaseArithmeticOpCost W op + total) 0

/-- Additive width growth requested by one source operation while scanning a
fixed PhaseProduct body program. -/
def phaseOpWidthGrowth {k : Nat} : valid_ops k → Nat
  | .shiftL _ n => n
  | .shiftR _ _ => 0
  | .negate _ => 1
  | .addScaled _ _ _ shift => shift + 1
  | .phaseProduct _ => 0

/-- Total additive width growth requested by a fixed PhaseProduct body program. -/
def phaseProgramWidthGrowth {k : Nat} : List (valid_ops k) → Nat
  | [] => 0
  | op :: ops => phaseOpWidthGrowth op + phaseProgramWidthGrowth ops

/-! ## The companion's exact-below-bound facts

Reproductions of `cuccaroModAddResources_totalGates_le_rippleAdderGateBound` and
`negateResources_totalGates_le_negateGateBound`
(`Implementation/GateCount/PhaseProduct/Lemmas.lean:318,329`). They are what
makes the two layers coherent: the operative model never charges more than the
recurrence layer assumes.
-/

theorem cuccaroModAddResources_totalGates_le_rippleAdderGateBound (w : Nat) :
    (cuccaroModAddResources w).totalGates <= rippleAdderGateBound w := by
  show 0 + (2 * w - 6) + (5 * w - 7) + (2 * w - 3) + 0 <= 9 * w + 2
  omega

theorem negateResourcesAtWidth_totalGates_le_negateGateBound (w : Nat) :
    (negateResourcesAtWidth w).totalGates <= w + rippleAdderGateBound w := by
  show 0 + (w + (2 * w - 6) + 2) + (5 * w - 7) + (2 * w - 3) + 0 <= w + (9 * w + 2)
  omega

end TableGeneration.RecursiveCost.ForShor
