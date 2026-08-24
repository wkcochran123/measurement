/-
# ForceCountSideTheorem — SIDE THEOREM (operator-directed, 2026-08-12)

Operator: "As the device demonstrates, force is the number of t=f virtual props exist."
Then: "11". Then: "Write the code as a side theorem and prove."

This file is the code, as a side theorem, proved. It is a LEAF: it reads Episode 6
(the GOSUB / virtual loop), Episode 32 (the natural-unit radius the force seam
recovers), and SelfEnergyGibbs (the device's own 11) — and touches none of them.
It is NOT part of the curated root. `selection_sound`, `affineInvAlpha`, and the
jar are untouched.

WHAT IS PROVED (the earned half, per all three chairs):
1. The count of virtual-loop (GOSUB) returns is well-defined and TRUTH-BLIND:
   the count of a chain does not depend on the truth of the decided props (Facts)
   it carries — the loop returns whether the prop is true or false. That is the
   machine-checked content of "t=f virtual props": each `.basis` layer carries a
   DECIDED prop (a `Fact`, truth + its Decidable — BM's reading), and the return
   consumes the layer without consulting the truth (Kodo's "truth-blind GOSUB").
2. The device's own 11 is pinned WITH ITS PROVENANCE: `depthN = maxCertifiedTurn
   + countToThree + 1 + settleMargin = 6 + 3 + 1 + 1 = 11` — a ladder length:
   10 forced/motivated (6 turn-target + 3 fencepost floor + 1 FORCED fencepost)
   plus 1 NAMED margin — SelfEnergyGibbs:83–87 labels `settleMargin` as
   DISCRETIONARY, "a chosen +1, named as a margin, not dressed as a necessity,"
   and this header keeps that label. (The numeral also happens to equal
   2*5+1; that is a coincidence of VALUE, not of construction — the construction
   is 6+3+1+1, and this file enshrines only the construction.)
3. A chain of exactly the diagnostic depth makes exactly 11 truth-blind returns:
   the device-computed 11 IS realizable as a count of t=f virtual-prop returns.
4. THE FORCE TEST, decided in public: the count does NOT equal the force grade.
   The force seam's recovered reading has numerator `naturalUnitOrbitRadius`
   (= 18, the Nat that makes `forceRecoveredExactG = deviceG` exact in Ep36),
   and 11 ≠ 18. So "force is the number of t=f virtual props" FAILS as an
   identity on this build: the count is real (11, theorem 3), the force grade is
   real (18, Ep36), and they are provably different numbers. The count decided.

FENCE (printed, per the wall all three chairs held): the comment at Episode6:428
naming the GOSUB "Feynman Propagator" is a LANDMARK, not a theorem. Nothing in
this file asserts a bridge from the count to QFT, to force-in-general, or to 11
dimensions. Scope is the electron model; the no-name-bridge stands.
-/
import Measurement.Episode6
import Measurement.Episode32
import Measurement.SupportingMeasurements.SelfEnergyGibbs

namespace Measurement.ForceCountSide

open Measurement

/-- `gosubReturnCount` — the number of virtual-loop (GOSUB) returns a `Basis`
chain makes: exactly one per `.basis` layer, because `jmp?` on a `.basis`
returns the tail (Episode6:428, the wildcard on `f.truth` — truth-blind).
`null_space` is the segfault (no return); a bare `origin` as written carries no
`.basis` layer yet. The count is STRUCTURAL: it counts the decided-prop-bearing
layers present in the chain. -/
def gosubReturnCount : Basis → Nat
  | .null_space _ => 0
  | .origin _ _ => 0
  | .basis _ _ _ tail => 1 + gosubReturnCount tail

/-- Theorem 1 (truth-blindness): the return count of a chain does not depend on
WHICH decided prop the layer carries — swap any `Fact` for any other and the
count is unchanged, definitionally. This is "the loop returns whether t or f". -/
theorem gosub_return_is_truth_blind
    (f f' : Fact) (p q : Product) (t : Basis) :
    gosubReturnCount (.basis f p q t) = gosubReturnCount (.basis f' p q t) := rfl

/-- `chainOfDepth n` — the canonical chain with exactly `n` virtual layers over
a terminated vacuum: every layer carries the decided prop `Fact.Truth` and the
zero product, nothing else. -/
def chainOfDepth : Nat → Basis
  | 0 => .null_space Fact.Truth
  | n + 1 =>
      .basis Fact.Truth (Product.origin Fact.Truth) (Product.origin Fact.Truth)
        (chainOfDepth n)

/-- The count of the canonical chain is its depth, for every depth. -/
theorem gosubReturnCount_chainOfDepth (n : Nat) :
    gosubReturnCount (chainOfDepth n) = n := by
  induction n with
  | zero => rfl
  | succ k ih => simp [chainOfDepth, gosubReturnCount, ih, Nat.add_comm]

/-- Theorem 2a (the device's 11, value): the diagnostic ladder length is 11. -/
theorem depthN_eq_eleven : SelfEnergyGibbs.depthN = 11 := by decide

/-- Theorem 2b (the device's 11, PROVENANCE): the 11 is constructed as
`maxCertifiedTurn + countToThree + 1 + settleMargin` — a ladder, 6+3+1+1:
ten forced/motivated plus one DISCRETIONARY named margin (`settleMargin`,
per its own label at SelfEnergyGibbs:83–87). This is definitional (`rfl`):
the construction is in the definition itself. -/
theorem depthN_provenance :
    SelfEnergyGibbs.depthN =
      SelfEnergyGibbs.maxCertifiedTurn
        + Measurement.AlphaBoundCountToThree.countToThree
        + 1 + SelfEnergyGibbs.settleMargin := rfl

/-- Theorem 3 (the count realizes the 11): a chain of exactly the diagnostic
depth makes exactly 11 truth-blind virtual-prop returns. The device's own 11 is
reachable as a count of t=f GOSUB returns. -/
theorem diagnostic_depth_chain_counts_eleven :
    gosubReturnCount (chainOfDepth SelfEnergyGibbs.depthN) = 11 := by
  rw [gosubReturnCount_chainOfDepth]; exact depthN_eq_eleven

/-- The force grade: the Nat numerator through which the Ep36 spring seam
recovers `deviceG` exactly (`forceRecoveredExactG` numerator). Its value. -/
theorem force_grade_is_eighteen : naturalUnitOrbitRadius = 18 := by decide

/-- Theorem 4 (THE TEST, either-way, answered): the count of t=f virtual-prop
returns at the device's own depth does NOT equal the force grade. 11 ≠ 18.
"Force is the number of t=f virtual props" fails as an identity on this build —
the count is real, the force grade is real, and the machine says they differ. -/
theorem gosub_count_ne_force_grade :
    gosubReturnCount (chainOfDepth SelfEnergyGibbs.depthN)
      ≠ naturalUnitOrbitRadius := by
  rw [diagnostic_depth_chain_counts_eleven, force_grade_is_eighteen]
  decide

end Measurement.ForceCountSide
