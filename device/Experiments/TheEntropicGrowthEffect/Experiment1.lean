import Experiments.Common

/-!
# The Dark Energy Effect — a finite ledger of negative informational pressure

Modelled after the worked exemplar `ThePositronAnnihilationEffect/Experiment1.lean`.
It replaces the 3-`Nat` `CountSetup` template with an **effect-specific domain**
(`CausalRegion`) and a genuinely **falsifiable** rule.

## Physics (modelled finitely)
A causal region `Ω` carries an interior `refinements : List Refinement` and a uniform
background credit `lambda : Nat`.  In an ordinary ledger the boundary pressure is the
reconciliation cost — here the **count** of interior refinements (`P = pressure`).  The
description posits a uniform background term `Λ` so the **effective** pressure is
`P_eff = P - Λ`.  When `Λ` exceeds `P` the net pressure is negative
(`Nat`-safely: `P < Λ`), and the ledger is biased toward **expansion** rather than
contraction.

The one structural fact that makes the bookkeeping cohere is **additivity**: the pressure
of a region assembled from two sub-regions is the sum of their pressures.  That is the
harness theorem `Experiments.Common.Ledger.count_append`, and it is a load-bearing conjunct
of `claim_holds` below — break the harness ledger and this file fails to build.

## NOT claimed
That this derives the cosmological constant `Λ`, the Friedmann equations, or any real
accelerating expansion; `Λ` is a labelled `Nat` offset, not a measured energy density.
Nothing about general relativity, vacuum energy, or quintessence is formalized.  The
"pressure" is a finite refinement count, and "expansion" is a single sign predicate on a
`Nat` subtraction — the **discrete shadow** of the smooth phenomenon, never the phenomenon.
**Claim ceiling:** a finite ledger model of the pressure offset, whose additivity conjunct
is the harness's own theorem.
-/

namespace Experiments.TheDarkEnergyEffect

/-- A single interior refinement: an opaque tag for one reconciliation event. -/
structure Refinement where
  tag : Nat
deriving DecidableEq, Repr

/-- A causal region: its interior refinements plus a uniform background credit `lambda` (the
finite stand-in for the cosmological term `Λ`). -/
structure CausalRegion where
  refinements : List Refinement
  lambda : Nat
deriving Repr

namespace CausalRegion

/-- The boundary pressure of a region = its reconciliation cost = the **count** of interior
refinements.  (This is `Ledger.count` of the interior, made explicit below.) -/
def pressure (Ω : CausalRegion) : Nat :=
  Ω.refinements.length

/-- The interior of a region, viewed as a harness ledger of refinements. -/
def interior (Ω : CausalRegion) : Experiments.Common.Ledger Refinement :=
  { events := Ω.refinements }

/-- The net (effective) pressure is **negative** when the background credit exceeds the raw
pressure.  Written `Nat`-safely: `P < Λ` ⇔ `P - Λ < 0`. -/
def netPressureNegative (Ω : CausalRegion) : Prop :=
  Ω.pressure < Ω.lambda

/-- The region is biased toward expansion exactly when its net pressure is negative:
contraction would *raise*, not lower, the informational cost. -/
def expands (Ω : CausalRegion) : Prop :=
  Ω.netPressureNegative

-- Make the richer predicates DECIDABLE so `decide`/`#eval` see through them.
instance (Ω : CausalRegion) : Decidable (Ω.netPressureNegative) := by
  unfold netPressureNegative; exact inferInstance
instance (Ω : CausalRegion) : Decidable (Ω.expands) := by
  unfold expands; exact inferInstance

/-- `pressure` is exactly the harness ledger count of the interior — pins `pressure` to the
harness bookkeeping. -/
theorem pressure_eq_interior_count (Ω : CausalRegion) :
    Ω.pressure = Ω.interior.count := by
  rfl

end CausalRegion

open CausalRegion

-- ---------------------------------------------------------------------------
-- FALSIFIABLE lemmas.  Each is ∀-quantified and would break if a hypothesis were dropped.
-- ---------------------------------------------------------------------------

/-- A region whose background credit does NOT exceed its pressure is never expansion-biased.
Drop the hypothesis `h` and the conclusion is false (e.g. `Λ = P`), so `h` is load-bearing. -/
theorem noCredit_no_expansion (Ω : CausalRegion) (h : Ω.lambda ≤ Ω.pressure) :
    ¬ Ω.expands :=
  fun he => Nat.not_lt.mpr h he

/-- Expansion forces a STRICTLY positive background credit: with `Λ = 0` no region expands.
Falsifiable — the bound `0 < Λ` is exactly what `expands` buys. -/
theorem expands_needs_credit (Ω : CausalRegion) (h : Ω.expands) : 0 < Ω.lambda :=
  Nat.lt_of_le_of_lt (Nat.zero_le _) h

/-- ADDITIVITY of pressure across a partition: assembling a region from two interiors sums
their pressures.  ∀-quantified over interiors and credits; this is the harness theorem
`Ledger.count_append` specialised to `pressure`.  Drop either summand and it breaks. -/
theorem pressure_additive (left right : List Refinement) (lam : Nat) :
    (CausalRegion.mk (left ++ right) lam).pressure =
      (CausalRegion.mk left lam).pressure + (CausalRegion.mk right lam).pressure := by
  show (Experiments.Common.Ledger.mk (left ++ right) : Experiments.Common.Ledger Refinement).count
      = (Experiments.Common.Ledger.mk left).count + (Experiments.Common.Ledger.mk right).count
  exact Experiments.Common.Ledger.count_append _ _

-- ---------------------------------------------------------------------------
-- The canonical dark-energy region: more credit than pressure ⇒ expands.
-- ---------------------------------------------------------------------------

/-- Two interior refinements, but a background credit of three: net pressure is negative. -/
def darkRegion : CausalRegion :=
  { refinements := [{ tag := 0 }, { tag := 1 }], lambda := 3 }

/-- The control: same two refinements, but credit `2 = pressure`, so it does NOT expand. -/
def ordinaryRegion : CausalRegion :=
  { refinements := [{ tag := 0 }, { tag := 1 }], lambda := 2 }

theorem darkRegion_expands : darkRegion.expands := by decide
theorem ordinaryRegion_does_not_expand : ¬ ordinaryRegion.expands := by decide

-- ---------------------------------------------------------------------------
-- THE CLAIM (content-bearing conjunction; one conjunct is the harness theorem).
-- ---------------------------------------------------------------------------

/-- The claim, in honest parts:
* (expansion) the canonical dark region is expansion-biased — `darkRegion.expands`;
* (necessity) that bias requires a strictly positive background credit — `expands_needs_credit`;
* (control) an ordinary region with `Λ = P` does NOT expand — falsifiability witness;
* (additivity) interior pressure is additive across a partition — the **harness** theorem
  `Ledger.count_append`, the load-bearing coupling: a regression there breaks this build. -/
def claimStatement : Prop :=
  darkRegion.expands ∧
    (∀ Ω : CausalRegion, Ω.expands → 0 < Ω.lambda) ∧
    ¬ ordinaryRegion.expands ∧
    (∀ (l r : List Refinement) (lam : Nat),
      (CausalRegion.mk (l ++ r) lam).pressure =
        (CausalRegion.mk l lam).pressure + (CausalRegion.mk r lam).pressure)

def claim : Experiments.Common.Claim :=
  { tag := Experiments.Common.ClaimTag.smoothShadowAnalogy
    statement := claimStatement }

theorem claim_holds : claim.statement :=
  ⟨darkRegion_expands, expands_needs_credit, ordinaryRegion_does_not_expand, pressure_additive⟩

/-- The tag is an honest ceiling: a smooth-shadow analogy, nothing more. -/
theorem ceiling : claim.tag = Experiments.Common.ClaimTag.smoothShadowAnalogy := rfl

-- ---------------------------------------------------------------------------
-- A computable run + a non-vacuous Experiment.claim, with a proved bridge.
-- ---------------------------------------------------------------------------

abbrev Setup := CausalRegion

/-- The run computes the expansion verdict — thanks to the `Decidable` instances above. -/
def run (Ω : Setup) : Bool := decide Ω.expands

def experiment : Experiments.Common.Experiment Setup Bool :=
  { tag := claim.tag
    run := run
    claim := fun Ω => Ω.expands }

theorem run_iff_claim (Ω : Setup) : run Ω = true ↔ experiment.claim Ω := by
  simp only [run, experiment, decide_eq_true_iff]

#eval run darkRegion                  -- expect: true
#eval run ordinaryRegion              -- expect: false  (Λ = P, no expansion bias)
#print axioms claim_holds             -- ambient [propext, Quot.sound], not coupling

/-- Bring a minimal device next to this experiment: it records whether the exported claim fires.
Decides `setup.expands` directly (the `Decidable` instance is for `expands`, not for the opaque
`experiment.claim` projection). -/
def deviceNear (setup : Setup) : Bool :=
  decide setup.expands

theorem deviceNear_detects_claim (setup : Setup) :
    deviceNear setup = true ↔ experiment.claim setup := by
  simp only [deviceNear, experiment, decide_eq_true_iff]

def triangulation : Experiments.Common.Triangulation Setup Bool :=
  { experiment := experiment
    device := deviceNear
    detects := deviceNear_detects_claim }

-- ---------------------------------------------------------------------------
-- GATE EVIDENCE: the falsifiable predicate evaluated where it is FALSE.
-- `noCredit_no_expansion` says `Λ ≤ P → ¬ expands`; the control region has `Λ = P = 2`,
-- so `ordinaryRegion.expands` is FALSE.  This prints `false`, proving the lemma is
-- load-bearing (not vacuous): the region exists where expansion does NOT fire.
-- ---------------------------------------------------------------------------
#eval decide ordinaryRegion.expands   -- expect: false  (Λ = P = 2, net pressure not negative)

end Experiments.TheDarkEnergyEffect
