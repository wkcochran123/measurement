import Experiments.Common

/-!
# The Heisenberg Effect — finite refinement-floor model (content-bearing, falsifiable)

This file follows the EXEMPLAR shape (`ThePositronAnnihilationEffect/Experiment1.lean`):

1. an **effect-specific domain** (`Regime`, `Step`) — NOT the generic 3-`Nat` `CountSetup`;
2. genuinely **falsifiable** quantified lemmas (`∀`, would break if a hypothesis were dropped) —
   one per conjunct of the admissibility rule, so none can silently rot;
3. a **content-bearing** claim — a real conjunction, never `True`;
4. an **honest tag** + a candid "NOT claimed" disclaimer;
5. explicit `Decidable` instances so `decide`/`#eval` see through the richer predicates;
6. a **structural device/harness coupling**: one conjunct of `claim_holds` is discharged by the
   harness continuity law `Experiments.Common.Ledger.count_append` — finite contributions sum
   additively. A rename/`sorry`/regression of `count_append` in `Common/Basic.lean` breaks THIS
   build. This is symbol coupling (the law's name sits in the proof term), not a measured value.

## Physics (modelled finitely)
The Heisenberg effect here is a **refinement-floor discipline**. A measurement regime has a
*floor* `floor` (the minimum admissible refinement). Each refinement `Step` is admissible iff its
chosen refinement level `level` is **at or above** the floor AND its finite residual `residual` is
**bounded by the budget** `budget`. Refining *below* the floor is inadmissible: the residual is no
longer absorbable and contributions sum without stabilization. The accumulation of residuals across
a sequence of steps is the harness `Ledger`; its total is additive (`count_append`) — finite
contributions sum, and the floor is exactly what keeps that sum finite/bounded.

## NOT claimed
That this is the quantum uncertainty principle; that any non-commutation relation, operator
spectrum, or ℏ is derived (no real number, no operator, no commutator appears). The "floor" is a
labelled finite constant, not a derived Planck-scale bound. No convergence/divergence analysis of
an actual infinite series is performed — only the *additivity* of finitely many residuals.
**Claim ceiling:** a finite ledger model of the admissibility logic, one of whose conjuncts is the
harness's own additivity theorem.
-/

namespace Experiments.TheHeisenbergEffect

/-- A refinement regime: the minimum admissible refinement (`floor`) and the finite residual
budget (`budget`) the ledger may absorb at each step. -/
structure Regime where
  floor : Nat
  budget : Nat
deriving DecidableEq, Repr

/-- A single refinement step: the refinement `level` actually chosen, and the finite `residual`
that level leaves behind. -/
structure Step where
  level : Nat
  residual : Nat
deriving DecidableEq, Repr

/-- The standard regime: a floor of 2 admissible refinement units, residual budget 3. -/
def defaultRegime : Regime := { floor := 2, budget := 3 }

namespace Regime

/-- `s` refines at or above the floor: `floor ≤ level`. (The Heisenberg lower bound.) -/
def atOrAboveFloor (r : Regime) (s : Step) : Prop :=
  r.floor ≤ s.level

/-- `s` leaves a residual the budget can absorb: `residual ≤ budget`. -/
def residualAbsorbable (r : Regime) (s : Step) : Prop :=
  s.residual ≤ r.budget

/-- THE ADMISSIBILITY RULE: a step is admissible iff it refines at/above the floor AND its
residual is absorbable. **Both conjuncts required** — each pinned by a falsifiable lemma below,
so dropping either fails the build. -/
def admissible (r : Regime) (s : Step) : Prop :=
  r.atOrAboveFloor s ∧ r.residualAbsorbable s

-- Make the richer predicates DECIDABLE so `decide`/`#eval` work.
instance (r : Regime) (s : Step) : Decidable (r.atOrAboveFloor s) := by
  unfold atOrAboveFloor; exact inferInstance
instance (r : Regime) (s : Step) : Decidable (r.residualAbsorbable s) := by
  unfold residualAbsorbable; exact inferInstance
instance (r : Regime) (s : Step) : Decidable (r.admissible s) := by
  unfold admissible; exact inferInstance

end Regime

-- ---------------------------------------------------------------------------
-- FALSIFIABLE lemmas: ONE PER CONJUNCT, so the whole admissibility rule is load-bearing.
-- Each would break if `admissible` dropped that conjunct.
-- ---------------------------------------------------------------------------

/-- The Heisenberg lower bound is necessary: refining BELOW the floor is never admissible.
Quantified over ALL regimes and steps. (Would be false if `admissible` dropped `atOrAboveFloor`.) -/
theorem belowFloor_not_admissible
    (r : Regime) (s : Step) (h : ¬ r.atOrAboveFloor s) : ¬ r.admissible s :=
  fun ha => h ha.1

/-- Budget control is necessary: an unabsorbable residual is never admissible.
(Would be false if `admissible` dropped `residualAbsorbable`.) -/
theorem unabsorbable_not_admissible
    (r : Regime) (s : Step) (h : ¬ r.residualAbsorbable s) : ¬ r.admissible s :=
  fun ha => h ha.2

/-- Contrapositive sharpened: dropping below the floor by even one unit (level < floor) is
inadmissible, for every regime. A second falsifiable witness that the bound is load-bearing. -/
theorem strictlyBelowFloor_not_admissible
    (r : Regime) (s : Step) (h : s.level < r.floor) : ¬ r.admissible s :=
  fun ha => Nat.not_lt.mpr ha.1 h

-- ---------------------------------------------------------------------------
-- The canonical admissible step + the residual ledger (harness `Ledger`).
-- ---------------------------------------------------------------------------

/-- A canonical admissible step: refines exactly at the floor, residual within budget. -/
def floorStep : Step := { level := 2, residual := 1 }

/-- A canonical INADMISSIBLE step: refines below the floor (the residue cannot stabilize). -/
def belowStep : Step := { level := 1, residual := 5 }

/-- The standard regime admits the floor step (concrete, via the `Decidable` instance). -/
theorem admits_floorStep : defaultRegime.admissible floorStep := by decide

/-- The standard regime does NOT admit the below-floor step. -/
theorem rejects_belowStep : ¬ defaultRegime.admissible belowStep := by decide

/-- A finite residual ledger: the residuals accumulated over a run of steps. -/
def residualLedger (steps : List Step) : Experiments.Common.Ledger Step :=
  { events := steps }

/-- Two segments of a run: their residual ledgers, to be appended. -/
def segmentA : Experiments.Common.Ledger Step := { events := [floorStep, floorStep] }
def segmentB : Experiments.Common.Ledger Step := { events := [floorStep] }

-- ---------------------------------------------------------------------------
-- THE CLAIM (content-bearing; one conjunct is the harness's own additivity theorem).
-- ---------------------------------------------------------------------------

/-- The claim, in honest parts:
* (admissibility) the regime admits the canonical floor step — proved here;
* (the bound bites) it rejects the below-floor step — proved here;
* (finite contributions sum) the residual count of two appended segments is the SUM of their
  counts — `Experiments.Common.Ledger.count_append`, the harness continuity law. This is the
  structural device coupling: contributions accumulate additively, which is exactly why the floor
  is required to keep the total finite. -/
def claimStatement : Prop :=
  defaultRegime.admissible floorStep ∧
    (¬ defaultRegime.admissible belowStep) ∧
    (Experiments.Common.Ledger.append segmentA segmentB).count
      = segmentA.count + segmentB.count

def claim : Experiments.Common.Claim :=
  { tag := Experiments.Common.ClaimTag.finiteLedgerModel
    statement := claimStatement }

theorem claim_holds : claim.statement :=
  ⟨admits_floorStep, rejects_belowStep,
    Experiments.Common.Ledger.count_append segmentA segmentB⟩

/-- The tag is an honest ceiling: a finite ledger model, nothing more. -/
theorem ceiling : claim.tag = Experiments.Common.ClaimTag.finiteLedgerModel := rfl

-- ---------------------------------------------------------------------------
-- A computable run + a NON-vacuous Experiment.claim, with a proved bridge.
-- ---------------------------------------------------------------------------

structure Setup where
  regime : Regime
  step : Step

/-- The run actually computes — thanks to the `Decidable` instances above. -/
def run (s : Setup) : Bool := decide (s.regime.admissible s.step)

/-- The exported claim is a genuine function of the setup; this bridge pins it to `run`. -/
def experiment : Experiments.Common.Experiment Setup Bool :=
  { tag := claim.tag
    run := run
    claim := fun s => s.regime.admissible s.step }

theorem run_iff_claim (s : Setup) :
    run s = true ↔ experiment.claim s := by
  simp only [run, experiment, decide_eq_true_iff]

def canonicalSetup : Setup := { regime := defaultRegime, step := floorStep }

#eval run canonicalSetup                                  -- expect: true
#eval run { canonicalSetup with step := belowStep }       -- expect: false (below floor)
#print axioms claim_holds                                 -- ambient footprint, not coupling

/-- Bring a minimal device next to this experiment: it records whether the exported claim fires. -/
def deviceNear (setup : Setup) : Bool :=
  decide (experiment.claim setup)

theorem deviceNear_detects_claim (setup : Setup) :
    deviceNear setup = true ↔ experiment.claim setup := by
  simp [deviceNear]

def triangulation : Experiments.Common.Triangulation Setup Bool :=
  { experiment := experiment
    device := deviceNear
    detects := deviceNear_detects_claim }

end Experiments.TheHeisenbergEffect
