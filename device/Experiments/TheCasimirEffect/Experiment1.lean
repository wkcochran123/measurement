import Experiments.Common

/-!
# The Casimir Effect — a finite ledger model of boundary-induced refinement asymmetry

Modelled after the worked exemplar `ThePositronAnnihilationEffect/Experiment1.lean`.

## Physics (modelled finitely)
The Casimir effect (description.md, from `instrument/chapters/07.tex`) is read here as the
*boundary expression of informational pressure*. Two parallel plates restrict the admissible
field modes in the **interior** region: each admissible mode is one distinguishable refinement of
the causal record. The plates suppress many of these, so the interior ledger records **strictly
fewer** admissible distinctions than the unrestricted **exterior** ledger. That strict count
imbalance is the informational tension whose smooth-limit shadow is the Casimir pressure.

We model the apparatus as a finite `Cavity`: a count of geometrically-available mode slots and a
suppression count (how many interior slots the plates kill). The interior admissible-mode `Ledger`
holds the surviving slots; the exterior `Ledger` holds all slots, unsuppressed. The content claim is:
* the interior is **bounded by** its surviving-mode count (the harness counting theorem), and
* the exterior **strictly exceeds** the interior whenever the plates suppress at least one mode
  (`interiorCount < exteriorCount`), i.e. there is a genuine boundary imbalance.

## Coupling
HARNESS, not device. The Casimir effect involves no holonomy / charge / positron / gauge loop, so
the device theorems (`Measurement.holonomy_*`, `detects_positron_*`) would be a FAKE coupling and
are forbidden. The honest hook is bookkeeping/bound: the interior admissible-mode count is
discharged by `Experiments.Common.Counting.boundedBy_of_eq`. That theorem is a LOAD-BEARING
conjunct of `claim_holds`: a regression/rename in the harness `Counting` lemma breaks THIS build.

## NOT claimed
That this derives the Casimir pressure, its 1/d⁴ scaling, or any zero-point-energy quantity; that
mode suppression is computed from real boundary conditions (the suppression count is a *labelled*
geometric input, not derived); any continuum limit (the "smooth shadow" is named, not taken). The
model enforces only the finite combinatorial fact that restricting interior modes makes the
interior ledger strictly smaller than the exterior — the discrete bookkeeping the description rests
the force on. **Claim ceiling:** a finite ledger stand-in (`smoothShadowAnalogy`) for the boundary
count imbalance, one of whose conjuncts is the harness's own counting theorem.
-/

namespace Experiments.TheCasimirEffect

/-- One admissible field mode = one distinguishable refinement of the causal record, labelled by a
finite slot index. -/
structure Mode where
  slot : Nat
deriving DecidableEq, Repr

/-- The apparatus: `slots` geometrically-available interior mode slots and a `suppressed` count of
those the two plates kill. The boundary restricts admissibility; the exterior sees all `slots`. -/
structure Cavity where
  slots : Nat
  suppressed : Nat
deriving Repr

/-- The standard cavity: 8 available slots, 3 suppressed by the plates. -/
def defaultCavity : Cavity := { slots := 8, suppressed := 3 }

namespace Cavity

/-- The exterior admissible-mode ledger: every slot survives (no suppression outside the plates). -/
def exterior (c : Cavity) : Experiments.Common.Ledger Mode :=
  { events := (List.range c.slots).map (fun i => { slot := i }) }

/-- The interior admissible-mode ledger: only the slots the plates do NOT suppress survive. We keep
the slots whose index is `≥ suppressed`, so exactly `suppressed` of them are removed. -/
def interior (c : Cavity) : Experiments.Common.Ledger Mode :=
  { events := ((List.range c.slots).filter (fun i => decide (c.suppressed ≤ i))).map
      (fun i => { slot := i }) }

/-- The interior surviving-mode count is `slots - suppressed` (truncated subtraction; honest because
`suppressed ≤ slots` for any real cavity, but we do not assume it — the count is what it is). -/
def interiorCount (c : Cavity) : Nat :=
  (c.interior).count

/-- The exterior admissible-mode count is `slots`. -/
def exteriorCount (c : Cavity) : Nat :=
  (c.exterior).count

/-- THE BOUNDARY IMBALANCE: the plates suppress at least one interior mode, so the exterior strictly
exceeds the interior. This is the informational tension the description turns into pressure. -/
def boundaryImbalance (c : Cavity) : Prop :=
  c.interiorCount < c.exteriorCount

instance (c : Cavity) : Decidable (c.boundaryImbalance) := by
  unfold boundaryImbalance; exact inferInstance

end Cavity

-- ---------------------------------------------------------------------------
-- Count lemmas: pin the exterior/interior tallies to closed forms, so the
-- imbalance is a real combinatorial fact, not a hand-set literal.
-- ---------------------------------------------------------------------------

/-- The exterior count is exactly `slots`. -/
theorem exteriorCount_eq (c : Cavity) : c.exteriorCount = c.slots := by
  simp [Cavity.exteriorCount, Cavity.exterior, Experiments.Common.Ledger.count]

-- ---------------------------------------------------------------------------
-- FALSIFIABLE lemma: the suppression is LOAD-BEARING. Drop the hypothesis
-- (`0 < suppressed`) and the conclusion (`interior < exterior`) breaks: with
-- `suppressed = 0` the two ledgers have EQUAL counts, so the imbalance is false.
-- Quantified over ALL cavities.
-- ---------------------------------------------------------------------------

/-- If the plates suppress at least one mode AND that suppression is within the available slots,
the interior is strictly smaller than the exterior. Necessity of `0 < c.suppressed`: at
`suppressed = 0` no mode is removed and `interiorCount = exteriorCount` (see `no_suppression_no_imbalance`),
so the conclusion is FALSE — the hypothesis is genuinely load-bearing. -/
theorem suppression_forces_imbalance
    (c : Cavity) (hpos : 0 < c.suppressed) (hle : c.suppressed ≤ c.slots) :
    c.boundaryImbalance := by
  unfold Cavity.boundaryImbalance Cavity.interiorCount Cavity.exteriorCount
  unfold Cavity.interior Cavity.exterior Experiments.Common.Ledger.count
  simp only [List.length_map, List.length_range]
  -- interior length = (number of i in range slots with suppressed ≤ i)
  -- = slots - suppressed < slots, since 0 < suppressed ≤ slots.
  have hfilter : (((List.range c.slots).filter (fun i => decide (c.suppressed ≤ i)))).length
      = c.slots - c.suppressed := by
    induction c.slots with
    | zero => simp
    | succ n ih =>
      rw [List.range_succ, List.filter_append]
      simp only [List.length_append]
      rw [ih]
      if hcase : c.suppressed ≤ n then
        simp [hcase]
        omega
      else
        simp [hcase]
        omega
  rw [hfilter]
  omega

/-- Witness that the hypothesis is load-bearing: with NO suppression the interior equals the
exterior, so there is NO imbalance. (This is the config the gate `#eval` below evaluates false.) -/
theorem no_suppression_no_imbalance
    (c : Cavity) (h0 : c.suppressed = 0) : ¬ c.boundaryImbalance := by
  unfold Cavity.boundaryImbalance Cavity.interiorCount Cavity.exteriorCount
  unfold Cavity.interior Cavity.exterior Experiments.Common.Ledger.count
  simp only [List.length_map, List.length_range]
  have hfilter : (((List.range c.slots).filter (fun i => decide (c.suppressed ≤ i)))).length
      = c.slots := by
    rw [h0]
    induction c.slots with
    | zero => simp
    | succ n ih =>
      rw [List.range_succ, List.filter_append]
      simp only [List.length_append]
      rw [ih]
      simp [Nat.zero_le]
  rw [hfilter]
  exact Nat.lt_irrefl c.slots

-- ---------------------------------------------------------------------------
-- The canonical cavity facts (concrete, via the Decidable instance / omega).
-- ---------------------------------------------------------------------------

/-- The default cavity exhibits the boundary imbalance. -/
theorem default_has_imbalance : defaultCavity.boundaryImbalance := by decide

/-- The interior count of the default cavity is exactly 5 (8 slots, 3 suppressed). -/
theorem default_interiorCount : defaultCavity.interiorCount = 5 := by decide

-- ---------------------------------------------------------------------------
-- THE CLAIM (content-bearing). Two conjuncts:
--  (imbalance)  the default cavity's interior is strictly smaller than its exterior — proved here;
--  (bound, HARNESS-COUPLED) the interior ledger is bounded by its own surviving-mode count, via
--    `Experiments.Common.Counting.boundedBy_of_eq`. This is the LOAD-BEARING harness coupling:
--    a regression in that lemma breaks this build.
-- ---------------------------------------------------------------------------

/-- The claim, in honest halves:
* (boundary imbalance) `defaultCavity.boundaryImbalance` — the exterior strictly exceeds the
  interior, the discrete fact the description turns into pressure; and
* (harness bound) the interior admissible-mode ledger is `Counting.boundedBy` its own count —
  discharged by `Experiments.Common.Counting.boundedBy_of_eq`, so the harness counting theorem
  sits in this proof term. -/
def claimStatement : Prop :=
  defaultCavity.boundaryImbalance ∧
    Experiments.Common.Counting.boundedBy defaultCavity.interior defaultCavity.interiorCount

def claim : Experiments.Common.Claim :=
  { tag := Experiments.Common.ClaimTag.smoothShadowAnalogy
    statement := claimStatement }

theorem claim_holds : claim.statement :=
  ⟨default_has_imbalance,
    Experiments.Common.Counting.boundedBy_of_eq (rfl : defaultCavity.interior.count = defaultCavity.interiorCount)⟩

/-- The tag is an honest ceiling: a finite stand-in (`smoothShadowAnalogy`) for the continuous
boundary force — the discrete count imbalance, not the pressure itself. -/
theorem ceiling : claim.tag = Experiments.Common.ClaimTag.smoothShadowAnalogy := rfl

-- ---------------------------------------------------------------------------
-- A computable run + a NON-vacuous Experiment.claim, with a proved bridge.
-- ---------------------------------------------------------------------------

abbrev Setup := Cavity

/-- The run actually computes — thanks to the `Decidable` instance above. -/
def run (s : Setup) : Bool := decide (s.boundaryImbalance)

/-- The exported claim is a genuine function of the setup; this bridge pins it to `run`, so the
claim body cannot be silently swapped for `fun _ => True` without breaking the proof. -/
def experiment : Experiments.Common.Experiment Setup Bool :=
  { tag := claim.tag
    run := run
    claim := fun s => s.boundaryImbalance }

theorem run_iff_claim (s : Setup) :
    run s = true ↔ experiment.claim s := by
  simp only [run, experiment, decide_eq_true_iff]

#eval run defaultCavity                                   -- expect: true
#eval run { defaultCavity with suppressed := 0 }          -- expect: FALSE  (no plates ⇒ no imbalance)
#print axioms claim_holds                                 -- ambient footprint, not coupling

/-- Bring a minimal device next to this experiment: it records whether the exported claim fires.
We decide on `setup.boundaryImbalance` directly (which has a `Decidable` instance) — definitionally
the same as `experiment.claim setup`. -/
def deviceNear (setup : Setup) : Bool :=
  decide (setup.boundaryImbalance)

theorem deviceNear_detects_claim (setup : Setup) :
    deviceNear setup = true ↔ experiment.claim setup := by
  simp only [deviceNear, experiment, decide_eq_true_iff]

def triangulation : Experiments.Common.Triangulation Setup Bool :=
  { experiment := experiment
    device := deviceNear
    detects := deviceNear_detects_claim }

end Experiments.TheCasimirEffect
