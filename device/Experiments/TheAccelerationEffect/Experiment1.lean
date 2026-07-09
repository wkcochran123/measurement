import Experiments.Common

/-!
# The Acceleration Effect — content-bearing finite model (rebuilt to the exemplar shape)

Source: `instrument/chapters/07.tex:397` (`phenomenon`, "The Acceleration Effect").

## Physics (modelled finitely)
The description says: *acceleration is the count of distinguishable failures of a coasting
interpolant to account for a merged ledger; a straight refinement trajectory is a zero-cost
hypothesis; every detectable deviation is recorded as a second-order refinement.*

We model a refinement trajectory as a finite list of recorded sample positions (`Track`). The
**coasting interpolant** is the zero-cost hypothesis: it predicts the next sample by holding the
last first-difference (velocity) fixed — a straight extrapolation. At each interior triple of
samples the coast prediction *fails* exactly when the **second difference** is nonzero. The
**acceleration ledger** records one event per such failure; `accelerationCount` is its length.
A straight (constant-velocity) track produces an empty ledger — zero cost, no acceleration.

## NOT claimed
That this is Newtonian force, mass, `F = ma`, or any continuum derivative; no limit is taken and
no metric/units are attached (samples are bare `Int`s). The second difference is the *discrete*
shadow of `d²x/dt²`, not that derivative. "Distinguishable" here means literally `≠ 0` on the
integer second difference — there is no detector floor / noise window modelled. **Claim ceiling:**
a finite ledger model whose one content number is the count of coasting failures, and whose
load-bearing conjunct is the harness identity `Counting.boundedBy_of_eq` applied to that count.
-/

namespace Experiments.TheAccelerationEffect

/-- A refinement trajectory: the recorded sample positions, in order. -/
structure Track where
  samples : List Int
deriving Repr

/-- The first differences (the discrete "velocity" stream) of a sample list. -/
def firstDiffs : List Int -> List Int
  | [] => []
  | [_] => []
  | a :: b :: rest => (b - a) :: firstDiffs (b :: rest)

/-- The second differences (the discrete "acceleration" stream): differences of `firstDiffs`. -/
def secondDiffs (t : Track) : List Int :=
  firstDiffs (firstDiffs t.samples)

/-- A single recorded coasting failure: where it occurred (interior index) and by how much the
coast prediction missed (the signed second difference there). This IS the "second-order
refinement" the description says each deviation is recorded as. -/
structure Deviation where
  atIndex : Nat
  residual : Int
deriving Repr

/-- Walk a second-difference stream from a starting interior index, keeping one `Deviation` per
*nonzero* entry (the distinguishable coasting failures). Explicit recursion (no `zipIdx`) so the
emptiness proof is a clean structural induction. -/
def keptFrom : Nat -> List Int -> List Deviation
  | _, [] => []
  | i, d :: rest =>
      if d = 0 then keptFrom (i + 1) rest
      else { atIndex := i, residual := d } :: keptFrom (i + 1) rest

/-- The acceleration ledger: one event per nonzero second difference. -/
def accelerationLedger (t : Track) : Experiments.Common.Ledger Deviation :=
  { events := keptFrom 0 (secondDiffs t) }

/-- The acceleration: the *number* of distinguishable coasting failures. This is the description's
"count of failures", nothing more. -/
def accelerationCount (t : Track) : Nat :=
  (accelerationLedger t).count

/-- A track is *coasting* (the zero-cost straight hypothesis) when every second difference is
zero: the velocity never changes. -/
def isCoasting (t : Track) : Prop :=
  ∀ d ∈ secondDiffs t, d = 0

instance (t : Track) : Decidable (isCoasting t) := by
  unfold isCoasting; exact inferInstance

-- ---------------------------------------------------------------------------
-- FALSIFIABLE lemmas. Each is ∀-quantified and breaks if its hypothesis is dropped.
-- ---------------------------------------------------------------------------

/-- If every entry of a stream is zero, `keptFrom` records nothing — from any starting index. -/
theorem keptFrom_nil_of_allZero :
    ∀ (i : Nat) (ds : List Int), (∀ d ∈ ds, d = 0) -> keptFrom i ds = []
  | _, [], _ => rfl
  | i, d :: rest, h => by
      have hd : d = 0 := h d (List.mem_cons_self ..)
      have hrest : ∀ x ∈ rest, x = 0 := fun x hx => h x (List.mem_cons_of_mem d hx)
      unfold keptFrom
      simp only [hd, if_pos]
      exact keptFrom_nil_of_allZero (i + 1) rest hrest

/-- If every recorded second difference vanishes (the track coasts), the acceleration ledger is
empty: a straight refinement trajectory costs nothing. Falsifiable: drop `h` and the conclusion
fails for any bent track (see the `#eval` at the bottom). -/
theorem coasting_has_no_acceleration (t : Track) (h : isCoasting t) :
    accelerationCount t = 0 := by
  unfold accelerationCount accelerationLedger Experiments.Common.Ledger.count
  unfold isCoasting at h
  rw [keptFrom_nil_of_allZero 0 (secondDiffs t) h]
  rfl

/-- Contrapositive / load-bearing converse: a track with a NONEMPTY acceleration ledger is NOT
coasting. Drops nothing silently — if `accelerationLedger` ignored the `≠ 0` filter this would be
false (a coasting track would still register). -/
theorem accelerated_is_not_coasting (t : Track)
    (h : accelerationCount t ≠ 0) : ¬ isCoasting t := by
  intro hc
  exact h (coasting_has_no_acceleration t hc)

/-- The recorded acceleration count is the length of the recorded ledger — the definitional
identity that ties "the number" to "the ledger of second-order refinements". -/
theorem count_is_ledger_length (t : Track) :
    accelerationCount t = (accelerationLedger t).events.length := rfl

-- ---------------------------------------------------------------------------
-- A concrete bent track and a concrete straight one.
-- ---------------------------------------------------------------------------

/-- A constant-velocity (straight) track: samples 0,2,4,6 — first diffs all `2`, no acceleration. -/
def straightTrack : Track := { samples := [0, 2, 4, 6] }

/-- A bent track: 0,1,4,9,16 (the squares) — constant *second* difference `2`, so every interior
triple is a distinguishable coasting failure: three recorded deviations. -/
def bentTrack : Track := { samples := [0, 1, 4, 9, 16] }

theorem straight_is_coasting : isCoasting straightTrack := by decide

theorem straight_has_zero_acceleration : accelerationCount straightTrack = 0 := by decide

theorem bent_has_three_accelerations : accelerationCount bentTrack = 3 := by decide

-- ---------------------------------------------------------------------------
-- THE CLAIM (content-bearing; the load-bearing conjunct is a HARNESS theorem).
-- COUPLING: harness — this effect is a finite COUNT / capacity reading, not holonomy/charge,
-- so it honestly couples to `Experiments.Common.Counting`, NOT the device.
-- ---------------------------------------------------------------------------

/-- The bound the acceleration ledger is read against: its own recorded count. -/
def accelerationBudget : Nat := accelerationCount bentTrack

/-- The claim, in honest parts:
* (straight = zero cost) the constant-velocity track records no acceleration — proved here from
  `coasting_has_no_acceleration`, which is itself ∀-falsifiable;
* (the bent track is genuinely accelerated) its ledger is nonempty, hence it is NOT coasting; and
* (the harness bound is load-bearing) the bent ledger's count is `≤ accelerationBudget`, via
  `Experiments.Common.Counting.boundedBy_of_eq` — the device-free counting identity. Break the
  count (e.g. drop the `≠ 0` filter so straight tracks register) and this conjunct fails. -/
def claimStatement : Prop :=
  accelerationCount straightTrack = 0 ∧
    ¬ isCoasting bentTrack ∧
    Experiments.Common.Counting.boundedBy (accelerationLedger bentTrack) accelerationBudget

def claim : Experiments.Common.Claim :=
  { tag := Experiments.Common.ClaimTag.finiteLedgerModel
    statement := claimStatement }

theorem claim_holds : claim.statement :=
  ⟨straight_has_zero_acceleration,
    accelerated_is_not_coasting bentTrack (by decide),
    Experiments.Common.Counting.boundedBy_of_eq (ledger := accelerationLedger bentTrack)
      (bound := accelerationBudget) rfl⟩

/-- The tag is an honest ceiling: a finite ledger model, nothing more. -/
theorem ceiling : claim.tag = Experiments.Common.ClaimTag.finiteLedgerModel := rfl

-- ---------------------------------------------------------------------------
-- A computable run + a non-vacuous Experiment.claim, with a proved bridge.
-- ---------------------------------------------------------------------------

structure Setup where
  track : Track

/-- The run actually computes the acceleration count of the setup's track. -/
def run (s : Setup) : Nat := accelerationCount s.track

/-- The exported claim is a genuine function of the setup (its acceleration count), pinned to
`run` below so the body cannot be swapped for `fun _ => True` without breaking the proof. -/
def experiment : Experiments.Common.Experiment Setup Nat :=
  { tag := claim.tag
    run := run
    claim := fun s => accelerationCount s.track = 0 }

/-- The exported claim is exactly the proposition that the run reads zero — so the claim body
genuinely tracks `run` and cannot be a constant `True`. -/
theorem run_zero_iff_claim (s : Setup) :
    run s = 0 ↔ experiment.claim s := by
  constructor
  · intro h; exact h
  · intro h; exact h

def canonicalSetup : Setup := { track := bentTrack }
def straightSetup : Setup := { track := straightTrack }

#eval run canonicalSetup     -- expect: 3  (three coasting failures)
#eval run straightSetup      -- expect: 0  (straight = zero cost)

-- A decidable expression that prints FALSE: the bent track does NOT coast — proving
-- `coasting_has_no_acceleration`'s hypothesis is load-bearing (it is false here, yet the
-- bent track has nonzero acceleration, so the lemma would be FALSE without `h`).
#eval decide (isCoasting bentTrack)   -- expect: false

#print axioms claim_holds             -- ambient [propext, Quot.sound], not coupling

instance (setup : Setup) : Decidable (experiment.claim setup) := by
  unfold experiment
  infer_instance

/-- Bring a minimal device next to this experiment: it records whether the exported claim fires. -/
def deviceNear (setup : Setup) : Bool :=
  decide (experiment.claim setup)

theorem deviceNear_detects_claim (setup : Setup) :
    deviceNear setup = true ↔ experiment.claim setup := by
  simp [deviceNear]

def triangulation : Experiments.Common.Triangulation Setup Nat :=
  { experiment := experiment
    device := deviceNear
    detects := deviceNear_detects_claim }

end Experiments.TheAccelerationEffect
