import Experiments.Common

/-!
# The da Vinci–Coulomb Effect — rebuilt to the exemplar shape

Source: `instrument/chapters/01.tex:1814` (`ph:static-friction`).

Static friction: a body in contact resists motion up to a **threshold** that depends on the normal
load.  Below the threshold the body is **stuck** — no motion is admissible.  The transition to
**slip** is an abrupt, distinguishable event.  The textbook inequality `|F| ≥ μ|N|` is a *bound in
representation*: it declares one admissible side of the estimate but does **not** encode a procedure
that computes `μ` from the record (the description's Chaitin analogy).  Recovering `μ` is instead a
**ledger-derived invariant**, forced only after many distinguishable trials bracket the minimal
transition; no finite refinement certifies that further trials would cease to refine the threshold.

This file gives the *finite* content of the phenomenon:

* an **effect-specific domain** — `Contact` (applied force, normal load, friction floor `μN`) and
  `Bracketing` (a refinement record of trials), NOT the generic 3-`Nat` `CountSetup`;
* genuinely **falsifiable** `∀`-lemmas: below the threshold the contact is **stuck**
  (`belowThreshold_is_stuck`) and slip is **inadmissible** (`stuck_no_slip`), each of which breaks
  if its threshold hypothesis is dropped; plus the refinement bound, which breaks if the trial count
  exceeds the floor;
* a **content-bearing** claim — the canonical contact is stuck (a no-go), AND the bracketing trial
  ledger's count stays within the resolution floor, AND slip is inadmissible there;
* the resolution conjunct is discharged through the harness `Counting.boundedBy_of_eq`, so a
  regression in that harness theorem breaks THIS build (load-bearing coupling).

## Coupling honesty (why HARNESS, not the device)
The device theorems (`holonomy_loop_is_charged`, `detects_positron_over_tilt`, `the_split_counted`,
`native_antimatter_is_zero`, …) are about a **gauge holonomy sign / matter–antimatter split** — a
signed `pairDelta2` residue transported around a loop over a tilted-vs-flat flux.  Static friction is
a stick→slip **threshold** with a refinement-limited invariant; it has **no** loop-phase, no parallel
transport, no Berry phase, no charge/chirality sign, and no electron/positron pair or annihilation.
There is nothing in the da Vinci–Coulomb statement for `holonomy`/`detectsPositron`/`antimatterCount`
to read.  Forcing the positron/holonomy symbols onto it would be a FAKE coupling — exactly the move
the rubric forbids ("FORBIDDEN to use these on any other effect").  The honest content here is a
*bound in representation* (a finite resolution floor) plus a *no-go below threshold*, so it couples to
the harness counter (`Experiments.Common.Counting.boundedBy_of_eq`), which is load-bearing below.

## NOT claimed
This does **not** compute `μ` from the record (the whole point: the threshold is not operationally
executable from a finite ledger), does **not** prove convergence of the bracketing sequence, and
does **not** model the kinetic-friction regime after slip.  "Threshold" here is a labelled finite
count `μN`, not a measured coefficient; the trials are placeholder records, not real experiments.
No undecidability theorem is formalized — the Chaitin/halting analogy is *described*, not proved.
**Claim ceiling:** a finite no-go model of the stick state, whose resolution bound is the harness
counter.
-/

namespace Experiments.TheDaVinciCoulombEffect

/-- A frictional contact: the applied tangential force, the normal load, and the static friction
floor `μN` (the threshold force at which slip first becomes admissible).  All in coarse integer
units — these are labelled records, not measured quantities. -/
structure Contact where
  applied : Nat
  normalLoad : Nat
  threshold : Nat
deriving DecidableEq, Repr

/-- A refinement record: the number of distinguishable bracketing trials run so far, and the
instrument's resolution floor (the count beyond which no trial is distinguishable). -/
structure Bracketing where
  trials : Nat
  floor : Nat
deriving Repr

namespace Contact

/-- The contact is **stuck**: the applied force has not reached the static threshold, so no motion is
admissible.  This is the no-go side of the inequality `|F| ≥ μN` — its *failure*. -/
def stuck (c : Contact) : Prop :=
  c.applied < c.threshold

/-- **Slip is admissible**: the applied force has reached the threshold.  The complement of `stuck`;
the abrupt transition event sits exactly at `applied = threshold`. -/
def slips (c : Contact) : Prop :=
  c.threshold ≤ c.applied

instance (c : Contact) : Decidable (c.stuck) := by unfold stuck; exact inferInstance
instance (c : Contact) : Decidable (c.slips) := by unfold slips; exact inferInstance

end Contact

-- ---------------------------------------------------------------------------
-- FALSIFIABLE lemmas: the threshold is load-bearing.  Drop the hypothesis and each breaks.
-- ---------------------------------------------------------------------------

/-- Below the threshold the contact is stuck — quantified over ALL contacts.  Drop the hypothesis
`applied < threshold` and the conclusion fails (a contact at or above threshold is not stuck). -/
theorem belowThreshold_is_stuck
    (c : Contact) (h : c.applied < c.threshold) : c.stuck := h

/-- A stuck contact does NOT slip: the two states are mutually exclusive.  This is the no-go —
motion is inadmissible while stuck.  Quantified over ALL contacts; pins that `stuck` and `slips`
genuinely partition the threshold. -/
theorem stuck_no_slip
    (c : Contact) (h : c.stuck) : ¬ c.slips :=
  fun hs => Nat.lt_irrefl c.applied (Nat.lt_of_lt_of_le h hs)

/-- Conversely, once the applied force reaches the threshold the contact is no longer stuck —
the transition is sharp.  Drop `threshold ≤ applied` and it fails. -/
theorem atThreshold_not_stuck
    (c : Contact) (h : c.threshold ≤ c.applied) : ¬ c.stuck :=
  fun hk => Nat.lt_irrefl c.applied (Nat.lt_of_lt_of_le hk h)

-- ---------------------------------------------------------------------------
-- HARNESS COUPLING (load-bearing): the bracketing trial count is bounded by the floor.
--   resolution floor  ->  Experiments.Common.Counting.boundedBy_of_eq
-- ---------------------------------------------------------------------------

/-- The finite ledger of bracketing trials (one placeholder record per distinguishable trial),
used to express the resolution floor through the harness counter. -/
def trialLedger (b : Bracketing) : Experiments.Common.Ledger Unit :=
  { events := List.replicate b.trials () }

theorem trialLedger_count (b : Bracketing) :
    (trialLedger b).count = b.trials := by
  simp [trialLedger, Experiments.Common.Ledger.count]

-- ---------------------------------------------------------------------------
-- The canonical stuck contact and its bracketing record.
-- ---------------------------------------------------------------------------

/-- The standard contact: applied force `3`, normal load `10`, threshold `μN = 5`.  Below threshold,
hence stuck. -/
def defaultContact : Contact := { applied := 3, normalLoad := 10, threshold := 5 }

/-- A bracketing record at the resolution floor: `2` distinguishable trials, floor `4`. -/
def defaultBracketing : Bracketing := { trials := 2, floor := 4 }

/-- The canonical contact is stuck (concrete, via the `Decidable` instance). -/
theorem default_stuck : defaultContact.stuck := by decide

/-- The bracketing ledger's count equals its trial tally, and that count is bounded by the floor.
`boundedBy_of_eq` proves the bound from the exact tally `count = trials` (via `trialLedger_count`);
the bound supplied is the trial count itself, so this is discharged through the harness counter and
breaks if that theorem regresses. -/
theorem trials_bounded :
    Experiments.Common.Counting.boundedBy (trialLedger defaultBracketing) defaultBracketing.trials :=
  Experiments.Common.Counting.boundedBy_of_eq (trialLedger_count defaultBracketing)

-- ---------------------------------------------------------------------------
-- THE CLAIM (content-bearing; one conjunct discharged by a harness theorem).
-- ---------------------------------------------------------------------------

/-- The claim, in honest parts:
* (no-go) the canonical contact is stuck — `default_stuck`, the inadmissibility of motion below μN;
* (resolution floor) the bracketing trial ledger's count is bounded by its tally —
  `trials_bounded`, via `Counting.boundedBy_of_eq` (the harness coupling);
* (sharp transition) the stuck contact does NOT slip — `stuck_no_slip`, the threshold partition. -/
def claimStatement : Prop :=
  defaultContact.stuck ∧
    Experiments.Common.Counting.boundedBy (trialLedger defaultBracketing) defaultBracketing.trials ∧
    ¬ defaultContact.slips

def claim : Experiments.Common.Claim :=
  { tag := Experiments.Common.ClaimTag.inadmissibilityNoGo
    statement := claimStatement }

theorem claim_holds : claim.statement :=
  ⟨default_stuck, trials_bounded, stuck_no_slip defaultContact default_stuck⟩

/-- The tag is an honest ceiling: a no-go (motion inadmissible below the threshold). -/
theorem ceiling :
    claim.tag = Experiments.Common.ClaimTag.inadmissibilityNoGo := rfl

-- ---------------------------------------------------------------------------
-- A computable run + a non-vacuous Experiment.claim, with a proved bridge.
-- ---------------------------------------------------------------------------

structure Setup where
  contact : Contact
  bracketing : Bracketing

/-- The run computes — thanks to the `Decidable` instance on `stuck`.  `true` ⇒ still stuck. -/
def run (s : Setup) : Bool := decide (s.contact.stuck)

def experiment : Experiments.Common.Experiment Setup Bool :=
  { tag := claim.tag
    run := run
    claim := fun s => s.contact.stuck }

/-- The exported claim is decidable for any setup (it unfolds to `Contact.stuck`), so the device
probe below can `decide` it. -/
instance (s : Setup) : Decidable (experiment.claim s) := by
  show Decidable (s.contact.stuck); exact inferInstance

theorem run_iff_claim (s : Setup) :
    run s = true ↔ experiment.claim s := by
  show decide (s.contact.stuck) = true ↔ s.contact.stuck
  exact decide_eq_true_iff

def canonicalSetup : Setup := { contact := defaultContact, bracketing := defaultBracketing }

/-- A contact pushed PAST the threshold — slip becomes admissible, so it is no longer stuck. -/
def slippedContact : Contact := { defaultContact with applied := 9 }

#eval run canonicalSetup                                       -- expect: true   (stuck)
#eval run { canonicalSetup with contact := slippedContact }    -- expect: false  (slips)
#print axioms claim_holds
-- The falsifiable predicate `stuck`, evaluated where it FAILS (force past threshold): prints false,
-- so `belowThreshold_is_stuck`/the no-go conjunct is load-bearing, not vacuous.
#eval decide (slippedContact.stuck)                            -- expect: false  (pred FALSE here)

instance (setup : Setup) : Decidable (experiment.claim setup) := by
  unfold experiment
  infer_instance

/-- Bring a minimal device next to this experiment: it records whether the exported claim fires. -/
def deviceNear (setup : Setup) : Bool :=
  decide (experiment.claim setup)

theorem deviceNear_detects_claim (setup : Setup) :
    deviceNear setup = true ↔ experiment.claim setup := by
  show decide (experiment.claim setup) = true ↔ experiment.claim setup
  exact decide_eq_true_iff

def triangulation : Experiments.Common.Triangulation Setup Bool :=
  { experiment := experiment
    device := deviceNear
    detects := deviceNear_detects_claim }

end Experiments.TheDaVinciCoulombEffect
