import Experiments.Common

/-!
# Hawking Radiation — an effect-specific finite model (exemplar shape)

Source: `instrument/chapters/06.tex:655` (`ex:hawking`).

## Physics (modelled finitely)
A particle-creation pair straddles a black-hole horizon: an outward event
`Eout` and an inward partner `Ein`.  While **both are unmeasured** the pair is an
*uncorrelant* — the two readings may permute freely and the scalar invariant
(here: the pair's total charge label, `Ein.charge + Eout.charge`) is preserved.
Once an observer **at infinity measures `Eout`**, the ordering is fixed and `Ein`
is forced to the *complementary* state inside the horizon: its charge must be the
negation of the measured outward charge, so that the two restrictions agree on the
shared horizon boundary.  The outward quantum is the Hawking radiation; the inward
partner is the lost-information complement.

We model the horizon as a `Boundary`: each event restricts to a single shared
boundary reading, namely the *signed charge that crosses the horizon*.  The pair is
**admissible** exactly when the two events present the same boundary reading (the
device's `Boundary.compatible`) — this is the finite shadow of "the inward partner
is forced complementary to the measured outward one."

## NOT claimed
That this reproduces the Hawking temperature, the thermal spectrum, the Bogoliubov
mode-mixing, any QFT-in-curved-spacetime amplitude, or actual information loss /
unitarity. `charge`, `horizon`, and the "complementary state" are **labels** on a
finite count model — no spacetime metric, no horizon area, no `kT = ℏκ/2π`.
**Claim ceiling:** a finite two-region *boundary-compatibility* model of the
horizon-pair correlation, whose admissibility conjunct is the harness's own
`Boundary.compatible` identity.  This is a smooth/limit phenomenon represented by
a discrete stand-in, so the tag is `smoothShadowAnalogy`.
-/

namespace Experiments.HawkingRadiation

/-- One horizon event: a side (`inside`/`outside` the horizon) and a signed charge
reading (`Int`, so the complementary partner can carry the negation). -/
inductive Side where
  | inside
  | outside
deriving DecidableEq, Repr

structure HorizonEvent where
  side : Side
  charge : Int
deriving DecidableEq, Repr

/-- A created pair straddling the horizon: the outward quantum and its inward partner. -/
structure Pair where
  outward : HorizonEvent
  inward : HorizonEvent
deriving DecidableEq, Repr

/-- The horizon as a `Boundary`: each event restricts to the SIGNED charge that
crosses it — outward charges count `+`, inward (lost-behind-horizon) charges count
with the opposite sign.  Two events "agree on the boundary" iff their crossings net
to the same value, i.e. iff the inward partner is the charge-complement of the
outward one. -/
def crossing (e : HorizonEvent) : Int :=
  match e.side with
  | Side.outside => e.charge
  | Side.inside => -e.charge

def horizon : Experiments.Common.Boundary HorizonEvent Int :=
  { restrict := crossing }

/-- A pair is ADMISSIBLE iff its two events present the same horizon reading
(`Boundary.compatible`): the outward and inward charges are complementary.
This is the load-bearing harness conjunct. -/
def admissible (p : Pair) : Prop :=
  horizon.compatible p.outward p.inward

/-- The scalar invariant preserved while the pair is unmeasured: the total pair
charge.  For an admissible (complementary) pair across the horizon this is `0` —
pair creation from the vacuum carries no net charge. -/
def totalCharge (p : Pair) : Int :=
  p.outward.charge + p.inward.charge

-- Decidable instances so `decide`/`#eval` see through the predicates.
instance : DecidableEq Experiments.Common.ClaimTag := by unfold DecidableEq; exact inferInstance
instance (p : Pair) : Decidable (admissible p) := by
  unfold admissible Experiments.Common.Boundary.compatible; exact inferInstance

-- ---------------------------------------------------------------------------
-- FALSIFIABLE lemmas: each would break if its hypothesis were dropped.
-- ---------------------------------------------------------------------------

/-- THE FORCING LEMMA (falsifiable, ∀-quantified): if a pair is admissible, the
inward partner's charge is forced to the negation of the outward charge — the
"complementary state inside the horizon".  Drop the `admissible` hypothesis and the
conclusion is false (a free pair can carry any inward charge). -/
theorem inward_forced_complementary (p : Pair)
    (hout : p.outward.side = Side.outside) (hin : p.inward.side = Side.inside)
    (h : admissible p) :
    p.inward.charge = -p.outward.charge := by
  unfold admissible Experiments.Common.Boundary.compatible horizon crossing at h
  simp only [hout, hin] at h
  -- h : p.outward.charge = -p.inward.charge  ⇒  inward = -outward
  omega

/-- An outward reading whose inward partner is NOT its complement (`r ≠ -q`) is
INADMISSIBLE — the horizon would not balance, so such a pair cannot form.
Quantified over all charges; load-bearing for `admissible`. -/
theorem mismatched_partner_inadmissible (q r : Int) (h : r ≠ -q) :
    ¬ admissible { outward := { side := Side.outside, charge := q }
                 , inward := { side := Side.inside, charge := r } } := by
  unfold admissible Experiments.Common.Boundary.compatible horizon crossing
  simp only
  omega

-- ---------------------------------------------------------------------------
-- The canonical Hawking pair: an outward +1 quantum, an inward complementary -1
-- (inside, so its crossing is +1, matching the outward crossing) — a charge-0
-- vacuum pair whose two horizon readings agree.
-- ---------------------------------------------------------------------------

def canonicalPair : Pair :=
  { outward := { side := Side.outside, charge := 1 }
  , inward := { side := Side.inside, charge := -1 } }

theorem canonical_admissible : admissible canonicalPair := by decide

theorem canonical_charge_conserved : totalCharge canonicalPair = 0 := by decide

-- ---------------------------------------------------------------------------
-- THE CLAIM (content-bearing conjunction; one conjunct is the harness identity).
-- ---------------------------------------------------------------------------

/-- The claim, in honest parts:
* (admissibility — harness) the canonical horizon pair satisfies
  `Boundary.compatible`, i.e. the inward partner is forced complementary
  (`Experiments.Common.Boundary.compatible`, via `canonical_admissible`);
* (invariant) the total pair charge is conserved at `0`;
* (forcing) for the canonical admissible pair, the inward charge is the negation
  of the outward charge — the inward partner is genuinely determined by the
  measured outward one.
Breaking the `Boundary.compatible` identity in the harness breaks the first
conjunct, hence this build. -/
def claimStatement : Prop :=
  admissible canonicalPair ∧
    totalCharge canonicalPair = 0 ∧
    canonicalPair.inward.charge = -canonicalPair.outward.charge

def claim : Experiments.Common.Claim :=
  { tag := Experiments.Common.ClaimTag.smoothShadowAnalogy
    statement := claimStatement }

theorem claim_holds : claim.statement :=
  ⟨canonical_admissible, canonical_charge_conserved,
    inward_forced_complementary canonicalPair rfl rfl canonical_admissible⟩

/-- The tag is an honest ceiling: a finite smooth-shadow stand-in, nothing more. -/
theorem ceiling :
    claim.tag = Experiments.Common.ClaimTag.smoothShadowAnalogy := rfl

-- ---------------------------------------------------------------------------
-- A computable run + a non-vacuous Experiment.claim, with a proved bridge.
-- ---------------------------------------------------------------------------

abbrev Setup := Pair

/-- The run actually computes — via the `Decidable` instance for `admissible`. -/
def run (s : Setup) : Bool := decide (admissible s)

def experiment : Experiments.Common.Experiment Setup Bool :=
  { tag := claim.tag
    run := run
    claim := fun s => admissible s }

theorem run_iff_claim (s : Setup) :
    run s = true ↔ experiment.claim s := by
  simp only [run, experiment, decide_eq_true_iff]

#eval run canonicalPair                                   -- expect: true
-- A mismatched partner (inward +2 against outward +1) is INADMISSIBLE: the
-- falsifiable predicate evaluates to FALSE, so the lemma above is load-bearing.
#eval run { outward := { side := Side.outside, charge := 1 }
          , inward := { side := Side.inside, charge := 2 } }   -- expect: false

#print axioms claim_holds

/-- Bring a minimal device next to this experiment: it records whether the exported claim fires. -/
def deviceNear (setup : Setup) : Bool :=
  run setup

theorem deviceNear_detects_claim (setup : Setup) :
    deviceNear setup = true ↔ experiment.claim setup := by
  simpa [deviceNear] using run_iff_claim setup

def triangulation : Experiments.Common.Triangulation Setup Bool :=
  { experiment := experiment
    device := deviceNear
    detects := deviceNear_detects_claim }

end Experiments.HawkingRadiation
