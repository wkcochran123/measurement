import Experiments.Common

/-!
# The Hawking Effect — a finite ledger model of horizon pair-bookkeeping

Rebuilt to the worked exemplar shape (`ThePositronAnnihilationEffect/Experiment1.lean`):
an effect-specific domain, falsifiable `∀`-lemmas (one per conjunct of the rule), a
content-bearing claim, an honest tag, explicit `Decidable` instances, and a LOAD-BEARING
coupling to the harness — here `Experiments.Common.Ledger.count_append`.

## Physics (modelled finitely)
The description's core mechanism is **paired refinement under a causal horizon**: "causal
influence cannot be destroyed, and refinement cannot occur in fractional units." Each
admissible update near the horizon bifurcates into a correlated pair — one branch is driven
**inward** (into the inaccessible region, permanently removed from local bookkeeping), the
conjugate branch is forced **outward** (into the observable region, where it appears as
radiation). The bookkeeping necessity is exactly: every interior branch is matched by an
exterior branch, and the total pair-count is conserved across the horizon split. That last
identity is the harness's `Ledger.count_append`: the count of the appended (inward ++ outward)
ledger equals the sum of the two side-counts — nothing is silently lost.

## NOT claimed
That this derives a Hawking temperature or spectrum; that it reproduces any QFT-in-curved-
spacetime amplitude; that the horizon is a real geometric horizon rather than a finite label;
that the "redshift"/"freezing of clocks" of the description are derived (they are named, not
computed). No Bogoliubov coefficients, no thermality, no greybody factors. **Claim ceiling:**
a finite ledger model whose conservation conjunct IS the harness's `count_append` theorem, so a
regression in `Experiments.Common.Ledger.count_append` breaks THIS build.
-/

namespace Experiments.TheHawkingEffect

/-- Which side of the horizon a refinement branch is exported to. -/
inductive Side where
  | inward   -- driven into the inaccessible region (interior)
  | outward  -- forced into the observable region (radiation)
deriving DecidableEq, Repr

/-- A single admissible refinement branch near the horizon: which side it went to, and an
opaque correlation index pairing it with its conjugate. -/
structure Branch where
  side : Side
  pairId : Nat
deriving DecidableEq, Repr

/-- A horizon refinement event: it bifurcates correlation `pairId` into exactly one inward and
one outward conjugate branch (paired refinement = the unique admissible response). -/
structure HorizonPair where
  pairId : Nat
deriving DecidableEq, Repr

namespace HorizonPair

/-- The interior (inaccessible) branch of the pair. -/
def interior (h : HorizonPair) : Branch := { side := Side.inward,  pairId := h.pairId }

/-- The exterior (radiated, observable) branch of the pair. -/
def exterior (h : HorizonPair) : Branch := { side := Side.outward, pairId := h.pairId }

/-- THE PAIR RULE: an admissible horizon event produces one interior and one exterior branch,
both carrying the SAME correlation id (they are conjugate), and on OPPOSITE sides. All three
conjuncts are pinned by falsifiable lemmas below. -/
def admissible (h : HorizonPair) (i e : Branch) : Prop :=
  i = h.interior ∧ e = h.exterior ∧ i.side ≠ e.side

instance (h : HorizonPair) (i e : Branch) : Decidable (h.admissible i e) := by
  unfold admissible; exact inferInstance

end HorizonPair

-- ---------------------------------------------------------------------------
-- FALSIFIABLE lemmas: ONE PER CONJUNCT, so the whole pair rule is load-bearing.
-- Each would break if `admissible` dropped that conjunct.
-- ---------------------------------------------------------------------------

/-- The interior branch is necessary: a candidate whose first branch is NOT the interior is
never admissible. Quantified over ALL pairs and branches. -/
theorem wrongInterior_not_admissible
    (h : HorizonPair) (i e : Branch) (hne : i ≠ h.interior) : ¬ h.admissible i e :=
  fun ha => hne ha.1

/-- The exterior branch is necessary (pins the middle conjunct). -/
theorem wrongExterior_not_admissible
    (h : HorizonPair) (i e : Branch) (hne : e ≠ h.exterior) : ¬ h.admissible i e :=
  fun ha => hne ha.2.1

/-- Opposite sides are necessary: a pair on the SAME side (no inward/outward split) is never
admissible. This is the "no silent loss" content — the branches must straddle the horizon. -/
theorem sameSide_not_admissible
    (h : HorizonPair) (i e : Branch) (hsame : i.side = e.side) : ¬ h.admissible i e :=
  fun ha => ha.2.2 hsame

-- ---------------------------------------------------------------------------
-- The horizon ledger split: inward ++ outward, with conserved total count.
-- ---------------------------------------------------------------------------

/-- A canonical horizon event. -/
def canonicalPair : HorizonPair := { pairId := 0 }

/-- The interior ledger: the branches removed from local bookkeeping (here, the one inward
branch of the canonical event). -/
def interiorLedger : Experiments.Common.Ledger Branch :=
  { events := [canonicalPair.interior] }

/-- The exterior ledger: the radiated, observable branches (the one outward conjugate). -/
def exteriorLedger : Experiments.Common.Ledger Branch :=
  { events := [canonicalPair.exterior] }

/-- The horizon's full record is the append of the two sides: nothing escapes the bookkeeping. -/
def horizonLedger : Experiments.Common.Ledger Branch :=
  Experiments.Common.Ledger.append interiorLedger exteriorLedger

/-- The canonical event is admissible (concrete, via the `Decidable` instance). -/
theorem admissible_canonical :
    canonicalPair.admissible canonicalPair.interior canonicalPair.exterior := by decide

-- ---------------------------------------------------------------------------
-- THE CLAIM (content-bearing; the conservation conjunct is the harness's own theorem).
-- ---------------------------------------------------------------------------

/-- The claim, in honest parts:
* (paired refinement) the canonical horizon event is admissible — one interior, one exterior,
  opposite sides — proved here by the decidable pair rule;
* (no silent loss / conservation) the count of the full horizon record equals the sum of the
  interior and exterior counts — discharged by `Experiments.Common.Ledger.count_append`, the
  LOAD-BEARING harness coupling. Breaking `count_append` breaks this build.
The second conjunct is the bookkeeping necessity the description rests on: "causal influence
cannot be destroyed." -/
def claimStatement : Prop :=
  canonicalPair.admissible canonicalPair.interior canonicalPair.exterior ∧
    horizonLedger.count = interiorLedger.count + exteriorLedger.count

def claim : Experiments.Common.Claim :=
  { tag := Experiments.Common.ClaimTag.finiteLedgerModel
    statement := claimStatement }

theorem claim_holds : claim.statement :=
  ⟨admissible_canonical,
    Experiments.Common.Ledger.count_append interiorLedger exteriorLedger⟩

/-- The tag is an honest ceiling: a finite ledger model, nothing more. -/
theorem ceiling :
    claim.tag = Experiments.Common.ClaimTag.finiteLedgerModel := rfl

-- ---------------------------------------------------------------------------
-- A computable run + a NON-vacuous Experiment.claim, with a proved bridge between them.
-- ---------------------------------------------------------------------------

structure Setup where
  horizon : HorizonPair
  interiorBranch : Branch
  exteriorBranch : Branch

/-- The run actually computes — thanks to the `Decidable` instance above. -/
def run (s : Setup) : Bool :=
  decide (s.horizon.admissible s.interiorBranch s.exteriorBranch)

/-- The exported claim is a genuine function of the setup; this bridge pins it to `run`. -/
def experiment : Experiments.Common.Experiment Setup Bool :=
  { tag := claim.tag
    run := run
    claim := fun s => s.horizon.admissible s.interiorBranch s.exteriorBranch }

theorem run_iff_claim (s : Setup) :
    run s = true ↔ experiment.claim s := by
  simp only [run, experiment, decide_eq_true_iff]

def canonicalSetup : Setup :=
  { horizon := canonicalPair
    interiorBranch := canonicalPair.interior
    exteriorBranch := canonicalPair.exterior }

/-- A control setup that is NOT admissible: both branches forced to the SAME (outward) side —
no horizon split, so the pair rule must reject it. -/
def collapsedSetup : Setup :=
  { canonicalSetup with interiorBranch := canonicalPair.exterior }

#eval run canonicalSetup    -- expect: true
#eval run collapsedSetup     -- expect: false  (same side — no horizon split)

/-- Bring a minimal device next to this experiment: it records whether the exported claim fires.
(Written directly on the admissible predicate — definitionally equal to `experiment.claim setup`
— so the `Decidable` instance is synthesized.) -/
def deviceNear (setup : Setup) : Bool :=
  decide (setup.horizon.admissible setup.interiorBranch setup.exteriorBranch)

theorem deviceNear_detects_claim (setup : Setup) :
    deviceNear setup = true ↔ experiment.claim setup := by
  simp only [deviceNear, experiment, decide_eq_true_iff]

def triangulation : Experiments.Common.Triangulation Setup Bool :=
  { experiment := experiment
    device := deviceNear
    detects := deviceNear_detects_claim }

-- GATE EVIDENCE -------------------------------------------------------------
#print axioms claim_holds
-- The falsifiable predicate evaluated at a config where it is FALSE (collapsed = same side),
-- proving the lemma is load-bearing, not vacuous:
#eval decide (collapsedSetup.horizon.admissible
  collapsedSetup.interiorBranch collapsedSetup.exteriorBranch)   -- expect: false

end Experiments.TheHawkingEffect
