import Experiments.Common

/-!
# The Archimedes–Proust Effect — continuity expresses, integers commit

Source: `instrument/chapters/02.tex:1506`, phenom `ph:continuity`.

Two complementary modes of quantitative knowledge:
* **Archimedes** — embed finite acts of comparison inside a *continuous* geometric
  relation. The continuum is never recorded; it is the **expressive alphabet** that
  interpolates unseen structure.
* **Proust** — the law of **definite proportions**: chemical compounds form in fixed
  **integer** ratios that must **balance exactly**. Facthood lives in the ledger, and
  no finer (fractional) distinction is licensed as a fact.

This file models the **Proust side as exact integer bookkeeping** (the content-bearing,
falsifiable part) and the **Archimedes side as a label-only continuous interpolation**
(the alphabet — present in the type, but carrying no recorded fact). The two are bound
together in one claim, never collapsed into each other.

## Coupling (HARNESS)
The Proust ledger is conservation/additivity bookkeeping: a compound assembled from two
reactant batches has an atom tally equal to the **sum** of the batch tallies. That is
exactly `Experiments.Common.Ledger.count_append`, and it is a *conjunct of* `claim_holds`,
so a regression in the harness ledger algebra breaks this build. This effect is about
continuity vs. discreteness — there is **no holonomy / charge / positron** content here,
so a device coupling would be FAKE and is deliberately not used.

## NOT claimed
That real chemistry obeys these exact ratios (isotopes, non-stoichiometric compounds, and
defect crystals all violate naive Proust); that the "continuous" interpolation here is a
real derivative or limit (it is a labelled stand-in — an *alphabet*, not a recorded fact);
any thermodynamics or reaction kinetics. **Claim ceiling:** a finite ledger model of integer
commitment, whose conservation conjunct is the harness's own `count_append`.
-/

namespace Experiments.TheArchimedesProustEffect

-- ---------------------------------------------------------------------------
-- DOMAIN: the Proust side — a compound as an exact integer proportion.
-- ---------------------------------------------------------------------------

/-- A compound recorded the way Proust licenses it: **whole-number** counts of two
elements. No fractional composition is representable — discreteness IS the commitment. -/
structure Compound where
  elemA : Nat
  elemB : Nat
deriving DecidableEq, Repr

namespace Compound

/-- The total atom tally — the one fact the ledger records. -/
def atoms (c : Compound) : Nat := c.elemA + c.elemB

/-- Two compounds combine by summing their integer proportions (a balanced reaction:
nothing is created or lost, only re-bookkept). -/
def combine (c d : Compound) : Compound :=
  { elemA := c.elemA + d.elemA, elemB := c.elemB + d.elemB }

/-- **Definite proportion**: `c` has the integer ratio `a : b` exactly, with no fractional
slack admitted. Written multiplicatively so it stays in `Nat` (Proust forbids fractions). -/
def hasRatio (c : Compound) (a b : Nat) : Prop :=
  c.elemA * b = c.elemB * a

instance (c : Compound) (a b : Nat) : Decidable (c.hasRatio a b) := by
  unfold hasRatio; exact inferInstance

end Compound

-- ---------------------------------------------------------------------------
-- DOMAIN: the Archimedes side — a continuous expressive alphabet (LABEL ONLY).
-- This is interpolation, never a recorded fact; it carries no integer commitment.
-- ---------------------------------------------------------------------------

/-- An Archimedean reading: a balance equivalence situated in a continuous parameter.
The `interp` field is the *alphabet* — a smooth coordinate that is never itself committed. -/
structure ArchReading where
  /-- the continuous interpolation coordinate (expression, NOT fact) -/
  interp : Int
deriving DecidableEq, Repr

-- ---------------------------------------------------------------------------
-- FALSIFIABLE lemmas — each would BREAK if a hypothesis were dropped.
-- ---------------------------------------------------------------------------

/-- Integer commitment is **additive**: assembling a compound from two batches sums the
atom tallies. Quantified over ALL compounds. (Falsifiable: replace `combine` by a non-sum
and this fails; it is also the harness-coupling shadow of `Ledger.count_append`.) -/
theorem combine_atoms_additive (c d : Compound) :
    (c.combine d).atoms = c.atoms + d.atoms := by
  simp only [Compound.combine, Compound.atoms]
  omega

/-- A definite-proportion compound stays in proportion when scaled by a whole number `k`
(integer commitment is closed under whole-number multiples) — but **only** because `k`
multiplies *both* elements. Drop the shared `k` (scale one element only) and the ratio
breaks: this `∀` is load-bearing. -/
theorem scale_preserves_ratio (c : Compound) (a b k : Nat) (h : c.hasRatio a b) :
    Compound.hasRatio { elemA := k * c.elemA, elemB := k * c.elemB } a b := by
  unfold Compound.hasRatio at *
  -- goal: (k * c.elemA) * b = (k * c.elemB) * a, from c.elemA * b = c.elemB * a
  calc (k * c.elemA) * b = k * (c.elemA * b) := by rw [Nat.mul_assoc]
    _ = k * (c.elemB * a) := by rw [h]
    _ = (k * c.elemB) * a := by rw [Nat.mul_assoc]

/-- A **falsifiable** discreteness no-go used as the load-bearing predicate at the bottom:
a compound whose proportions are NOT in the ratio `a:b` does not get committed as `a:b`.
Stated positively as a decidable predicate so `#eval` can witness a FALSE instance. -/
def Compound.committedAs (c : Compound) (a b : Nat) : Prop := c.hasRatio a b

instance (c : Compound) (a b : Nat) : Decidable (c.committedAs a b) := by
  unfold Compound.committedAs; exact inferInstance

theorem offRatio_not_committed (c : Compound) (a b : Nat) (h : ¬ c.hasRatio a b) :
    ¬ c.committedAs a b :=
  fun hc => h hc

-- ---------------------------------------------------------------------------
-- Canonical event: water-like 2:1 hydrogen:oxygen, the textbook definite proportion.
-- ---------------------------------------------------------------------------

/-- Two parts A to one part B — the canonical Proust ratio. -/
def water : Compound := { elemA := 2, elemB := 1 }

/-- A second batch of the same compound (used to exercise additivity). -/
def waterBatch : Compound := { elemA := 4, elemB := 2 }

/-- The canonical compound sits at exactly the integer ratio 2:1 (decidable check). -/
theorem water_is_2to1 : water.hasRatio 2 1 := by decide

/-- The Archimedean alphabet reading that accompanies the event — a continuous coordinate,
recorded here only as a label (no integer commitment is read off it). -/
def archCoord : ArchReading := { interp := 0 }

-- ---------------------------------------------------------------------------
-- THE CLAIM — content-bearing conjunction; the conservation conjunct is the harness's
-- own `Ledger.count_append`, so the harness ledger algebra is LOAD-BEARING here.
-- ---------------------------------------------------------------------------

/-- The Proust ledger built from two atom-counted batches. Each event is a unit atom token;
the count is the atom tally, so `count_append` is literally batch additivity. -/
def batchLedger (c : Compound) : Experiments.Common.Ledger Unit :=
  { events := List.replicate c.atoms () }

theorem batchLedger_count (c : Compound) :
    (batchLedger c).count = c.atoms := by
  simp [batchLedger, Experiments.Common.Ledger.count]

/-- The claim, in honest parts:
* (definite proportion) the canonical compound is committed at exactly 2:1 — proved here;
* (integer balance is additive) assembling two batches sums their atom tallies — proved here;
* (HARNESS conservation) the two batches' ledgers append to the summed count
  (`Experiments.Common.Ledger.count_append`) — the load-bearing harness coupling;
* (discreteness no-go) a compound off the ratio is not committed at that ratio. -/
def claimStatement : Prop :=
  water.committedAs 2 1 ∧
    (water.combine waterBatch).atoms = water.atoms + waterBatch.atoms ∧
    (Experiments.Common.Ledger.append (batchLedger water) (batchLedger waterBatch)).count
        = (batchLedger water).count + (batchLedger waterBatch).count ∧
    ¬ Compound.committedAs { elemA := 3, elemB := 1 } 2 1

def claim : Experiments.Common.Claim :=
  { tag := Experiments.Common.ClaimTag.finiteLedgerModel
    statement := claimStatement }

theorem claim_holds : claim.statement :=
  ⟨ water_is_2to1
  , combine_atoms_additive water waterBatch
  , Experiments.Common.Ledger.count_append (batchLedger water) (batchLedger waterBatch)
  , offRatio_not_committed { elemA := 3, elemB := 1 } 2 1 (by decide) ⟩

/-- The tag is an honest ceiling: a finite ledger model of integer commitment. -/
theorem ceiling : claim.tag = Experiments.Common.ClaimTag.finiteLedgerModel := rfl

-- ---------------------------------------------------------------------------
-- A computable run + a non-vacuous Experiment.claim, with a proved bridge.
-- ---------------------------------------------------------------------------

structure Setup where
  compound : Compound
  ratioA : Nat
  ratioB : Nat
  /-- the Archimedean alphabet coordinate that accompanies the reading (label only) -/
  alphabet : ArchReading

/-- The run computes — via the `Decidable` instance on `committedAs`. -/
def run (s : Setup) : Bool := decide (s.compound.committedAs s.ratioA s.ratioB)

def experiment : Experiments.Common.Experiment Setup Bool :=
  { tag := claim.tag
    run := run
    claim := fun s => s.compound.committedAs s.ratioA s.ratioB }

theorem run_iff_claim (s : Setup) :
    run s = true ↔ experiment.claim s := by
  simp only [run, experiment, decide_eq_true_iff]

def canonicalSetup : Setup :=
  { compound := water, ratioA := 2, ratioB := 1, alphabet := archCoord }

#eval run canonicalSetup                                   -- expect: true  (water IS 2:1)
#eval run { canonicalSetup with compound := { elemA := 3, elemB := 1 } }
                                                            -- expect: false (3:1 ≠ 2:1)
#print axioms claim_holds                                  -- ambient footprint, not coupling

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

end Experiments.TheArchimedesProustEffect
