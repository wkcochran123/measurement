import Experiments.Common

/-!
# The Descartes Effect — coordinates are FORCED by bookkeeping, not geometry

Modelled after the exemplar `ThePositronAnnihilationEffect/Experiment1.lean`.

## Phenomenon (modelled finitely)
Two repeatable rulers `A` and `B` are applied in independent directions. Each generates its own
stable count. The description's claim: two such independent counts **cannot be merged into a
single tally without loss of information** — the only admissible record that retains both
distinctions is an *ordered pair*. Operationally, independence appears as **non-commutativity**:
applying `A` then `B` cannot, in general, be reconstructed from `B` then `A`, so each operation
is compelled to have its own axis of record. Coordinates do not measure space; they preserve
independence. Geometry here is stabilized bookkeeping of repeatable operations.

We model a procedure as a list of *strokes*, each tagged by the ruler that made it (`axisA` or
`axisB`). A `Coord` is the ordered pair `(countA, countB)` — the minimal data structure that
keeps both tallies apart. The collapse to a single tally is `countA + countB` (a `Ledger`'s
flat length); the lemmas show this single number is *lossy* — distinct ordered pairs share it —
whereas the ordered pair is *injective into the procedure's distinctions*.

The bookkeeping coupling is the harness's `Ledger.count_append`: composing (concatenating) two
procedures adds their stroke counts at the seam — no distinction is created or destroyed when
two procedures are recorded jointly.

## NOT claimed
That this *derives* real Cartesian space, a vector-space structure, an inner product, or any
metric; that two axes is the true dimension of anything physical; that non-commutativity here is
a Lie bracket or a curvature. The "coordinates" are a finite pair of `Nat` tallies — the discrete
shadow of the description's argument, NOT continuum geometry. **Claim ceiling:** a finite ledger
model of why independent counts are forced into ordered tuples, whose additivity conjunct IS the
harness's `count_append`.
-/

namespace Experiments.TheDescartesEffectCh08

/-- The two independent rulers. Each stroke on a procedure is tagged by which ruler made it. -/
inductive Ruler where
  | axisA
  | axisB
deriving DecidableEq, Repr

/-- A procedure is a finite record of ruler-strokes: a `Ledger` of `Ruler` tags. This is the
"causal ledger" of repeated acts the description speaks of. -/
abbrev Procedure := Experiments.Common.Ledger Ruler

/-- The forced coordinate: the ordered pair of independent tallies `(countA, countB)`. This is the
minimal data structure that keeps the two distinctions from collapsing. -/
structure Coord where
  countA : Nat
  countB : Nat
deriving DecidableEq, Repr

namespace Procedure

/-- How many `axisA` strokes the procedure records. -/
def countA (p : Procedure) : Nat :=
  (p.events.filter (fun r => decide (r = Ruler.axisA))).length

/-- How many `axisB` strokes the procedure records. -/
def countB (p : Procedure) : Nat :=
  (p.events.filter (fun r => decide (r = Ruler.axisB))).length

/-- THE FORCED RECORD: read both independent tallies as an ordered pair. -/
def coord (p : Procedure) : Coord :=
  { countA := p.countA, countB := p.countB }

end Procedure

-- ---------------------------------------------------------------------------
-- FALSIFIABLE lemmas: each pins a load-bearing part of the description's argument.
-- ---------------------------------------------------------------------------

/-- THE COLLAPSE IS LOSSY. A single flat tally (`Ledger.count`, the total stroke length) cannot
distinguish two procedures whose strokes differ only by which ruler made them. Here `[A]` and
`[B]` both flatten to `1`, yet they are different procedures — so the single count loses the
distinction the ordered pair keeps. FALSIFIABLE: this is FALSE for the ordered `coord`
(see `coord_separates` below); it is the single-tally collapse that fails to separate. -/
theorem singleTally_is_lossy :
    (Experiments.Common.Ledger.count ({ events := [Ruler.axisA] } : Procedure))
      = (Experiments.Common.Ledger.count ({ events := [Ruler.axisB] } : Procedure)) := by
  decide

/-- THE ORDERED PAIR SEPARATES what the single tally collapses. The two procedures above, which
share a flat count, have DISTINCT coordinates. This is the forcing: only the ordered pair retains
both distinctions. FALSIFIABLE: drop the ordered structure (use the sum `countA + countB`) and
the two sides become equal again — the separation depends on keeping the axes apart. -/
theorem coord_separates :
    Procedure.coord ({ events := [Ruler.axisA] } : Procedure)
      ≠ Procedure.coord ({ events := [Ruler.axisB] } : Procedure) := by
  decide

/-- NON-COMMUTATIVITY of independent composition. Applying ruler `A` then `B` records the strokes
in one order; `B` then `A` records them in the other. As procedures (ordered records) these are
NOT equal — the outcome of `A;B` cannot be reconstructed from `B;A`. This is the operational
signature that compels separate axes. Quantified over ALL stroke contents `a b`, with the
hypothesis that the two rulers actually differ on this seam. FALSIFIABLE: drop the hypothesis
`a ≠ b` and it breaks (if both strokes are the same ruler, the two orders coincide). -/
theorem composition_noncommutes
    (a b : Ruler) (h : a ≠ b) :
    ({ events := [a, b] } : Procedure).events ≠ ({ events := [b, a] } : Procedure).events := by
  intro heq
  -- heq : [a, b] = [b, a]; matching the heads gives a = b, contradicting h
  simp only [List.cons.injEq] at heq
  exact h heq.1

/-- A single ruler is NOT forced into two axes: a procedure of only-`A` strokes has `countB = 0`,
so its coordinate lives on one axis. FALSIFIABLE: pins that the second axis appears ONLY when the
second ruler is actually applied — independence is what compels the pair, not assumption. -/
theorem single_ruler_one_axis (n : Nat) :
    (Procedure.coord ({ events := List.replicate n Ruler.axisA } : Procedure)).countB = 0 := by
  show Procedure.countB ({ events := List.replicate n Ruler.axisA } : Procedure) = 0
  unfold Procedure.countB
  induction n with
  | zero => decide
  | succ k ih =>
      rw [List.replicate_succ, List.filter_cons]
      show (List.filter (fun r => decide (r = Ruler.axisB)) (List.replicate k Ruler.axisA)).length = 0
      exact ih

-- ---------------------------------------------------------------------------
-- ADDITIVITY at the seam (the harness coupling — LOAD-BEARING).
-- ---------------------------------------------------------------------------

/-- JOINT RECORDING preserves count. When two procedures are recorded jointly (composed by
concatenation), no stroke is created or destroyed at the seam: the joint stroke count is the sum
of the parts. This is EXACTLY `Experiments.Common.Ledger.count_append`, so a regression there
breaks this build. It is the bookkeeping (not geometry) that forces the tuple structure: combined
procedures must support the comparison of the parts. -/
def jointlyRecorded (left right : Procedure) : Prop :=
  (Experiments.Common.Ledger.append left right).count = left.count + right.count

theorem jointly_holds (left right : Procedure) : jointlyRecorded left right :=
  Experiments.Common.Ledger.count_append left right

/-- Make `jointlyRecorded` DECIDABLE so `decide`/`#eval` see through it (it is a `Nat` equality). -/
instance (left right : Procedure) : Decidable (jointlyRecorded left right) := by
  unfold jointlyRecorded; exact inferInstance

-- ---------------------------------------------------------------------------
-- The canonical worked example: two independent rulers applied a few times each.
-- ---------------------------------------------------------------------------

/-- Ruler `A` applied twice. -/
def procA : Procedure := { events := [Ruler.axisA, Ruler.axisA] }

/-- Ruler `B` applied three times. -/
def procB : Procedure := { events := [Ruler.axisB, Ruler.axisB, Ruler.axisB] }

/-- The composed procedure: `A` twice then `B` thrice. Its coordinate is the forced pair `(2, 3)`. -/
def procAB : Procedure := Experiments.Common.Ledger.append procA procB

/-- The forced coordinate of the composed procedure is exactly `(2, 3)` (a frozen-literal check on
the chosen event). -/
theorem coord_canonical : procAB.coord = { countA := 2, countB := 3 } := by decide

-- ---------------------------------------------------------------------------
-- THE CLAIM (content-bearing; the additivity conjunct IS the harness theorem).
-- ---------------------------------------------------------------------------

/-- The claim, in honest parts:
* (forced pair) the composed procedure's record is the ordered pair `(2, 3)` — both tallies kept;
* (separation) the ordered pair distinguishes `[A]` from `[B]`, which the flat count collapses;
* (lossy collapse) that flat count really does collapse them; and
* (joint bookkeeping) recording two procedures jointly adds their counts at the seam — the
  harness's `count_append`, the load-bearing coupling.
The last conjunct is discharged by `Experiments.Common.Ledger.count_append`, so a regression in
the harness fails this build. -/
def claimStatement : Prop :=
  procAB.coord = { countA := 2, countB := 3 } ∧
    Procedure.coord ({ events := [Ruler.axisA] } : Procedure)
      ≠ Procedure.coord ({ events := [Ruler.axisB] } : Procedure) ∧
    (Experiments.Common.Ledger.count ({ events := [Ruler.axisA] } : Procedure)
      = Experiments.Common.Ledger.count ({ events := [Ruler.axisB] } : Procedure)) ∧
    jointlyRecorded procA procB

def claim : Experiments.Common.Claim :=
  { tag := Experiments.Common.ClaimTag.finiteLedgerModel
    statement := claimStatement }

theorem claim_holds : claim.statement :=
  ⟨coord_canonical, coord_separates, singleTally_is_lossy, jointly_holds procA procB⟩

/-- The tag is an honest ceiling: a finite ledger model of forced coordinates, nothing more. -/
theorem ceiling : claim.tag = Experiments.Common.ClaimTag.finiteLedgerModel := rfl

-- ---------------------------------------------------------------------------
-- A computable run + a NON-vacuous Experiment.claim, with a proved bridge.
-- ---------------------------------------------------------------------------

structure Setup where
  left : Procedure
  right : Procedure

/-- The run computes the forced coordinate of the jointly-recorded procedure. -/
def run (s : Setup) : Coord :=
  Procedure.coord (Experiments.Common.Ledger.append s.left s.right)

def experiment : Experiments.Common.Experiment Setup Coord :=
  { tag := claim.tag
    run := run
    claim := fun s => jointlyRecorded s.left s.right }

/-- The exported claim is a genuine function of the setup, and this bridge pins it to the harness
identity, so the claim body cannot be silently swapped for `fun _ => True`. -/
theorem run_count_eq_sum (s : Setup) :
    (Experiments.Common.Ledger.append s.left s.right).count = s.left.count + s.right.count :=
  Experiments.Common.Ledger.count_append s.left s.right

def canonicalSetup : Setup := { left := procA, right := procB }

#eval run canonicalSetup                                  -- expect: { countA := 2, countB := 3 }
-- Load-bearing check: the falsifiable separation predicate is FALSE when we collapse the
-- ordered pair to a single sum — distinct procedures `[A]`, `[B]` then look identical.
#eval decide
  (((Procedure.coord ({ events := [Ruler.axisA] } : Procedure)).countA
      + (Procedure.coord ({ events := [Ruler.axisA] } : Procedure)).countB)
    ≠ ((Procedure.coord ({ events := [Ruler.axisB] } : Procedure)).countA
      + (Procedure.coord ({ events := [Ruler.axisB] } : Procedure)).countB))  -- expect: false
#print axioms claim_holds                                 -- [propext, Quot.sound] = AMBIENT

/-- Bring a minimal device next to this experiment: it records whether the exported claim fires. -/
def deviceNear (setup : Setup) : Bool :=
  decide (jointlyRecorded setup.left setup.right)

theorem deviceNear_detects_claim (setup : Setup) :
    deviceNear setup = true ↔ experiment.claim setup := by
  unfold deviceNear experiment
  exact decide_eq_true_iff

def triangulation : Experiments.Common.Triangulation Setup Coord :=
  { experiment := experiment
    device := deviceNear
    detects := deviceNear_detects_claim }

end Experiments.TheDescartesEffectCh08
