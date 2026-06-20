import Experiments.Common

/-!
# The Excel Effect — a dependency graph whose total recalculates on every addend

The instrument's *Excel effect* (`instrument/chapters/11.tex:293`, `phenomenon`):
the Universe Tensor is not a collection of independent variables but a *directed
acyclic graph of functional dependencies*. A change in any distinguishable event
(a "cell") forces an immediate, globally consistent update of all dependent
events. Apparent nonlocality is not a signal — it is a dependency
**recalculation**: "the ledger updates the total the instant an addend changes."

We model this finitely. A `Cell` is a distinguishable event with a recorded
value. The *dependents of a cell* form a finite `Ledger` of cells, and the
recalculated **total** of a region is `Ledger.count` of the addends that feed it
(the number of live addends — the "cells" the formula sums over). The Excel
content is the **additivity of recalculation**: appending a block of dependent
addends updates the total by exactly the block's own count, with no latency and
no cross-term — the spreadsheet identity `=SUM(A)+SUM(B) = SUM(A;B)`.

## Coupling
HARNESS, not device. The Excel effect is pure **bookkeeping / additivity** — the
ledger total updates by exactly what its addends contribute. There is no
holonomy, gauge loop-phase, curvature, Berry phase, or charge here, so a device
coupling would be FAKE. The load-bearing conjunct `recalc_is_additive` is
discharged by `Experiments.Common.Ledger.count_append`: the recalculated total
of two appended dependency blocks is the sum of their totals. A rename or
regression of that harness lemma breaks *this* build.

## NOT claimed
That this *derives* nonlocality, entanglement, Bell correlations, or
faster-than-light coordination; that real physics is a spreadsheet; that
"latency is zero" is a physical theorem rather than the instrument's *stipulation*
(here it is just the definitional fact that `count` of an append is a finite sum,
computed in one step). No continuum field, no causal cone, no metric. A `Cell`'s
`value` is an abstract `Nat` slot, not a physical observable. We do not enforce
acyclicity of the dependency graph — "DAG" is the instrument's framing; the
finite model only tracks the *addends a total sums over*.
**Claim ceiling:** a finite ledger model of dependency recalculation as additive
bookkeeping.
-/

namespace Experiments.TheExcelEffect

/-- A spreadsheet *cell*: a distinguishable event carrying an address slot and a
recorded value. Two cells are distinct iff some field differs. -/
structure Cell where
  addr : Nat
  value : Nat
deriving DecidableEq, Repr

/-- A *dependency block*: the finite ledger of addend cells that feed one total.
The recalculated total sums over exactly these addends. -/
abbrev Block := Experiments.Common.Ledger Cell

/-- The recalculated **total** of a block: the number of live addends the formula
sums over (`Ledger.count`). This is the "ledger's total" of the Excel statement. -/
def total (b : Block) : Nat :=
  b.count

/-- The global update operation: combining two dependency blocks (e.g. when a
sub-region's addends start feeding a parent total) is ledger append. -/
def combine (left right : Block) : Block :=
  Experiments.Common.Ledger.append left right

/-- A block *contributes* a given amount to a total when its recalculated total is
exactly that amount. The Excel claim is that contributions add with no cross-term. -/
def contributes (b : Block) (amount : Nat) : Prop :=
  total b = amount

instance (b : Block) (amount : Nat) : Decidable (contributes b amount) := by
  unfold contributes total
  exact inferInstance

-- ---------------------------------------------------------------------------
-- FALSIFIABLE lemmas. Each ∀-quantified; drop a hypothesis and it breaks.
-- ---------------------------------------------------------------------------

/-- RECALCULATION IS ADDITIVE (load-bearing, harness-coupled): the total of the
combined block is the sum of the two blocks' totals — the spreadsheet identity
`SUM(A;B) = SUM(A)+SUM(B)`. Discharged by the harness lemma `Ledger.count_append`;
break or rename that lemma and this fails. Quantified over ALL blocks. -/
theorem recalc_is_additive (left right : Block) :
    total (combine left right) = total left + total right :=
  Experiments.Common.Ledger.count_append left right

/-- AN ADDEND THAT CHANGES THE COUNT CHANGES THE TOTAL (falsifiable): if a block
contributes a *positive* amount, combining it onto a base strictly increases the
recalculated total. Drop the `0 < amount` hypothesis and the strict inequality is
false (an empty block leaves the total fixed) — so the hypothesis is load-bearing. -/
theorem live_addend_moves_total
    (base added : Block) (amount : Nat)
    (hcontrib : contributes added amount) (hpos : 0 < amount) :
    total base < total (combine base added) := by
  have h := recalc_is_additive base added
  unfold contributes at hcontrib
  omega

/-- AN ADDEND THAT IS NOT A DEPENDENT (empty contribution) leaves the total fixed:
combining a block that contributes `0` does not change the recalculated total. This
pins that the update tracks *only* the live addends, nothing spurious. -/
theorem inert_addend_fixes_total
    (base added : Block)
    (hcontrib : contributes added 0) :
    total (combine base added) = total base := by
  have h := recalc_is_additive base added
  unfold contributes at hcontrib
  omega

-- ---------------------------------------------------------------------------
-- A concrete dependency graph: a parent total fed by two sub-region blocks.
-- ---------------------------------------------------------------------------

/-- Sub-region A: two addend cells feeding the parent total. -/
def regionA : Block :=
  { events := [⟨0, 7⟩, ⟨1, 5⟩] }

/-- Sub-region B: three addend cells feeding the parent total. -/
def regionB : Block :=
  { events := [⟨2, 3⟩, ⟨3, 9⟩, ⟨4, 2⟩] }

theorem regionA_contributes : contributes regionA 2 := by decide
theorem regionB_contributes : contributes regionB 3 := by decide

/-- The parent total recalculates to the sum of the sub-region totals: `2 + 3 = 5`,
the instant the regions are combined — globally consistent, in one step. -/
theorem parent_total_recalculates :
    total (combine regionA regionB) = 5 := by decide

/-- A live sub-region strictly moves the parent total (regionB has positive count). -/
theorem regionB_moves_total :
    total regionA < total (combine regionA regionB) :=
  live_addend_moves_total regionA regionB 3 regionB_contributes (by decide)

-- ---------------------------------------------------------------------------
-- THE CLAIM (content-bearing conjunction; one conjunct is the harness theorem).
-- ---------------------------------------------------------------------------

/-- The claim, in honest parts:
* (additive recalculation / harness-coupled) the parent total of the two
  combined sub-regions is the sum of their totals (`Ledger.count_append`, via
  `recalc_is_additive`) — `SUM(A;B) = SUM(A)+SUM(B)`;
* (a live addend moves the total) combining the live region B strictly increases
  the parent total — the recalculation actually fires when an addend is added; and
* (the recalculated total is exactly the dependency sum) it equals `5`, the count
  of all live addends — no cross-term, no latency. -/
def claimStatement : Prop :=
  total (combine regionA regionB) = total regionA + total regionB ∧
    total regionA < total (combine regionA regionB) ∧
    total (combine regionA regionB) = 5

def claim : Experiments.Common.Claim :=
  { tag := Experiments.Common.ClaimTag.finiteLedgerModel
    statement := claimStatement }

theorem claim_holds : claim.statement :=
  ⟨recalc_is_additive regionA regionB,
    regionB_moves_total,
    parent_total_recalculates⟩

/-- The tag is an honest ceiling: a finite ledger model of additive dependency
recalculation, nothing more. -/
theorem ceiling : claim.tag = Experiments.Common.ClaimTag.finiteLedgerModel := rfl

-- ---------------------------------------------------------------------------
-- A computable run + a NON-vacuous Experiment.claim, with a proved bridge.
-- ---------------------------------------------------------------------------

structure Setup where
  base : Block
  added : Block
  expected : Nat

/-- The run computes — thanks to the `Decidable` instance above: does combining
`added` onto `base` recalculate to the `expected` total? -/
def run (s : Setup) : Bool := decide (contributes (combine s.base s.added) s.expected)

def experiment : Experiments.Common.Experiment Setup Bool :=
  { tag := claim.tag
    run := run
    claim := fun s => contributes (combine s.base s.added) s.expected }

theorem run_iff_claim (s : Setup) :
    run s = true ↔ experiment.claim s := by
  simp only [run, experiment, decide_eq_true_iff]

def canonicalSetup : Setup := { base := regionA, added := regionB, expected := 5 }

/-- Bring a minimal device next to this experiment: it records whether the
exported claim fires. -/
def deviceNear (setup : Setup) : Bool :=
  decide (contributes (combine setup.base setup.added) setup.expected)

theorem deviceNear_detects_claim (setup : Setup) :
    deviceNear setup = true ↔ experiment.claim setup := by
  simp only [deviceNear, experiment, decide_eq_true_iff]

def triangulation : Experiments.Common.Triangulation Setup Bool :=
  { experiment := experiment
    device := deviceNear
    detects := deviceNear_detects_claim }

#eval run canonicalSetup                                   -- expect: true
#print axioms claim_holds                                  -- ambient [propext, Quot.sound], not coupling
-- A config where the claim predicate is FALSE: combining the same regions does
-- NOT recalculate to 4 (it is 5). Proves the predicate is load-bearing, not
-- vacuous — the run can read false.
#eval run { canonicalSetup with expected := 4 }            -- expect: false

end Experiments.TheExcelEffect
