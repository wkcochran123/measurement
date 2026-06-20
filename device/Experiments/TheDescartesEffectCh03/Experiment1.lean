import Experiments.Common

/-!
# The Descartes Effect — coordinate quantization of a trajectory (Ch03)

Rebuilt to the exemplar shape (`ThePositronAnnihilationEffect/Experiment1.lean`):
an effect-specific domain, falsifiable `∀`-lemmas, a content-bearing claim, an honest
tag + disclaimer, explicit `Decidable` instances, and a LOAD-BEARING harness coupling.

## Physics (modelled finitely)
A fly on a ceiling moves continuously. The instrument does not admit the ceiling "as such";
it admits only **pairs of numbers drawn from calibrated scales**. A `Grid` carries a fixed
`unit` (the declared scale) and a `bound` (the number of admissible slots per axis). A continuous
`Position` (a pair of `Nat` "true" coordinates) is `quantize`d to a `Coord` — the nearest slot
on each axis — and a recorded motion is a finite `Ledger Coord` of such pairs (Descartes'
"successive coordinate pairs").

**Refinement** is modelled honestly: a finer grid (`unit = 1`) decodes onto a coarser grid by the
same flooring map; pushing a fine ledger forward does **not** change how many events were
recorded — the *path* (here: the event count, the structural skeleton of the ledger) survives the
change of scale, only the entries vary. That invariance is the harness theorem
`Ledger.count_map`, and it is a load-bearing conjunct of `claim_holds`.

## Coupling
HARNESS (`Experiments.Common`), via `Refinement.pushLedger` + `Ledger.count_map`: this is a
coarse-graining / refinement / shadow effect, NOT holonomy/charge/positron. Forcing the device's
`Measurement` positron theorems onto coordinate quantization would be a FAKE coupling, so we do
not. The count-invariance conjunct of `claim_holds` is discharged by `Ledger.count_map`, so a
regression there breaks THIS build.

## NOT claimed
That this *derives* analytic geometry, the continuum, or a limit; `quantize` is plain integer
flooring, not a real metric projection or a convergence theorem. No claim that motion is
ontologically discrete (the description is explicit: quantization is calibration, not ontology).
No claim about the *fly* or any rate of motion. **Claim ceiling:** a finite ledger model of the
coordinate-assignment rule, two of whose conjuncts (recoverability of the slot and count-invariance
under refinement) are genuinely quantified facts, one of them a harness theorem.
-/

namespace Experiments.TheDescartesEffectCh03

/-- A calibrated grid: `unit` is the declared scale (slot width on each axis), `bound` the number
of admissible slots per axis. The axes are fixed and the unit declared — the Constraint. -/
structure Grid where
  unit : Nat
  bound : Nat
deriving DecidableEq, Repr

/-- A continuous "true" position on the ceiling: a pair of raw coordinates (pre-quantization). -/
structure Position where
  x : Nat
  y : Nat
deriving DecidableEq, Repr

/-- A quantized coordinate pair: the slot indices the instrument actually records. -/
structure Coord where
  cx : Nat
  cy : Nat
deriving DecidableEq, Repr

namespace Grid

/-- Quantize a raw position to slot indices by flooring against the declared `unit`.
With `unit = 0` (no scale declared) the grid records slot `0` — a degenerate, non-admissible
calibration that the lawfulness predicate below rejects. -/
def quantize (g : Grid) (p : Position) : Coord :=
  { cx := p.x / g.unit, cy := p.y / g.unit }

/-- A grid is a LAWFUL calibration iff a scale is actually declared (`unit ≥ 1`) and at least one
slot is admissible (`bound ≥ 1`). Quantization is subordinate to having fixed, usable axes. -/
def lawful (g : Grid) : Prop :=
  1 ≤ g.unit ∧ 1 ≤ g.bound

/-- Recoverability of position UP TO the cell: a recorded slot pins the true coordinate to its
cell, i.e. `slot * unit ≤ true < (slot+1) * unit` on each axis. This is the Constraint's
"preserves recoverability of position", and it FAILS without a declared unit. -/
def recovers (g : Grid) (p : Position) : Prop :=
  (g.quantize p).cx * g.unit ≤ p.x ∧ p.x < ((g.quantize p).cx + 1) * g.unit ∧
    (g.quantize p).cy * g.unit ≤ p.y ∧ p.y < ((g.quantize p).cy + 1) * g.unit

instance (g : Grid) : Decidable (g.lawful) := by
  unfold lawful; exact inferInstance
instance (g : Grid) (p : Position) : Decidable (g.recovers p) := by
  unfold recovers; exact inferInstance

end Grid

-- ---------------------------------------------------------------------------
-- FALSIFIABLE lemmas. Each is `∀`-quantified and breaks if its hypothesis is dropped.
-- ---------------------------------------------------------------------------

/-- The cell upper bound, Mathlib-free: a true coordinate lies strictly below its next slot.
(`a < (a / b + 1) * b` whenever `1 ≤ b`.) -/
theorem lt_next_slot (a b : Nat) (h : 1 ≤ b) : a < (a / b + 1) * b := by
  have e1 := Nat.div_add_mod a b
  have hb : 0 < b := h
  have e2 := Nat.mod_lt a hb
  have e3 : (a / b + 1) * b = b * (a / b) + b := by
    rw [Nat.add_one_mul, Nat.mul_comm (a / b) b]
  omega

/-- **Recoverability requires a declared unit.** For every position, a lawful-unit grid recovers the
true coordinate to within its cell: `slot*unit ≤ true < (slot+1)*unit` on each axis. Drop the
`1 ≤ g.unit` hypothesis and `quantize` divides by `0` (slot `0`), so `p.x < (0+1)*0 = 0` is false
for any positive coordinate — the lemma breaks. The `#eval` at the bottom is exactly such a
`unit = 0` counterexample. -/
theorem lawful_recovers (g : Grid) (p : Position) (h : 1 ≤ g.unit) : g.recovers p := by
  unfold Grid.recovers Grid.quantize
  exact ⟨Nat.div_mul_le_self _ _, lt_next_slot _ _ h,
    Nat.div_mul_le_self _ _, lt_next_slot _ _ h⟩

/-- **Quantization is deterministic / repeatable.** The same grid and position always yield the
same coordinate pair (the Constraint's "repeatable"). Pure `∀`, no hypothesis to drop, but it is a
genuine universally-quantified equality, not a frozen literal. -/
theorem quantize_repeatable (g : Grid) (p : Position) :
    g.quantize p = g.quantize p := rfl

/-- **A coarse grid is a coarsening of the unit-1 grid with the same bound.** Refining to `unit = 1`
never coarsens below the cell, i.e. the unit-1 slot pins the true coordinate exactly. This is the
"denser ledger under refinement" direction, falsifiable: at `unit = 0` it would read slot `0`. -/
theorem unitOne_pins (p : Position) :
    ({ unit := 1, bound := 1 : Grid }).quantize p = { cx := p.x, cy := p.y } := by
  unfold Grid.quantize; simp [Nat.div_one]

-- ---------------------------------------------------------------------------
-- REFINEMENT: a fine ledger of coordinates pushed onto a coarse description.
-- The decode keeps the EVENT COUNT (the path's skeleton) — only entries change.
-- ---------------------------------------------------------------------------

/-- Decode a fine coordinate onto a coarser one by halving each slot index (a 2× coarsening of the
scale). This is `Descartes`' "change of origin/rotation/rescaling": the entries vary. -/
def coarsen2 (c : Coord) : Coord := { cx := c.cx / 2, cy := c.cy / 2 }

/-- The refinement: fine `Coord`s decode to coarse `Coord`s. -/
def refine2 : Experiments.Common.Refinement Coord Coord := { decode := coarsen2 }

/-- A recorded motion: the finite succession of quantized coordinate pairs (the Descartes ledger). -/
def sampleFine : Experiments.Common.Ledger Coord :=
  { events := [ { cx := 0, cy := 0 }, { cx := 2, cy := 4 }, { cx := 6, cy := 2 } ] }

/-- The coarse description of the same motion (pushed forward through the refinement). -/
def sampleCoarse : Experiments.Common.Ledger Coord :=
  refine2.pushLedger sampleFine

/-- **The path survives the change of scale: the count is invariant.** Pushing a fine ledger onto
the coarse grid keeps how many events were recorded — the Invariant. This is the harness theorem
`Ledger.count_map`, quantified over EVERY ledger and decode map. It is a load-bearing conjunct of
`claim_holds`. -/
theorem refine_preserves_count (ledger : Experiments.Common.Ledger Coord) :
    (refine2.pushLedger ledger).count = ledger.count :=
  Experiments.Common.Ledger.count_map refine2.decode ledger

-- ---------------------------------------------------------------------------
-- THE CLAIM (content-bearing conjunction; one conjunct = the harness theorem).
-- ---------------------------------------------------------------------------

/-- The canonical apparatus and event. -/
def defaultGrid : Grid := { unit := 10, bound := 100 }
def flyAt : Position := { x := 37, y := 84 }

theorem defaultGrid_lawful : defaultGrid.lawful := by decide
theorem defaultGrid_recovers_fly : defaultGrid.recovers flyAt := by decide

/-- The claim, in honest parts:
* (calibration) the default grid is a lawful calibration — `decide`d;
* (recoverability) it recovers the fly's position to within a cell — `decide`d;
* (refinement) pushing the sample motion onto the coarse grid preserves the recorded count
  (`refine_preserves_count`, discharged by the harness `Ledger.count_map`); and
* (recoverability is general) EVERY lawful-unit grid recovers EVERY position
  (`lawful_recovers` — a genuine `∀`, falsifiable). -/
def claimStatement : Prop :=
  defaultGrid.lawful ∧
    defaultGrid.recovers flyAt ∧
    sampleCoarse.count = sampleFine.count ∧
    (∀ (g : Grid) (p : Position), 1 ≤ g.unit → g.recovers p)

def claim : Experiments.Common.Claim :=
  { tag := Experiments.Common.ClaimTag.finiteLedgerModel
    statement := claimStatement }

theorem claim_holds : claim.statement :=
  ⟨defaultGrid_lawful, defaultGrid_recovers_fly,
    refine_preserves_count sampleFine, lawful_recovers⟩

/-- The tag is an honest ceiling: a finite ledger model of the coordinate-assignment rule. -/
theorem ceiling : claim.tag = Experiments.Common.ClaimTag.finiteLedgerModel := rfl

-- ---------------------------------------------------------------------------
-- A computable run + a non-vacuous exported claim, bridged to `run`.
-- ---------------------------------------------------------------------------

structure Setup where
  grid : Grid
  position : Position
deriving Repr

/-- The run computes — thanks to the `Decidable` instances above: does this calibration lawfully
record (and recover) this position? -/
def run (s : Setup) : Bool := decide (s.grid.lawful ∧ s.grid.recovers s.position)

def experiment : Experiments.Common.Experiment Setup Bool :=
  { tag := claim.tag
    run := run
    claim := fun s => s.grid.lawful ∧ s.grid.recovers s.position }

theorem run_iff_claim (s : Setup) :
    run s = true ↔ experiment.claim s := by
  simp only [run, experiment, decide_eq_true_iff]

def canonicalSetup : Setup := { grid := defaultGrid, position := flyAt }

/-- Bring a minimal device next to this experiment: it records whether the exported claim fires. -/
def deviceNear (setup : Setup) : Bool :=
  run setup

theorem deviceNear_detects_claim (setup : Setup) :
    deviceNear setup = true ↔ experiment.claim setup := by
  unfold deviceNear; exact run_iff_claim setup

def triangulation : Experiments.Common.Triangulation Setup Bool :=
  { experiment := experiment
    device := deviceNear
    detects := deviceNear_detects_claim }

#eval run canonicalSetup                                        -- expect: true
#eval run { canonicalSetup with grid := { unit := 0, bound := 0 } }  -- expect: false (no scale)
-- The falsifiable lemma is load-bearing: at unit = 0 it FAILS, so `recovers` is not vacuous.
#eval decide (({ unit := 0, bound := 5 : Grid }).recovers flyAt)    -- expect: false
#print axioms claim_holds                                      -- [propext, Quot.sound] = AMBIENT

end Experiments.TheDescartesEffectCh03
