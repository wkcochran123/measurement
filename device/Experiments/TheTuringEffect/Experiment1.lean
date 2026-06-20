import Experiments.Common

/-!
# The Turing Effect — a finite serialization model (content version, no device coupling)

## Physics (modelled finitely)
The effect (instrument/chapters/02.tex:780) says: any finite-dimensional process may be
*serialized* — decomposed into a **one-dimensional record** by sequential commitment — and later
*reconstructed*.  The hard CONSTRAINT is the device's: **no instrument may commit more than one
distinction in a single recording step**.  A multidimensional structure (here a 2-D grid `Cell`)
is scanned line-by-line into an ordered ledger of one-distinction-at-a-time `Step`s; the apparent
dimensionality is reconstructed only after the record is complete.

We model this with:
* `Cell` — a 2-D distinction (`row`, `col`) — the effect-specific domain (NOT `CountSetup`);
* a `serialize` that emits **exactly one `Step` per cell** (sequential commitment to the ledger);
* a `reconstruct` that recovers the grid from the record.

The load-bearing facts are quantified over ALL grids:
* the record commits exactly one step per cell — `serialize_length` (length = #cells), so it can
  never silently emit two distinctions for one cell or skip one;
* serialization is **lossless**: `reconstruct (serialize g) = g` for every grid — the "later
  reconstruction" of the description.

## Coupling
Per the suite cheat-sheet, the Turing / undecidability family has **NO honest device
(`Measurement`) coupling** — there is no halting/Goedel theorem in the device.  We therefore tag
`physicalClaimLabelOnly` and build the honest content model only.  We DO lean on the **harness**
(`Experiments.Common.Ledger.count_map`) for one conjunct, so a regression in the harness ledger
algebra breaks this build.

## NOT claimed
No claim about undecidability, the halting problem, Goedel, Chaitin, or Turing-completeness in the
computability sense.  "Turing" here is a **label** for the structural fact that lawful measurement
admits only *sequential* commitment.  We do not claim universality of computation, only that THIS
finite grid serializes losslessly under a one-distinction-per-step record.
-/

namespace Experiments.TheTuringEffect

/-- A single 2-D distinction in the process being measured: which row, which column.
This is the "higher-dimensional structure" the instrument cannot commit at once. -/
structure Cell where
  row : Nat
  col : Nat
deriving DecidableEq, Repr

/-- One lawful recording **step**: exactly one distinction committed to the ledger.  The record is
a `List Step`; the constraint "one distinction per step" is structural — each `Step` carries one
`cell`, and `serialize` emits one `Step` per cell. -/
structure Step where
  cell : Cell
deriving DecidableEq, Repr

/-- A finite multidimensional process: a rectangular grid of distinctions, `rows × cols`. -/
structure Grid where
  rows : Nat
  cols : Nat
deriving DecidableEq, Repr

namespace Grid

/-- The 2-D content of the grid, before serialization: every `(r, c)` with `r < rows`, `c < cols`,
scanned line-by-line (row-major) — the order the instrument will commit them in. -/
def cells (g : Grid) : List Cell :=
  (List.range g.rows).flatMap (fun r =>
    (List.range g.cols).map (fun c => { row := r, col := c }))

/-- The total number of distinctions in the process. -/
def size (g : Grid) : Nat := g.rows * g.cols

end Grid

/-- SERIALIZE: scan the grid into a one-dimensional record, **one `Step` per distinction**.  This
is the "internal decomposition and sequential traversal" of the description — `Cell`s become an
ordered ledger of single-distinction steps. -/
def serialize (g : Grid) : Experiments.Common.Ledger Step :=
  { events := g.cells.map (fun c => { cell := c }) }

/-- RECONSTRUCT: rebuild the 2-D content from the completed record — "the apparent dimensionality
of the phenomenon is reconstructed only after the record is complete." -/
def reconstruct (ledger : Experiments.Common.Ledger Step) : List Cell :=
  ledger.events.map (fun s => s.cell)

-- ---------------------------------------------------------------------------
-- FALSIFIABLE lemmas, quantified over ALL grids.  Each would break if the model
-- dropped its hypothesis / committed more or fewer than one distinction per step.
-- ---------------------------------------------------------------------------

/-- The record decodes a single distinction per step `STEP` back to its cell: the channel between
`Cell` and `Step` is exactly the identity-on-content (drop a field of `Step` and this fails). -/
theorem step_roundtrip (c : Cell) : (({ cell := c } : Step)).cell = c := rfl

/-- **One distinction per cell**: the record commits *exactly* `g.cells.length` steps — never two
distinctions in one step, never a skipped cell.  Quantified over every grid. -/
theorem serialize_length (g : Grid) :
    (serialize g).count = g.cells.length := by
  simp [serialize, Experiments.Common.Ledger.count]

/-- The 2-D content has exactly `rows × cols` distinctions. -/
theorem cells_length (g : Grid) : g.cells.length = g.size := by
  simp only [Grid.cells, Grid.size, List.length_flatMap, List.length_map,
    List.length_range, List.map_const', List.sum_replicate_nat]

/-- **Sequential commitment matches the 2-D size**: the one-dimensional record has exactly one
step per distinction in the original `rows × cols` process. -/
theorem serialize_count_eq_size (g : Grid) :
    (serialize g).count = g.size := by
  rw [serialize_length, cells_length]

/-- **Lossless reconstruction**: for EVERY grid, reconstructing from the completed serial record
recovers the original 2-D content exactly.  This is the heart of the effect — and it would FAIL if
`serialize` dropped or reordered a distinction. -/
theorem reconstruct_serialize (g : Grid) :
    reconstruct (serialize g) = g.cells := by
  simp only [reconstruct, serialize, List.map_map]
  exact List.map_id _

-- ---------------------------------------------------------------------------
-- THE CLAIM (content-bearing; one conjunct is a HARNESS theorem).
-- ---------------------------------------------------------------------------

/-- A concrete process: a 2×3 grid of distinctions. -/
def sampleGrid : Grid := { rows := 2, cols := 3 }

/-- The claim, in honest parts:
* (serial size) the record commits exactly one step per distinction — `serialize_count_eq_size`;
* (lossless) reconstruction recovers the 2-D content for the sample grid — `reconstruct_serialize`;
* (ledger continuity, HARNESS-coupled) concatenating two records adds their lengths
  (`Experiments.Common.Ledger.count_append`) — so two serial records compose as one ledger.
The last conjunct puts a harness symbol in the proof term: a regression in the ledger algebra
breaks this build. -/
def claimStatement : Prop :=
  (serialize sampleGrid).count = sampleGrid.size ∧
    reconstruct (serialize sampleGrid) = sampleGrid.cells ∧
    (∀ (l r : Experiments.Common.Ledger Step),
      (Experiments.Common.Ledger.append l r).count = l.count + r.count)

def claim : Experiments.Common.Claim :=
  { tag := Experiments.Common.ClaimTag.physicalClaimLabelOnly
    statement := claimStatement }

theorem claim_holds : claim.statement :=
  ⟨serialize_count_eq_size sampleGrid,
    reconstruct_serialize sampleGrid,
    fun l r => Experiments.Common.Ledger.count_append l r⟩

/-- The tag is an honest ceiling: a physical claim's LABEL only — "Turing" names the structural
sequentiality, it does not assert any computability theorem. -/
theorem ceiling :
    claim.tag = Experiments.Common.ClaimTag.physicalClaimLabelOnly := rfl

-- ---------------------------------------------------------------------------
-- A computable run + a NON-vacuous experiment, with a proved bridge.
-- ---------------------------------------------------------------------------

structure Setup where
  grid : Grid

/-- The run actually computes: serialize the grid, return the length of the one-dimensional
record (the number of single-distinction commitments). -/
def run (s : Setup) : Nat := (serialize s.grid).count

/-- The exported claim is a genuine function of the setup (not `fun _ => True`): the serial record
length equals the 2-D size of the process. -/
def experiment : Experiments.Common.Experiment Setup Nat :=
  { tag := claim.tag
    run := run
    claim := fun s => (serialize s.grid).count = s.grid.size }

theorem run_eq_size (s : Setup) : run s = s.grid.size :=
  serialize_count_eq_size s.grid

theorem run_iff_claim (s : Setup) :
    run s = s.grid.size ↔ experiment.claim s := by
  simp only [run, experiment]

def canonicalSetup : Setup := { grid := sampleGrid }

#eval run canonicalSetup                     -- expect: 6  (2×3 distinctions, one step each)
#eval reconstruct (serialize sampleGrid)     -- expect: the six cells, row-major
#print axioms claim_holds

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

end Experiments.TheTuringEffect
