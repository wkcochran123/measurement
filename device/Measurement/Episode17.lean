import Measurement.Episode16
import Measurement.NamingClose
import Measurement.Funge

set_option maxHeartbeats 4000000
set_option maxRecDepth 1000
set_option allowUnsafeReducibility true

namespace Measurement

/-
__EPISODE 17__: _The Stationary Reader_

Episode16 made the middle point admissible: the direct reading `a -> c`
can be compared with the composed reading `a -> b -> c`.

This episode names two constraints, and they are not the same.

`stationaryAt` says the chosen slip is a minimum of the composed action.
`flatAt` says the composed action cannot detect the slip coordinate at all.
Thus:

* `reducibleSlip = admits ∧ minimum-stationary`
* `closedFlatAt  = admits ∧ gauge-flat`

The final residue theorem intentionally uses the stronger `closedFlatAt`.
-/

structure FiniteGaugePath where
  source : Bullshit
  slip : Bullshit
  target : Bullshit

namespace FiniteGaugePath

def withSlip (path : FiniteGaugePath) (slip : Bullshit) : FiniteGaugePath :=
  { path with slip := slip }

end FiniteGaugePath

structure FiniteGaugeAction where
  segmentCost : Bullshit -> Bullshit -> Nat

namespace FiniteGaugeAction

def direct (action : FiniteGaugeAction) (path : FiniteGaugePath) : Nat :=
  action.segmentCost path.source path.target

def composed (action : FiniteGaugeAction) (path : FiniteGaugePath) : Nat :=
  action.segmentCost path.source path.slip +
    action.segmentCost path.slip path.target

def admits (action : FiniteGaugeAction) (path : FiniteGaugePath) : Prop :=
  action.direct path = action.composed path

def stationaryAt (action : FiniteGaugeAction) (path : FiniteGaugePath) : Prop :=
  forall slip' : Bullshit,
    action.composed path <= action.composed (path.withSlip slip')

def flatAt (action : FiniteGaugeAction) (path : FiniteGaugePath) : Prop :=
  forall slip' : Bullshit,
    action.composed (path.withSlip slip') = action.composed path

def closedFlatAt (action : FiniteGaugeAction) (path : FiniteGaugePath) : Prop :=
  action.admits path /\ action.flatAt path

def reducibleSlip (action : FiniteGaugeAction) (path : FiniteGaugePath) : Prop :=
  action.admits path /\ action.stationaryAt path

theorem flatAt_stationaryAt
    {action : FiniteGaugeAction} {path : FiniteGaugePath}
    (h : action.flatAt path) :
    action.stationaryAt path := by
  intro slip'
  rw [h slip']
  exact Nat.le_refl _

theorem closedFlatAt_admits
    {action : FiniteGaugeAction} {path : FiniteGaugePath}
    (h : action.closedFlatAt path) :
    action.admits path :=
  h.left

theorem closedFlatAt_flatAt
    {action : FiniteGaugeAction} {path : FiniteGaugePath}
    (h : action.closedFlatAt path) :
    action.flatAt path :=
  h.right

theorem closedFlatAt_reducibleSlip
    {action : FiniteGaugeAction} {path : FiniteGaugePath}
    (h : action.closedFlatAt path) :
    action.reducibleSlip path :=
  ⟨h.left, action.flatAt_stationaryAt h.right⟩

theorem reducibleSlip_admits
    {action : FiniteGaugeAction} {path : FiniteGaugePath}
    (h : action.reducibleSlip path) :
    action.admits path :=
  h.left

theorem reducibleSlip_stationary
    {action : FiniteGaugeAction} {path : FiniteGaugePath}
    (h : action.reducibleSlip path) :
    action.stationaryAt path :=
  h.right

end FiniteGaugeAction

-- ===========================================================================
-- THE DOUBLE-READ WIRING (ep17-loop Phase 2).
--
-- Ep17 is the seam -- the stationary reader that asks whether the composed reading
-- can tell the slip apart from the direct one. This section CONNECTS that reader to
-- the naming close (NamingClose) and to the funge/tange partition (Funge), where the
-- forward walk of Episodes 17->52 meets the Meanwhile loop's pigeonhole. ADDITIVE:
-- the six predicates above (their signatures AND theorem statements) are untouched;
-- Episodes 18-40 build against them unchanged. Nothing here is imported by them.
--
-- The double-read map (interpretive, made precise where it is provable):
--   * `stationaryAt` (composed action minimized -- the first variation vanishes)
--       <-> `delta1_vanished` (the spent first variation, box 0).
--   * `admits` (direct = composed -- the seam holds, no residue read)
--       <-> the value box (box 0), and its shape is the funge/crank partition.
--   * `flatAt` (composed cannot detect the slip -- gauge-flat)
--       <-> the all-funge / label line (no crank, no tange).
--   * the reader's tower closes because the box count is finite
--       <-> `naming_tower_wraps` / `boxOf`: the tower cannot be a line, so the walk
--          closes into the loop.
-- ===========================================================================

/-- The finite representation of a gauge reading: an admitting reading (direct =
composed -- the seam holds, no residue) lands in the value box (0, where the vanished
first variation sits); a non-admitting one lands in the electron / second-variation
box (1). This boxes Ep17's reader into NamingClose's finite count -- the point where
the reader's walk meets the pigeonhole. -/
def readingBox (action : FiniteGaugeAction) (path : FiniteGaugePath) : Fin boxCount :=
  if action.direct path = action.composed path then valueBox else electronBox

/-- WIRE 1+3 -- admits reads the value box. An admitting reading (the seam holds,
direct = composed) is the value / 0th term (box 0), where `delta1_vanished` sits. The
stationary, seam-holding reader IS the vanished first variation's class. -/
theorem admits_reads_value_box
    {action : FiniteGaugeAction} {path : FiniteGaugePath} (h : action.admits path) :
    readingBox action path = valueBox := by
  unfold readingBox
  exact if_pos h

/-- WIRE 1 (naming side) -- the vanished first variation sits in that same value box.
So Ep17's admitting/stationary reader and NamingClose's `delta1_vanished` name one
class (box 0). -/
theorem vanished_delta1_in_value_box (g : Gospel) (p : Prop) :
    boxOf (delta1_vanished g p) = valueBox :=
  (fixed_point_pins_zeroth g p).left

/-- WIRE 1 (flat side) -- a closed-flat reading (admits + flat) reads the value box:
the flat, seam-holding reader is the vanished first variation's class. -/
theorem closedFlat_reads_value_box
    {action : FiniteGaugeAction} {path : FiniteGaugePath} (h : action.closedFlatAt path) :
    readingBox action path = valueBox :=
  admits_reads_value_box h.left

/-- WIRE 4 -- the reader's tower closes because the box count is finite. Any
Nat-indexed walk of gauge readings, boxed by the finite representation, MUST wrap:
two distinct steps share a box (`naming_tower_wraps`). The reader's forward walk
cannot be a line -- it closes into the loop. -/
theorem reader_tower_closes (action : FiniteGaugeAction) (walk : Nat → FiniteGaugePath) :
    ∃ i j : Nat, i ≠ j ∧ readingBox action (walk i) = readingBox action (walk j) :=
  naming_tower_wraps (fun n => readingBox action (walk n))

/-- WIRE 2 -- flatAt <-> the all-funge / label line. A tape with no cranks (no tange,
the gauge-flat reading that cannot detect a slip) reads every fact as a funge: the
count is the whole length. -/
theorem flat_reading_all_funge (tape : List Fact) (h : crankTurns tape = 0) :
    countFunges tape = tape.length := by
  have hp := funges_and_cranks_partition tape
  omega

/-- WIRE 3 -- admits's shape IS the funge/crank partition. `admits` is direct =
composed (whole = sum of parts); the funge/crank partition is length = funges + cranks
(the whole tape counted once, as funges through the slip plus cranks). Same
conservation, read on the tape. -/
theorem admits_shape_is_partition (tape : List Fact) :
    tape.length = countFunges tape + crankTurns tape :=
  (funges_and_cranks_partition tape).symm

end Measurement
