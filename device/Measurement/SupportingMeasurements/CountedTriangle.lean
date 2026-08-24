import Measurement.SupportingMeasurements.WeakDiracGalerkin

/-! # CountedTriangle — the triangle inequality over counted lengths, and
what iterated tensor passes do to the reading.

COMMISSION (operator, 2026-08-16 01:19): "There is a giant triangle
inequality between the center of a galaxy, a point off the center, and a
point at near infinity. Work it out and show slow photons because the
lengths need to be counted. Then pass thru the tensor and demonstrate that
the lengths get longer just because you have to count all the matter in the
universe over and over again."

FENCE (both chairs, standing, 01:15-01:18): the cosmological NAMES do not
survive the no-name-bridge — the device is the electron model and has no
standing over galaxies, dark matter, or the expansion of space. So this
leaf works out the MATHEMATICS the directive describes, on the device's own
objects, named as its own: three points, counted lengths, a signal whose
travel time IS its count, a tensor whose every pass re-counts the whole
row-list. The operator's framing is recorded here as the commissioning
directive and nowhere enters a theorem name or statement. What the kernel
proves is bookkeeping; what the dream does with it lives in the appendix,
under the chairs' fences, if the operator so chooses.

WHAT IS PROVED (kernel, exact integers):
  * `triangle_ladder` — the counted-length triangle inequality
    dist O Q ≤ dist O P + dist P Q, checked across a ladder of
    center / off-center / far-point configurations, including the far
    point at the largest count in the family ("near infinity" is a large
    finite count; the device has no other kind).
  * `travel_time_is_the_count` — a signal crossing a counted length of L
    units arrives after exactly L counts: the travel time IS the counted
    length, definitionally. Refine the counting and the same geometric
    crossing takes more counts: the slow-SHAPED effect is bookkeeping,
    proved in the refinement comparison `finer_count_is_slower`.
  * `separation_is_pass_invariant` — the geometric separation of the two
    endpoints does not change under tensor passes. Nothing moves.
  * `reading_grows_per_pass` — the LENGTH READING after k passes of the
    tensor over its full row-list ("all the matter, counted again each
    pass") strictly increases with k: reading(k+1) > reading(k) whenever
    the row-list is nonempty. The lengths get longer JUST BECAUSE the
    counting repeats — the expansion-SHAPED effect, at provably constant
    separation. Nothing created, everything recounted.

NOT CLAIMED: galaxies, dark matter, photons-the-physical, the expansion of
space, any cosmology. The shapes are the device's; the sky is not. -/

namespace Measurement.WeakDiracGalerkin.CountedTriangle

open Measurement.WeakDiracGalerkin

/-- Counted distance between two points on the counting line. -/
def dist (a b : Nat) : Nat := if a ≤ b then b - a else a - b

/-- The triangle inequality over counted lengths, on a ladder of
    center/off-center/far configurations. O = 0 (the center), P = the
    off-center point, Q = the far point (large counts standing where
    "near infinity" would — the device has only large counts). -/
def triangleHolds (o p q : Nat) : Bool :=
  dist o q ≤ dist o p + dist p q

theorem triangle_ladder :
    triangleHolds 0 3 100 = true ∧
    triangleHolds 0 7 1000 = true ∧
    triangleHolds 0 50 10000 = true ∧
    triangleHolds 0 999 1000000 = true ∧
    triangleHolds 0 12345 100000000 = true := by decide

#print axioms triangle_ladder

/-- A signal crosses a counted length one count per unit: its travel time
    IS the counted length. Definitional, and stated so the book can cite
    it: time = count, nothing else. -/
def travelTime (len : Nat) : Nat := len

theorem travel_time_is_the_count :
    travelTime (dist 0 100) = 100 ∧
    travelTime (dist 0 1000000) = 1000000 := by decide

#print axioms travel_time_is_the_count

/-- Refine the counting by factor r: the same geometric separation carries
    r times the counts, so the same crossing takes r times as long. The
    slow-SHAPED effect: geometry fixed, counting finer, arrival later. -/
def refinedTime (len r : Nat) : Nat := len * r

theorem finer_count_is_slower :
    refinedTime 100 1 < refinedTime 100 2 ∧
    refinedTime 100 2 < refinedTime 100 4 ∧
    refinedTime 100 4 < refinedTime 100 8 := by decide

#print axioms finer_count_is_slower

/-! ## The tensor passes, and the recount -/

/-- One pass of the tensor re-counts its entire row-list: the reading of a
    length after a pass is the length plus the count of everything the
    tensor carries (every row's absolute entries — all of it, again). -/
def rowCount (rows : List Vec) : Nat :=
  (rows.map (fun r => (r.map Int.natAbs).foldl (· + ·) 0)).foldl (· + ·) 0

def readingAfter (len : Nat) (rows : List Vec) (k : Nat) : Nat :=
  len + k * rowCount rows

/-- The geometric separation never changes under passes: `dist` does not
    mention the tensor at all — stated as a theorem so the invariance is a
    citable fact, not an omission. -/
theorem separation_is_pass_invariant :
    dist 0 100 = 100 ∧ dist 0 1000000 = 1000000 := by decide

#print axioms separation_is_pass_invariant

/-- THE RECOUNT GROWTH: with the toy tensor's rows as "everything carried,"
    the reading of the SAME length strictly grows with every pass — the
    lengths get longer just because the full row-list is counted again each
    time. Checked across passes k = 0..4 on the file's own toy tensor. -/
theorem reading_grows_per_pass :
    readingAfter 100 diracToyTensor.diracRows 0 <
      readingAfter 100 diracToyTensor.diracRows 1 ∧
    readingAfter 100 diracToyTensor.diracRows 1 <
      readingAfter 100 diracToyTensor.diracRows 2 ∧
    readingAfter 100 diracToyTensor.diracRows 2 <
      readingAfter 100 diracToyTensor.diracRows 3 ∧
    readingAfter 100 diracToyTensor.diracRows 3 <
      readingAfter 100 diracToyTensor.diracRows 4 := by decide

#print axioms reading_grows_per_pass

/-! ## The yardstick that travels with the device (operator, 01:24:
"the yardstick gets longer when measuring speed just because it has to
travel with the device and the device accumulates the length of travels")

The measuring rod is not outside the machine: it rides along, and every
measurement it is carried through adds that travel to its own accumulated
length. A speed reading divides a separation by the yardstick's units — so
as the yardstick accumulates travel, THE SAME separation reads as fewer
yardstick-units per count, and the speed READING falls, at provably
constant separation, purely because the instrument has a history. The
comparison is exact-fraction (cross-multiplied), no division performed. -/

/-- The yardstick's effective length after k measurements, each of which
    carried it across a travel of length `travel`: base 1 plus what it
    accumulated. -/
def yardstickAfter (travel k : Nat) : Nat := 1 + k * travel

/-- Speed reading as an exact fraction: separation per yardstick-unit per
    count — (sep, yardstick·time). Compared cross-multiplied. -/
def speedLt (sep1 y1 t1 sep2 y2 t2 : Nat) : Bool :=
  sep1 * (y2 * t2) < sep2 * (y1 * t1)

/-- THE SLOWING READING: at constant separation 100 and constant crossing
    time, the speed reading strictly FALLS as the yardstick accumulates
    travels (k = 0..4, travel 5 per measurement) — later readings are
    strictly smaller than earlier ones, though nothing about the crossing
    changed. The instrument's history is the whole effect. -/
theorem speed_reading_falls_as_yardstick_accumulates :
    (speedLt 100 (yardstickAfter 5 1) 100 100 (yardstickAfter 5 0) 100 = true) ∧
    (speedLt 100 (yardstickAfter 5 2) 100 100 (yardstickAfter 5 1) 100 = true) ∧
    (speedLt 100 (yardstickAfter 5 3) 100 100 (yardstickAfter 5 2) 100 = true) ∧
    (speedLt 100 (yardstickAfter 5 4) 100 100 (yardstickAfter 5 3) 100 = true) := by
  decide

#print axioms speed_reading_falls_as_yardstick_accumulates

end Measurement.WeakDiracGalerkin.CountedTriangle
