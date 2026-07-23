import Measurement.ArchimedesPi

/-! # Measurement.Gauge.ArchimedesPiDisplay — the readout layer for `ArchimedesPi` (Gauge phase, cluster 1).

The physics (the polygon squeeze, the proved-ordered walls, the measured π bracket, `22/7`) and ALL theorems
live in `Measurement.ArchimedesPi`; this module is a LEAF holding ONLY its `#eval` display, importing the
physics ONE-WAY (nothing under `Measurement/` imports `Gauge/`; nothing imports this module). This is the
`CalibrationManifest` reporting-leaf pattern generalized into a `Gauge/` directory — the presentation layer
pulled out of the episode (audit: numbers/display out of the episodes). -/

open Measurement Measurement.ArchimedesPi

-- ── the measured squeeze (read the bracket; NO π was input — only orbitRadius + floorSqrt) ──
#eval s!"[squeeze method — π MEASURED off the device's orbit (radius {orbitRadius}); NO π input, only floorSqrt]"
#eval s!"  scale = 1e9 ; hexagon seed a₀=2√3={a0}, b₀=3={b0}  (unit diameter)"
#eval String.intercalate "\n" ((List.range 8).map (fun n =>
  let a := piHi n; let b := piLo n
  s!"  depth {n} (2^{n}·hexagon = {6 * 2^n}-gon):  π ∈ [{b}, {a}] / 1e9  =  [{b}·1e-9 , {a}·1e-9]"))

-- The bracket AS A RATIONAL (walls over the scale): inscribed/S < π < circumscribed/S.
#eval s!"[π bracket, depth 6 ({6*2^6}-gon)]  {piLo 6}/1000000000 < π < {piHi 6}/1000000000  (measured, walls proved ordered)"

-- BLIND read LAST: where does 22/7 sit vs the measured bracket? (22/7 = 3.142857142…; ×1e9 = 3142857142)
#eval s!"[read LAST, blind] 22/7 ×1e9 = 3142857142 ; measured upper wall (depth 6) = {piHi 6} ; is π < 22/7 confirmed by the measurement? {decide (piHi 6 ≤ 3142857143)} (circumscribed wall ≤ 22/7 ⟹ measured π < 22/7)"
#eval "[honest] π is held as the measured OPEN BRACKET, never collapsed to a point; 22/7 is Archimedes' rational upper bound the squeeze CONFIRMS (π < 22/7), read after the fact — NOT aimed at, NOT fused with the count-3 fencepost. Depth is the resolution; 22/7 is where the upper wall lands."
