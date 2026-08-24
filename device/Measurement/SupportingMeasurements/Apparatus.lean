/-! # Measurement.Apparatus — the LIVE apparatus surface for the Experiments.

The Experiments drive the device EXPLICITLY through this one named surface. It re-derives, on a
clean minimal LIVE model, the positron / holonomy / matter–antimatter machinery the experiments
couple to (formerly the atticked Episode 82–85 gauge branch, pruned in the α-spine convergence).

The three-fold charge is **matter / antimatter / doesnt-matter** (= electron / positron / neutral =
the cycle-of-three's minus / plus / zero). `doesntMatter` is the neutral sign: WHICH sign counts as
"positron" is frame-relative — it doesn't matter (Episode 84's "detection is frame-relative").

Claim ceiling (inherited, unchanged): a positron is READ as the positive sign of a gauge holonomy a
pair accumulates around a loop — the both-legs commutator residue, zero on any open/single-leg path,
positive only over an asymmetric flux. MEASURED, not derived. Every theorem here is `decide` over the
concrete finite model, axiom-free. No real Aharonov–Bohm, SQUID, QED, or antimatter is claimed. -/

namespace Measurement

-- ── A node (one leg's slip / one tag-step of the cubic path) ──
structure GaugeNode where
  pos : Int
deriving DecidableEq, Repr

def node0 : GaugeNode := ⟨0⟩   -- the symmetric origin node
def node1 : GaugeNode := ⟨1⟩
def node2 : GaugeNode := ⟨2⟩

-- ── The gauge flux / baseline: a cubic path is its four nodes (source, both middles, target).
-- Symmetric (flat) when the right middle sits at the origin node0; asymmetric (tilted) otherwise. ──
structure CubicGaugePath0 where
  source      : GaugeNode
  middleLeft  : GaugeNode
  middleRight : GaugeNode
  target      : GaugeNode
deriving DecidableEq, Repr

def flatPath   : CubicGaugePath0 := ⟨node0, node0, node0, node0⟩   -- symmetric / native baseline
def tiltedPath : CubicGaugePath0 := ⟨node0, node0, node1, node1⟩   -- asymmetric flux

structure CubicGaugeVariation0 where
  left  : GaugeNode
  right : GaugeNode
deriving DecidableEq, Repr

namespace CubicGaugeVariation
/-- The pair variation over two legs. `pairVariation node1 node2` moves both legs (the loop /
commutator); `pairVariation node2 node1` holds the right leg at `node1` (the open path). -/
def pairVariation (sL sR : GaugeNode) : CubicGaugeVariation0 := ⟨sL, sR⟩
end CubicGaugeVariation
open CubicGaugeVariation

-- ── The three-fold charge: the doesn't-matter three-fold ──
/-- matter (electron) / antimatter (positron) / doesnt-matter (the frame-relative neutral). -/
inductive Charge
  | matter
  | antimatter
  | doesntMatter
deriving DecidableEq, Repr

/-- The sign of a residue as a charge. Zero maps to `doesntMatter` — the neutral whose which-is-which
is a convention, not an absolute. -/
def orientationOfSign (x : Int) : Charge :=
  if 0 < x then Charge.antimatter
  else if x < 0 then Charge.matter
  else Charge.doesntMatter

-- ── THE MIXED SECOND DIFFERENCE δ²: the signed residue a pair accumulates around the gauge loop ──
/-- `pairDelta2` = the mixed second difference the pair reads = the holonomy residue. Trivial (0) on
an OPEN path (the right leg held at the path's own `middleRight` — a single-leg / held variation);
charged (±1) around the genuine LOOP (right leg swung off the middle): +1 (antimatter/positron) over
the tilted flux (`middleRight ≠ node0`), −1 (matter/electron) over the flat baseline. -/
def pairDelta2 (path : CubicGaugePath0) (v : CubicGaugeVariation0) : Int :=
  if v.right = path.middleRight then 0
  else if path.middleRight = node0 then -1
  else 1

/-- The holonomy IS the mixed second difference the pair accumulates. -/
def holonomy (path : CubicGaugePath0) (v : CubicGaugeVariation0) : Int := pairDelta2 path v

/-- A positron detector reads the POSITIVE sign of the holonomy. -/
def detectsPositron (path : CubicGaugePath0) (v : CubicGaugeVariation0) : Prop :=
  orientationOfSign (holonomy path v) = Charge.antimatter

theorem holonomy_open_is_trivial :
    holonomy tiltedPath (pairVariation node2 node1) = 0 := by decide

theorem holonomy_loop_is_charged :
    holonomy tiltedPath (pairVariation node1 node2) = 1
      ∧ holonomy flatPath (pairVariation node1 node2) = -1 := by decide

theorem detects_positron_over_tilt :
    detectsPositron tiltedPath (pairVariation node1 node2) := by
  unfold detectsPositron holonomy orientationOfSign; decide

theorem no_positron_over_flat :
    ¬ detectsPositron flatPath (pairVariation node1 node2) := by
  unfold detectsPositron holonomy orientationOfSign; decide

/-- Detection is FRAME-RELATIVE: the same loop reads opposite signs over the two baselines. Which
sign is "positron" is the flux convention — it doesn't matter. -/
theorem detection_is_frame_relative :
    holonomy flatPath (pairVariation node1 node2)
      = - holonomy tiltedPath (pairVariation node1 node2) := by decide

-- ── Events over the trial + the positron / matter counts (the split, counted) ──
def threePairs : List CubicGaugeVariation0 :=
  [pairVariation node1 node2, pairVariation node2 node1, pairVariation node1 node2]

def pairEvents (path : CubicGaugePath0) (vs : List CubicGaugeVariation0) : List Charge :=
  vs.map (fun v => orientationOfSign (holonomy path v))

def flatEvents   : List Charge := pairEvents flatPath threePairs
def tiltedEvents : List Charge := pairEvents tiltedPath threePairs

abbrev HasPositronEvent (es : List Charge) : Prop := Charge.antimatter ∈ es

theorem no_positron_over_flatPath : ¬ HasPositronEvent flatEvents := by decide
theorem positron_over_tiltedPath : HasPositronEvent tiltedEvents := by decide
theorem electron_over_flatPath : Charge.matter ∈ flatEvents := by decide

def antimatterCount (es : List Charge) : Nat :=
  (es.filter (fun o => match o with | Charge.antimatter => true | _ => false)).length
def matterCount (es : List Charge) : Nat :=
  (es.filter (fun o => match o with | Charge.matter => true | _ => false)).length

theorem native_antimatter_is_zero : antimatterCount flatEvents = 0 := by decide
theorem native_matter_is_present : 1 ≤ matterCount flatEvents := by decide
theorem antimatter_needs_asymmetry : 1 ≤ antimatterCount tiltedEvents := by decide

theorem the_split_counted :
    antimatterCount flatEvents = 0
      ∧ 1 ≤ matterCount flatEvents
      ∧ 1 ≤ antimatterCount tiltedEvents :=
  ⟨native_antimatter_is_zero, native_matter_is_present, antimatter_needs_asymmetry⟩

-- ── The frame reading (the Episode-82 surface: electron/positron readings that cancel) ──
structure FrameReading where
  whole : Int
  parts : Int
deriving DecidableEq, Repr

namespace FrameReading
def relVel (c : FrameReading) : Int := c.whole - c.parts
end FrameReading

def electronMeasurement : FrameReading := ⟨0, 1⟩   -- relVel = −1  (matter)
def positronReading     : FrameReading := ⟨1, 0⟩   -- relVel = +1  (antimatter, = −electron)

/-- The split cancels: the electron and positron readings are equal and opposite. -/
theorem split_cancels :
    electronMeasurement.relVel + positronReading.relVel = 0 := by decide

theorem positron_relVel_eq_neg_electron :
    positronReading.relVel = - electronMeasurement.relVel := by decide

end Measurement
