import Measurement.Episode72

set_option maxHeartbeats 4000000
set_option maxRecDepth 1000
set_option allowUnsafeReducibility true

namespace Measurement

/-
__EPISODE 73__: _The Orientation EKG_

Episode52 produced the signed pair and said the impolite part out loud: the
electron sign was a convention chosen by the corpus's measurement-minus-story
orientation.  The opposite orientation reads +1 by `positron_charge`, and the
pair cancels.  `Measurement.GeneratedQEDBridge` later preserves that fact at
the generated-device layer as `generated_orientations_cancel`.  Episode31's
SPD positivity is the same warning from another wall: a negative sign is not a
diagonal energy reading.  The norm carries magnitude; the sign lives in the
cross term and in the chosen orientation of the instrument.

So this episode does not derive the electron's sign from the interior.  It
does the only gauge fixing available to an apparatus: count.  Episodes26,
27, and 32 already used the EKG pattern for elaborator heartbeats: an
undecided comparison becomes anchored when measured separation makes the
fastest candidate unique.  Here the same instrument logic is pointed at
charge orientation.  Replace "fastest" by "most frequent."  If one
orientation clears the other by a noise floor, then the dominant orientation
is unique.

Convention is gauge.  Tally is measurement.

Stated formally:
* `Orientation`, `Orientation.other`, and `orientationReading` name the two
  charge orientations and read them as Episode52's -1/+1 pair.
* `orientationReading_electron`, `orientationReading_positron`, and
  `orientation_readings_cancel` file the computable signs and cancellation.
* `OrientationTally.Dominates` says an orientation beats its opposite past a
  noise floor.
* `dominant_unique` is the EKG theorem: two orientations cannot both dominate
  the same tally.
* `ConventionAnchor`, `anchor_unique`, and
  `ConventionAnchor.anchoredReading` package the empirical convention as data
  with proof, not choice.
* `sampleEvents`, `sampleTally`, `sampleAnchor`, and `sampleReadout` give a
  closed computable apparatus sample.

Residue left (honest scope):
the tally anchors the convention; it does not derive the sign.  "One happens
more" is empirical input, represented here by a finite sample list standing in
for an apparatus.  No CP violation, Sakharov condition, baryogenesis, standard
model asymmetry, or standard-physics charge convention theorem is claimed.
The interior remains sign-blind in exactly the sense the prior episodes
advertised: magnitude is not orientation.
-/

inductive Orientation where
  | electron
  | positron
deriving DecidableEq, Repr

namespace Orientation

def other : Orientation -> Orientation
  | .electron => .positron
  | .positron => .electron

end Orientation

def orientationReading : Orientation -> Int
  | .electron => electron
  | .positron =>
      (CubicGaugePath.leftMiddleResidual discriminatingAction flatPath
          (CubicGaugeVariation.leftVariation pairKick) +
        CubicGaugePath.rightMiddleResidual discriminatingAction flatPath
          (CubicGaugeVariation.rightVariation pairKick)) -
        CubicGaugeVariation.coupledCubicDifference
          discriminatingAction flatPath pairKick

theorem orientationReading_electron :
    orientationReading .electron = -1 := by
  decide

theorem orientationReading_positron :
    orientationReading .positron = 1 := by
  decide

theorem orientation_readings_cancel :
    orientationReading .electron + orientationReading .positron = 0 := by
  decide

structure OrientationTally where
  count : Orientation -> Nat
  noiseFloor : Nat

namespace OrientationTally

def Dominates (t : OrientationTally) (o : Orientation) : Prop :=
  t.count (Orientation.other o) + t.noiseFloor < t.count o

end OrientationTally

theorem dominant_unique
    {t : OrientationTally} {o1 o2 : Orientation} :
    t.Dominates o1 -> t.Dominates o2 -> o1 = o2 := by
  intro h1 h2
  cases o1 with
  | electron =>
      cases o2 with
      | electron => rfl
      | positron =>
          unfold OrientationTally.Dominates at h1 h2
          simp [Orientation.other] at h1 h2
          exact absurd h1 (by omega)
  | positron =>
      cases o2 with
      | electron =>
          unfold OrientationTally.Dominates at h1 h2
          simp [Orientation.other] at h1 h2
          exact absurd h1 (by omega)
      | positron => rfl

structure ConventionAnchor where
  tally : OrientationTally
  dominant : Orientation
  dominates : tally.Dominates dominant

theorem anchor_unique
    (A B : ConventionAnchor)
    (sameTally : A.tally = B.tally) :
    A.dominant = B.dominant := by
  exact
    dominant_unique
      (t := A.tally)
      (o1 := A.dominant)
      (o2 := B.dominant)
      A.dominates
      (by
        rw [sameTally]
        exact B.dominates)

namespace ConventionAnchor

def anchoredReading (A : ConventionAnchor) : Int :=
  orientationReading A.dominant

end ConventionAnchor

def sampleEvents : List Orientation :=
  [ .electron
  , .electron
  , .electron
  , .positron
  , .electron
  , .electron
  , .positron
  , .electron
  , .electron
  ]

def orientationCount (events : List Orientation) : Orientation -> Nat :=
  events.foldr
    (fun event counts query =>
      if event = query then counts query + 1 else counts query)
    (fun _ => 0)

def sampleTally : OrientationTally where
  count := orientationCount sampleEvents
  noiseFloor := 2

theorem sample_electron_count :
    sampleTally.count .electron = 7 := by
  decide

theorem sample_positron_count :
    sampleTally.count .positron = 2 := by
  decide

theorem sample_electron_dominates :
    sampleTally.Dominates .electron := by
  unfold OrientationTally.Dominates sampleTally orientationCount sampleEvents
  decide

def sampleAnchor : ConventionAnchor where
  tally := sampleTally
  dominant := .electron
  dominates := sample_electron_dominates

theorem sample_anchoredReading :
    sampleAnchor.anchoredReading = -1 := by
  decide

structure OrientationEKGReadout where
  electronCount : Nat
  positronCount : Nat
  dominant : Orientation
  anchoredReading : Int
  cancellation : Int
deriving Repr

def sampleReadout : OrientationEKGReadout where
  electronCount := sampleTally.count .electron
  positronCount := sampleTally.count .positron
  dominant := sampleAnchor.dominant
  anchoredReading := sampleAnchor.anchoredReading
  cancellation := orientationReading .electron + orientationReading .positron

#eval sampleReadout

#print axioms orientationReading_electron
-- expected: 'Measurement.orientationReading_electron' does not depend on any axioms
#print axioms orientationReading_positron
-- expected: 'Measurement.orientationReading_positron' does not depend on any axioms
#print axioms orientation_readings_cancel
-- expected: 'Measurement.orientation_readings_cancel' does not depend on any axioms
#print axioms dominant_unique
-- expected: 'Measurement.dominant_unique' depends on axioms: [propext, Quot.sound]
#print axioms anchor_unique
-- expected: 'Measurement.anchor_unique' depends on axioms: [propext, Quot.sound]
#print axioms ConventionAnchor.anchoredReading
-- expected: 'Measurement.ConventionAnchor.anchoredReading' does not depend on any axioms
#print axioms sample_electron_count
-- expected: 'Measurement.sample_electron_count' does not depend on any axioms
#print axioms sample_positron_count
-- expected: 'Measurement.sample_positron_count' does not depend on any axioms
#print axioms sample_electron_dominates
-- expected: 'Measurement.sample_electron_dominates' does not depend on any axioms
#print axioms sampleAnchor
-- expected: 'Measurement.sampleAnchor' does not depend on any axioms
#print axioms sample_anchoredReading
-- expected: 'Measurement.sample_anchoredReading' does not depend on any axioms

end Measurement
