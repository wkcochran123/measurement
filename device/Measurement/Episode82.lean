import Measurement.Episode81

set_option maxHeartbeats 4000000
set_option maxRecDepth 1000
set_option allowUnsafeReducibility true

namespace Measurement

/-
__EPISODE 82__: _Relative Velocity Is a Selection — the Single `Quot.sound`_

OPERATOR (2026-06-17, verbatim):
"The code should compute the orientation split from relative electron motion, not
claim it has derived the Standard Model matter/antimatter asymmetry."

HONESTY GATE (non-negotiable; every claim in this file lives under it):
This episode MEASURES the matter/antimatter split -- it reads `sign(δ²)` through the
located selection-collapse.  It does NOT derive baryogenesis, CP violation, or a
Sakharov condition.  WHICH sign counts as "matter" is a CONVENTION fixed by
Episode73's tally (`sampleEvents`, `dominant_unique`), not derived here.  Claim
ceiling: "charge = sign(δ²); the matter/antimatter split is the sign of the
relative-velocity invariant, measured by the apparatus; orientation is a convention."

----

Episode52 produced the electron as the second variation δ² = MEASUREMENT - STORY
(`residue_is_the_difference_between_story_and_measurement`, Ep52:195) and placed its
strain in the stack's Frechet slot through the chair (`truthLocal`) -- the lone reason
`the_stack_produces_it` carries `Classical.choice`.

Here the SAME object is filed without the chair, and the one quotient-collapse the whole
construction needs is made explicit and named ONCE:

  RELATIVE VELOCITY of the produced pair  =  the frame-invariant  =  δ²  =  secondVariation
                                          =  whole - parts        (MEASUREMENT - STORY)

  ObservationallyEquivalent a b  :=  a and b are the SAME relative velocity  :=  same δ²
                                  :=  (a.whole - a.parts) = (b.whole - b.parts)
                                     -- a DECIDABLE relation (Int equality): omega discharges it.

  selection_sound  :=  the ONLY sanctioned `Quot.sound` site (raw `Quot`, no `Setoid`):
                       observationally-equivalent readings collapse to one class.

The electron's two readings -- ROUTE A "three readings with the EKG" (the MEASUREMENT,
`coupledCubicDifference`, a finite second difference assembled from the path's three
`segmentCost` reads, reconciled against the two first variations) and ROUTE B "the
other from the two first variations" (the second variation itself, the single
invariant) -- are observationally equivalent (same δ²), so they collapse via
`selection_sound`.  The matter/antimatter SPLIT is read by the SIGN across classes:
electron class -> -1 (matter), positron class (opposite orientation) -> +1 (antimatter);
they cancel (coheres with Episode73 `orientation_readings_cancel`).

Note (corrected by Kodo): `SlipMultiset` is a plain `List` wrapper and the device imports
no Mathlib, so there is no `Multiset`/`Quotient`; the corpus's ambient `Quot.sound` is
`funext`-borne.  This episode is the LOCATED, named home for `Quot.sound` (one site,
`selection_sound`); it does NOT scrub the ambient `funext` ones, and it does NOT remove
Episode52's `Classical.choice` (rerouting `the_stack_produces_it` and retiring the
genuine pre-Ep16 `SAME` needle are DEFERRED -- both edit built episodes).
-/

/-- A reading from a single trial: a `whole` count and a `parts` count.  The
boost-invariant -- the relative velocity, the second variation δ² -- is `whole - parts`
(a common Galilean boost adds the same constant to both and cancels here). -/
structure FrameReading where
  whole : Int
  parts : Int

namespace FrameReading

/-- The relative velocity / second variation δ²: the frame-invariant. -/
def relVel (c : FrameReading) : Int := c.whole - c.parts

end FrameReading

/-- A measured candidate reading of the pair's relative velocity. -/
abbrev Candidate := FrameReading

/-- The collapse relation: two readings are observationally equivalent iff they are the
SAME relative velocity (same δ²).  Decidable (Int equality) -- dischargeable by `omega`. -/
def ObservationallyEquivalent (a b : Candidate) : Prop :=
  a.relVel = b.relVel

-- The collapse point is the SHARED polymorphic `Measurement.selection_sound` (defined
-- ONCE in Episode15 -- the corpus's single sanctioned `Quot.sound` site). Episode82 no
-- longer declares its own (that local copy collided with Ep15's at the same
-- `Measurement.selection_sound` name); `relvel_routes_agree` below instances the shared
-- lemma at `r := ObservationallyEquivalent` (inferred from `routes_same_invariant`).

/-- The relative-velocity quotient: candidate readings modulo observational
equivalence (same δ²).  Raw `Quot`, not `Quotient` -- no `Setoid`. -/
def RelVel : Type := Quot ObservationallyEquivalent

namespace RelVel

/-- The class of a reading. -/
def mk (c : Candidate) : RelVel := Quot.mk ObservationallyEquivalent c

/-- The relative velocity δ², lifted to the quotient (well-defined: equivalence IS
equality of the invariant).  `Quot.lift` is a computation rule, not an axiom. -/
def value : RelVel → Int :=
  Quot.lift FrameReading.relVel (fun _ _ h => h)

/-- The matter/antimatter SPLIT: the SIGN of the relative-velocity invariant, lifted to
the quotient.  Matter is one sign, antimatter the other; which is which is the
convention (see HONESTY GATE). -/
def splitSign : RelVel → Int :=
  Quot.lift (fun c => Int.sign c.relVel) (fun _ _ h => congrArg Int.sign h)

end RelVel

namespace CubicGaugeVariation

/-- ROUTE A -- "three readings with the EKG".  The measured coupled cost difference as
the whole, the two first variations as the parts.  Its δ² is the second variation. -/
def measurementReading
    (action : FiniteGaugeAction) (path : CubicGaugePath)
    (variation : CubicGaugeVariation) : FrameReading where
  whole := coupledCubicDifference action path variation
  parts :=
    CubicGaugePath.leftMiddleResidual action path (leftVariation variation) +
      CubicGaugePath.rightMiddleResidual action path (rightVariation variation)

/-- ROUTE B -- "the other you make from the two first variations".  The second variation
itself (the single invariant), no parts.  Its δ² is the second variation. -/
def invariantReading
    (action : FiniteGaugeAction) (path : CubicGaugePath)
    (variation : CubicGaugeVariation) : FrameReading where
  whole := secondVariation action path variation
  parts := 0

/-- U3 (the contrast lemma): the two routes are the SAME relative velocity -- the bare
δ² identity, proved WITHOUT the quotient.  `Quot.sound`-FREE (`omega` over `Int`, via
Episode31's decomposition).  The only thing the collapse adds on top of this is
`Quot.sound`, which proves the collapse's `Quot.sound` is LOCATED, not ambient. -/
theorem routes_same_invariant
    (action : FiniteGaugeAction) (path : CubicGaugePath)
    (variation : CubicGaugeVariation) :
    ObservationallyEquivalent
      (measurementReading action path variation)
      (invariantReading action path variation) := by
  have h :=
    coupledCubicDifference_eq_left_right_plus_secondVariation action path variation
  simp only [ObservationallyEquivalent, FrameReading.relVel,
    measurementReading, invariantReading]
  omega

/-- The two readings collapse to one relative velocity THROUGH `selection_sound` (the
sole `Quot.sound`); no second `Quot.sound`/`Quotient.sound` call anywhere. -/
theorem relvel_routes_agree
    (action : FiniteGaugeAction) (path : CubicGaugePath)
    (variation : CubicGaugeVariation) :
    RelVel.mk (measurementReading action path variation) =
      RelVel.mk (invariantReading action path variation) :=
  selection_sound (routes_same_invariant action path variation)

end CubicGaugeVariation

/-
The produced pair (Episode52): the electron at `discriminatingAction flatPath pairKick`,
and the positron as the opposite orientation.
-/

/-- Route A at the electron. -/
def electronMeasurement : FrameReading :=
  CubicGaugeVariation.measurementReading discriminatingAction flatPath pairKick

/-- Route B at the electron. -/
def electronInvariant : FrameReading :=
  CubicGaugeVariation.invariantReading discriminatingAction flatPath pairKick

/-- The positron: the OPPOSITE orientation (STORY - MEASUREMENT), i.e. the electron's
reading with `whole`/`parts` swapped -- its δ² is the negation. -/
def positronReading : FrameReading :=
  { whole := electronMeasurement.parts, parts := electronMeasurement.whole }

/-- The electron's two readings are the same relative velocity (collapse via the located
`Quot.sound`). -/
theorem electron_routes_agree :
    RelVel.mk electronMeasurement = RelVel.mk electronInvariant :=
  CubicGaugeVariation.relvel_routes_agree discriminatingAction flatPath pairKick

/-- The relative velocity δ² of the electron's invariant reading IS the electron
(Episode52 `electron`; `electron_charge` = -1). -/
theorem electron_relVel_eq_electron :
    electronInvariant.relVel = electron := by
  simp only [electronInvariant, CubicGaugeVariation.invariantReading,
    FrameReading.relVel, electron, CubicGaugeVariation.secondVariation]
  omega

/-- The split has opposite signs: the positron's relative velocity is the negation of the
electron's (opposite orientation). -/
theorem positron_relVel_eq_neg_electron :
    positronReading.relVel = - electronMeasurement.relVel := by
  simp only [positronReading, FrameReading.relVel]
  omega

/-- Matter and antimatter cancel: the electron and positron relative velocities sum to
zero (coheres with Episode73 `orientation_readings_cancel`).  Axiom-free (`omega`) -- the
cancellation is structural, not a derived asymmetry. -/
theorem split_cancels :
    electronMeasurement.relVel + positronReading.relVel = 0 := by
  simp only [positronReading, FrameReading.relVel]
  omega

/-
The standing record.  Verified by the operator's build (NOT run here -- no build this
round).  Expected results inline.
-/

-- U2': the single sanctioned `Quot.sound` site, and ONLY `Quot.sound`.
#print axioms selection_sound
  -- expect: [Quot.sound]  (EXACTLY -- no propext, no Classical.choice)

-- U2'': route-agreement routes THROUGH selection_sound; no second Quot.sound call.
#print axioms CubicGaugeVariation.relvel_routes_agree
  -- expect: Quot.sound present, NO Classical.choice  (propext ok)

-- U3: the bare δ² identity is `Quot.sound`-FREE -- the contrast proving the collapse's
-- `Quot.sound` is located, not ambient.
#print axioms CubicGaugeVariation.routes_same_invariant
  -- expect: Quot.sound-FREE (at most [propext])

-- U4': the SIGN readout is the matter/antimatter split.
#eval RelVel.splitSign (RelVel.mk electronMeasurement)   -- expect: -1  (matter)
#eval RelVel.splitSign (RelVel.mk positronReading)       -- expect:  1  (antimatter)
#eval RelVel.value (RelVel.mk electronMeasurement)        -- δ² of the electron: expect -1

end Measurement
