import Measurement.Episode57
import Measurement.Formalization.QED

set_option autoImplicit false

/-!
# The Generated Program Through The Device Image

The paper's bridge tier, applied to the generated program: the electron and
positron readings of `GeneratedQEDProgram` (Episode55), each read through a
`PhysicalExperiment` / `DeviceEncoding` pair into the terminal Herbrand
image (Formalization/QED).

One discipline drives the design: the terminal device-image theorems say
all encoded candidates in one image share ONE observable under one
interpreter (`gauge_unique_on_device_image`).  Therefore `electron = -1`
and `positron = +1` cannot inhabit one terminal image as distinct
observables.  Per the paper lane's decision, each orientation gets its OWN
experiment -- `generatedElectronExperiment` and
`generatedPositronExperiment` -- preserving both charge theorems at full
strength.  The sign is not smuggled outside the formalism; it selects the
experiment.

Candidates are `Unit`: the bridge theorem is about the generated canonical
output, and pretending the image is total over physical states would be a
larger claim than the corpus makes.  Honesty about size: the interpreters
are CONSTANT functions of the Herbrand term, so at this instance the
terminal-uniqueness layer is exercised, not load-bearing -- the image
subsingleton would hold for any constant map on `Unit`.  What the bridge
buys is the SLOT: the generated readings now live in the same device-image
shape as every other observable in the formalization, ready for an
interpreter that genuinely reads the term.  And the orientation pair is
formally registered, not narrated: the two images' points cancel
(`generated_orientations_cancel`).

This file lives OUTSIDE the episode chain (it imports both stacks); the
episode apex stays `Measurement.lean`'s import, per the paper lane's
bridge-file rule.
-/

namespace Measurement.Formalization

open Measurement

/-- The electron experiment: the generated program's excitation channel,
read at the pair kick.  One canonical candidate, observable in `Int`. -/
def generatedElectronExperiment
    {P : GeometricProgram} (Q : GeneratedQEDProgram P) :
    PhysicalExperiment where
  Candidate := Unit
  Observable := Int
  admissible := fun _ => True
  gauge := fun _ =>
    CubicGaugeVariation.mixedCubicCoupling
      Q.excitationAction Q.path Q.electronPair

/-- The electron's device encoding: every candidate encodes to the
canonical terminal term, and the interpreter reads the generated
coupling. -/
def generatedElectronEncoding
    {P : GeometricProgram} (Q : GeneratedQEDProgram P) :
    DeviceEncoding (generatedElectronExperiment Q) where
  Encodable := fun _ => True
  encode := fun _ _ _ => inferredTerm
  interpret := fun _ =>
    CubicGaugeVariation.mixedCubicCoupling
      Q.excitationAction Q.path Q.electronPair
  agrees := fun _ _ _ => rfl

/-- The positron experiment: the opposite orientation -- story minus
measurement -- as its own experiment, per the one-observable-per-image
discipline. -/
def generatedPositronExperiment
    {P : GeometricProgram} (Q : GeneratedQEDProgram P) :
    PhysicalExperiment where
  Candidate := Unit
  Observable := Int
  admissible := fun _ => True
  gauge := fun _ =>
    (CubicGaugePath.leftMiddleResidual Q.excitationAction Q.path
        (CubicGaugeVariation.leftVariation Q.electronPair) +
      CubicGaugePath.rightMiddleResidual Q.excitationAction Q.path
        (CubicGaugeVariation.rightVariation Q.electronPair)) -
      CubicGaugeVariation.coupledCubicDifference
        Q.excitationAction Q.path Q.electronPair

/-- The positron's device encoding. -/
def generatedPositronEncoding
    {P : GeometricProgram} (Q : GeneratedQEDProgram P) :
    DeviceEncoding (generatedPositronExperiment Q) where
  Encodable := fun _ => True
  encode := fun _ _ _ => inferredTerm
  interpret := fun _ =>
    (CubicGaugePath.leftMiddleResidual Q.excitationAction Q.path
        (CubicGaugeVariation.leftVariation Q.electronPair) +
      CubicGaugePath.rightMiddleResidual Q.excitationAction Q.path
        (CubicGaugeVariation.rightVariation Q.electronPair)) -
      CubicGaugeVariation.coupledCubicDifference
        Q.excitationAction Q.path Q.electronPair
  agrees := fun _ _ _ => rfl

/-- The electron's device image is a single point. -/
theorem generated_electron_device_image_unique
    {P : GeometricProgram} (Q : GeneratedQEDProgram P) :
    Subsingleton
      { o : Int //
        ∃ c : Unit,
          ∃ _ : (generatedElectronExperiment Q).admissible c,
            ∃ _ : (generatedElectronEncoding Q).Encodable c,
              o = (generatedElectronExperiment Q).gauge c } :=
  device_gauge_image_subsingleton
    (generatedElectronExperiment Q)
    (generatedElectronEncoding Q)

/-- The positron's device image is a single point. -/
theorem generated_positron_device_image_unique
    {P : GeometricProgram} (Q : GeneratedQEDProgram P) :
    Subsingleton
      { o : Int //
        ∃ c : Unit,
          ∃ _ : (generatedPositronExperiment Q).admissible c,
            ∃ _ : (generatedPositronEncoding Q).Encodable c,
              o = (generatedPositronExperiment Q).gauge c } :=
  device_gauge_image_subsingleton
    (generatedPositronExperiment Q)
    (generatedPositronEncoding Q)

/-- The electron image's one point reads -1. -/
theorem generated_electron_image_reads_minus_one :
    (generatedElectronExperiment generatedThreeRungQEDProgram).gauge
        Unit.unit = (-1 : Int) :=
  generatedThreeRungQEDProgram.electronReads

/-- The positron image's one point reads +1. -/
theorem generated_positron_image_reads_plus_one :
    (generatedPositronExperiment generatedThreeRungQEDProgram).gauge
        Unit.unit = (1 : Int) :=
  generatedThreeRungQEDProgram.positronReads

/-- The electron image's point, read at type `Int`. -/
noncomputable def electronImagePoint : Int :=
  (generatedElectronExperiment generatedThreeRungQEDProgram).gauge Unit.unit

/-- The positron image's point, read at type `Int`. -/
noncomputable def positronImagePoint : Int :=
  (generatedPositronExperiment generatedThreeRungQEDProgram).gauge Unit.unit

/-- The orientation pair is real: the electron image's point and the
positron image's point cancel. -/
theorem generated_orientations_cancel :
    electronImagePoint + positronImagePoint = 0 := by
  unfold electronImagePoint positronImagePoint
  rw [generated_electron_image_reads_minus_one,
    generated_positron_image_reads_plus_one]
  decide

/-- Acceptance pin for the Formalization bridge theorem: the truth stack's
transmute IS the default closure, so `finiteGaugeEquation_eq_transmute`'s
hypothesis has a checked witness. -/
example : UsesDefaultTransmute (truthLocal.{0, 0, 0, 0}).theory := rfl

-- The standing record: the device-image layer adds no axioms beyond the
-- chair already in the generated program.
#print axioms generated_electron_device_image_unique
#print axioms generated_electron_image_reads_minus_one
#print axioms generated_positron_image_reads_plus_one
#print axioms generated_orientations_cancel

end Measurement.Formalization
