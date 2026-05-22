import Measurement.Episode15
namespace Measurement


noncomputable def truthPhase (P : Prop) : P ∨ ¬P :=
  Classical.em P

noncomputable instance truthRepeatable_fixedPoint
    [xx : REPEATABLE Prop truthCarrier]
    : Inhabited (
        xx.typical_response
          xx.repeatable_process.expectation
          xx.repeatable_process.expectation
        ∨
        ¬ (xx.typical_response
             xx.repeatable_process.expectation
             xx.repeatable_process.expectation)) :=
  ⟨truthPhase
      (xx.typical_response
         xx.repeatable_process.expectation
         xx.repeatable_process.expectation)⟩

noncomputable instance truthSymbolInhabited :
    Inhabited truthDistinct.symbol :=
  ⟨Fact.Truth.truth⟩

noncomputable instance truthAdmissible :
    ADMISSIBLE Prop truthCarrier :=
  STEP_1 Prop truthCarrier

noncomputable instance truthCountable :
    COUNTABLE Prop truthCarrier :=
  COUNTABLE_ADMISSIBLE Prop truthCarrier

noncomputable instance truthEncoded :
    ENCODED Prop truthCarrier :=
  ENCODED_COUNTABLE Prop truthCarrier

noncomputable instance truthResidue :
    RESIDUE Prop truthCarrier :=
  RESIDUE_ENCODED Prop truthCarrier

noncomputable instance truthBinary :
    BINARY Prop truthCarrier :=
  BINARY_RESIDUE Prop truthCarrier

noncomputable instance truthRepeatable :
    REPEATABLE Prop truthCarrier :=
  REPEATABLE_BINARY Prop truthCarrier

noncomputable instance truthNumeric :
    NUMERIC Prop truthCarrier :=
  NUMERIC_REPEATABLE Prop truthCarrier

noncomputable instance truthRepresentable :
    REPRESENTABLE Prop truthCarrier :=
  REPRESENTABLE_NUMERIC Prop truthCarrier

noncomputable instance truthPhysical :
    PHYSICAL Prop truthCarrier :=
  PHYSICAL_NUMERIC Prop truthCarrier

noncomputable instance truthComparable :
    COMPARABLE Prop truthCarrier :=
  COMPARABLE_PHYSICAL Prop truthCarrier

noncomputable instance truthObserved :
    OBSERVED Prop truthCarrier :=
  OBSERVED_COMPARABLE Prop truthCarrier

noncomputable instance truthPresent :
    PRESENT Prop truthCarrier :=
  PRESENT_OBSERVED Prop truthCarrier

noncomputable instance truthMeasurable :
    MEASURABLE Prop truthCarrier :=
  MEASURABLE_PRESENT Prop truthCarrier

noncomputable instance truthGungan :
    GUNGAN Prop truthCarrier :=
  GUNGAN_MEASURABLE Prop truthCarrier

noncomputable instance truthSource :
    SOURCE Prop truthCarrier :=
  SOURCE_GUNGAN Prop truthCarrier

noncomputable instance truthExecuted :
    EXECUTED Prop truthCarrier :=
  EXECUTED_SOURCE Prop truthCarrier

noncomputable instance truthValue :
    VALUE Prop truthCarrier :=
  VALUE_EXECUTED Prop truthCarrier

noncomputable instance truthMagnitude :
    MAGNITUDE Prop truthCarrier :=
  MAGNITUDE_VALUE Prop truthCarrier

noncomputable instance truthScaled :
    SCALED Prop truthCarrier :=
  SCALED_MAGNITUDE Prop truthCarrier

noncomputable instance truthLoad :
    LOAD Prop truthCarrier :=
  LOAD_SCALED Prop truthCarrier

noncomputable instance truthFiniteElephant :
    FINITE_ELEPHANT Prop truthCarrier :=
  FINITE_ELEPHANT_LOAD Prop truthCarrier

noncomputable instance truthBullshit :
    BULLSHIT Prop truthCarrier :=
  BULLSHIT_FINITE_ELEPHANT Prop truthCarrier

noncomputable instance truthPropaganda :
    PROPAGANDA Prop truthCarrier :=
  PROPAGANDA_BULLSHIT Prop truthCarrier

noncomputable instance truthAcolyte :
    ACOLYTE Prop truthCarrier :=
  ACOLYTE_PROPAGANDA Prop truthCarrier

noncomputable instance truthScientific :
    SCIENTIFIC Prop truthCarrier :=
  SCIENTIFIC_ACOLYTE Prop truthCarrier

noncomputable instance truthTruth :
    TRUTH Prop truthCarrier :=
  TRUTH_SCIENTIFIC Prop truthCarrier

noncomputable instance truthWitnessed :
    WITNESSED Prop truthCarrier :=
  WITNESSED_TRUTH Prop truthCarrier

noncomputable instance truthReal :
    REAL Prop truthCarrier :=
  REAL_WITNESSED Prop truthCarrier

noncomputable instance truthLocal :
    LOCAL Prop truthCarrier :=
  LOCAL_REAL Prop truthCarrier

noncomputable instance truthUniversal :
    UNIVERSAL Prop truthCarrier :=
  UNIVERSAL_LOCAL Prop truthCarrier

noncomputable instance truthLogical :
    LOGICAL Prop truthCarrier :=
  LOGICAL_UNIVERSAL Prop truthCarrier

noncomputable instance truthElaborationProcess
    [prop: LOGICAL Prop truthCarrier]
    : ElaborationProcess Prop truthCarrier where
  stamina := prop.feelings
  calibration := prop.ekg
  computer_state := .load Fact.Truth Fact.Truth.truth Prop

noncomputable instance truthHalted :
    HALTED Prop truthCarrier :=
  HALTED_LOGICAL Prop truthCarrier

noncomputable instance truthMeasured :
    MEASURED Prop truthCarrier :=
  MEASURED_HALTED Prop truthCarrier

noncomputable instance truthCompiled :
    COMPILED Prop truthCarrier :=
  COMPILED_MEASURED Prop truthCarrier

noncomputable instance truthTrueOutput :
    TrueOutput Prop truthCarrier :=
  TRUE_COMPILED Prop truthCarrier

noncomputable instance truthInferred :
    INFERRED Prop truthCarrier :=
  INFERRED_TRUE Prop truthCarrier


set_option maxHeartbeats 0
set_option synthInstance.maxHeartbeats 0

noncomputable def theory_true? : Prop :=
  let inst : INFERRED Prop truthCarrier := inferInstance
  inst.inferred?
    inst.equivalence_process.closure
    inst.theory


#check theory_true?

end Measurement
