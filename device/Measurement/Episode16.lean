import Measurement.Episode15
import Measurement.Calibration.EKGBounded
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

namespace TruthTransition

noncomputable def reader : AtreyuProcess Prop truthCarrier :=
  truthTrueOutput.atreyu_process

noncomputable def repeatable : Bullshit :=
  THEORY.repeatable reader truthTrueOutput.TRUE

noncomputable def hypothesis : Bullshit :=
  THEORY.hypothesis reader truthTrueOutput.TRUE

noncomputable def theory : Bullshit :=
  THEORY.theory reader truthTrueOutput.TRUE

noncomputable def raw_output : Bullshit :=
  THEORY.raw_output reader truthTrueOutput.TRUE

noncomputable def trueOutput_value1 : Prop :=
  truthTrueOutput.obfusplained?
    truthTrueOutput.output_true
    repeatable
    hypothesis

noncomputable def trueOutput_value2 : Prop :=
  truthTrueOutput.obfusplained?
    truthTrueOutput.output_true
    hypothesis
    theory

noncomputable def trueOutput_direct : Prop :=
  truthTrueOutput.obfusplained?
    truthTrueOutput.output_true
    repeatable
    theory

noncomputable def trueOutput_composed : Prop :=
  trueOutput_value1 ∧ trueOutput_value2

noncomputable def trueOutput_coherent : Prop :=
  trueOutput_direct = trueOutput_composed

noncomputable def closure_repeatable_hypothesis : Closure :=
  truthInferred.equivalence_process.close? repeatable hypothesis

noncomputable def closure_hypothesis_theory : Closure :=
  truthInferred.equivalence_process.close? hypothesis theory

noncomputable def closure_repeatable_theory : Closure :=
  truthInferred.equivalence_process.close? repeatable theory

noncomputable def equivalence_value1 : Prop :=
  Closure.le
    truthInferred.equivalence_process.closure
    closure_repeatable_hypothesis

noncomputable def equivalence_value2 : Prop :=
  Closure.le
    closure_repeatable_hypothesis
    closure_hypothesis_theory

noncomputable def equivalence_direct : Prop :=
  Closure.le
    truthInferred.equivalence_process.closure
    closure_repeatable_theory

noncomputable def equivalence_composed : Prop :=
  equivalence_value1 ∧ equivalence_value2

noncomputable def equivalence_coherent : Prop :=
  equivalence_direct = equivalence_composed

noncomputable def inferred_value1 : Prop :=
  truthInferred.inferred?
    closure_repeatable_hypothesis
    closure_hypothesis_theory

noncomputable def inferred_value2 : Prop :=
  truthInferred.inferred?
    closure_hypothesis_theory
    truthInferred.theory

noncomputable def inferred_direct : Prop :=
  truthInferred.inferred?
    closure_repeatable_theory
    truthInferred.theory

noncomputable def inferred_composed : Prop :=
  inferred_value1 ∧ inferred_value2

noncomputable def inferred_coherent : Prop :=
  inferred_direct = inferred_composed

noncomputable def transition_coherent : Prop :=
  trueOutput_coherent ∧ equivalence_coherent ∧ inferred_coherent

structure StepValues where
  trueOutput_first : Prop
  trueOutput_second : Prop
  trueOutput_direct : Prop
  trueOutput_composed : Prop
  trueOutput_coherent : Prop
  equivalence_first : Prop
  equivalence_second : Prop
  equivalence_direct : Prop
  equivalence_composed : Prop
  equivalence_coherent : Prop
  inferred_first : Prop
  inferred_second : Prop
  inferred_direct : Prop
  inferred_composed : Prop
  inferred_coherent : Prop
  transition_coherent : Prop

noncomputable def step_values : StepValues where
  trueOutput_first := trueOutput_value1
  trueOutput_second := trueOutput_value2
  trueOutput_direct := trueOutput_direct
  trueOutput_composed := trueOutput_composed
  trueOutput_coherent := trueOutput_coherent
  equivalence_first := equivalence_value1
  equivalence_second := equivalence_value2
  equivalence_direct := equivalence_direct
  equivalence_composed := equivalence_composed
  equivalence_coherent := equivalence_coherent
  inferred_first := inferred_value1
  inferred_second := inferred_value2
  inferred_direct := inferred_direct
  inferred_composed := inferred_composed
  inferred_coherent := inferred_coherent
  transition_coherent := transition_coherent

end TruthTransition


-- EKG bounded subjunctive probe: MEASURE the evaluation of the proposition,
-- and that is all. Budget 720 user-heartbeats = 9 (a Fact) * 8 (a 3SAT clause's
-- 2^3 assignments) * 10 (safety) = 720000 internal compiler heartbeats. The
-- probe binds no declaration, so it cannot leak universe metavariables, and it
-- never fails the module: on outgrowth it logs the EKG event and continues.
ekg_probe 7 =>
  TruthTransition.transition_coherent

theorem true_eq_false :
    Subsingleton Fact.Truth.truth = Subsingleton (¬ Fact.Truth.truth) := by
  apply propext
  exact ⟨fun _ => inferInstance, fun _ => inferInstance⟩

end Measurement
