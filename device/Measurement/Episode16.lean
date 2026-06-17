import Measurement.Episode15
import Measurement.Calibration.EKGBounded
namespace Measurement


-- `truthPhase`/`truthRepeatable_fixedPoint` removed (no axiom of choice): they
-- used `Classical.em` to inhabit `R ∨ ¬R` for an ARBITRARY `[xx : REPEATABLE
-- Prop truthCarrier]`, whose `R = xx.typical_response e e` is abstract -- so no
-- constructive witness exists for generic `xx`. The instance had no consumer, so
-- deletion removes the excluded-middle root cleanly. (If a hidden typeclass use
-- surfaces at build, re-add a SPECIALIZED constructive instance: for the concrete
-- REPEATABLE_BINARY carrier, `expectation = .hypothesis ..` and `iterate` returns
-- `.signal_response ..`, so `R` is false and `Or.inr` closes it without choice.)

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

-- EKG bounded subjunctive probe: MEASURE elaboration of the proposition-shaped
-- term, and that is all. This smoke pulse uses budget 7. The fuller one-clause
-- budget appears later as 720 = 9 fact positions * 8 three-bit assignments * 10
-- safety. The probe binds no declaration, so it cannot leak universe
-- metavariables, and it never fails the module: on outgrowth it logs the EKG
-- event and continues.
ekg_probe 7 =>
  let repeatable : Bullshit :=
    truthTrueOutput.TRUE
  let hypothesis : Bullshit :=
    truthTrueOutput.output
  let theory : Bullshit :=
    truthTrueOutput.atreyu_process.satirize truthTrueOutput.output
  let trueOutput_value1 : Prop :=
    truthTrueOutput.obfusplained?
      truthTrueOutput.output_true
      repeatable
      hypothesis
  let trueOutput_value2 : Prop :=
    truthTrueOutput.obfusplained?
      truthTrueOutput.output_true
      hypothesis
      theory
  let trueOutput_direct : Prop :=
    truthTrueOutput.obfusplained?
      truthTrueOutput.output_true
      repeatable
      theory
  let trueOutput_coherent : Prop :=
    trueOutput_direct = (trueOutput_value1 ∧ trueOutput_value2)
  let closure_repeatable_hypothesis : Closure :=
    truthInferred.equivalence_process.close? repeatable hypothesis
  let closure_hypothesis_theory : Closure :=
    truthInferred.equivalence_process.close? hypothesis theory
  let closure_repeatable_theory : Closure :=
    truthInferred.equivalence_process.close? repeatable theory
  let equivalence_value1 : Prop :=
    Closure.le
      truthInferred.equivalence_process.closure
      closure_repeatable_hypothesis
  let equivalence_value2 : Prop :=
    Closure.le
      closure_repeatable_hypothesis
      closure_hypothesis_theory
  let equivalence_direct : Prop :=
    Closure.le
      truthInferred.equivalence_process.closure
      closure_repeatable_theory
  let equivalence_coherent : Prop :=
    equivalence_direct = (equivalence_value1 ∧ equivalence_value2)
  let inferred_value1 : Prop :=
    truthInferred.inferred?
      closure_repeatable_hypothesis
      closure_hypothesis_theory
  let inferred_value2 : Prop :=
    truthInferred.inferred?
      closure_hypothesis_theory
      truthInferred.theory
  let inferred_direct : Prop :=
    truthInferred.inferred?
      closure_repeatable_theory
      truthInferred.theory
  let inferred_coherent : Prop :=
    inferred_direct = (inferred_value1 ∧ inferred_value2)
  trueOutput_coherent ∧ equivalence_coherent ∧ inferred_coherent

theorem true_eq_false :
    Subsingleton Fact.Truth.truth = Subsingleton (¬ Fact.Truth.truth) := by
  apply propext
  exact ⟨fun _ => inferInstance, fun _ => inferInstance⟩

end Measurement
