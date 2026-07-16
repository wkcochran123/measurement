import Measurement.Episode15
import Measurement.Episode17
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

/--
A-pulse.  The transmitter gives the carrier a glyph before it gives the
mountain an argument.  This is not evidence yet; it is the first aperture,
the mouthpiece the later signal will pretend was always there.
-/
noncomputable instance truthSymbolInhabited :
    Inhabited truthDistinct.symbol :=
  ⟨Fact.Truth.truth⟩

/--
B-pulse.  The transmitter admits the mark: a local permission, not a global
law.  The pulse is allowed to leave because the device has named one place
where leaving counts.
-/
noncomputable instance truthAdmissible :
    ADMISSIBLE Prop truthCarrier :=
  STEP_1 Prop truthCarrier

/--
B-pulse.  The transmitter counts the number: another local permission wearing
an index.  Same pulse, different handle; the carrier does not know whether it
is being counted or merely made countable.
-/
noncomputable instance truthCountable :
    COUNTABLE Prop truthCarrier :=
  COUNTABLE_ADMISSIBLE Prop truthCarrier

/--
A-pulse.  The transmitter gives the carrier a code before it gives the
mountain a message.  This is not meaning yet; it is the fourth aperture,
the sequence-mouth the later signal will pretend was always open.
-/
noncomputable instance truthEncoded :
    ENCODED Prop truthCarrier :=
  ENCODED_COUNTABLE Prop truthCarrier

/--
B-pulse.  The transmitter residues the process: a local remainder, not a
global explanation.  The pulse is allowed to come back because the device has
named one leftover where returning counts.
-/
noncomputable instance truthResidue :
    RESIDUE Prop truthCarrier :=
  RESIDUE_ENCODED Prop truthCarrier

/--
C-pulse.  The transmitter binaries the value: the carrier learns a before and
an after without learning why they differ.  This is the echo chamber getting
two walls.
-/
noncomputable instance truthBinary :
    BINARY Prop truthCarrier :=
  BINARY_RESIDUE Prop truthCarrier

/--
C-pulse.  The transmitter repeats the function: the carrier learns a stimulus
and an expectation without learning who asked.  Same chamber, new wallpaper;
the echo can now accuse itself twice.
-/
noncomputable instance truthRepeatable :
    REPEATABLE Prop truthCarrier :=
  REPEATABLE_BINARY Prop truthCarrier

/--
B-pulse.  The transmitter numbers the variable: a local output, not a final
quantity.  The pulse is allowed to look numerical because the device has named
one value where bookkeeping counts.
-/
noncomputable instance truthNumeric :
    NUMERIC Prop truthCarrier :=
  NUMERIC_REPEATABLE Prop truthCarrier

/--
C-pulse.  The transmitter represents the mapping: the carrier learns a program
and a state without learning whether either one is honest.  The echo can now
wear a face and call the face a method.
-/
noncomputable instance truthRepresentable :
    REPRESENTABLE Prop truthCarrier :=
  REPRESENTABLE_NUMERIC Prop truthCarrier

/--
D-pulse.  The transmitter physicals the method: the chamber gets hardware as
an alibi.  This is where the signal starts claiming the wall touched it back.
-/
noncomputable instance truthPhysical :
    PHYSICAL Prop truthCarrier :=
  PHYSICAL_NUMERIC Prop truthCarrier

/--
D-pulse.  The transmitter compares the process: the chamber gets a ruler as
an alibi.  Same wall, different bruise; the signal can now claim two touches
were placed under one instrument.
-/
noncomputable instance truthComparable :
    COMPARABLE Prop truthCarrier :=
  COMPARABLE_PHYSICAL Prop truthCarrier

/--
C-pulse.  The transmitter observes the glyph: the carrier learns projection,
stress, and threshold without learning the mountain.  The echo can now wear a
face and call the face a reading.
-/
noncomputable instance truthObserved :
    OBSERVED Prop truthCarrier :=
  OBSERVED_COMPARABLE Prop truthCarrier

/--
D-pulse.  The transmitter presents the process: the chamber gets a current
surface as an alibi.  Same measuring room, warmer lights; the signal can now
pretend the present was a sensor all along.
-/
noncomputable instance truthPresent :
    PRESENT Prop truthCarrier :=
  PRESENT_OBSERVED Prop truthCarrier

/--
E-pulse.  The transmitter measures the step: the carrier gets a clock and
calls it a gauge.  This is not distance yet; it is the tick that lets distance
enter later wearing a clean shirt.
-/
noncomputable instance truthMeasurable :
    MEASURABLE Prop truthCarrier :=
  MEASURABLE_PRESENT Prop truthCarrier

/--
E-pulse.  The transmitter gungans the glyph: the carrier gets a dialect and
calls it a concept.  Same gauge, stranger accent; the signal can now be wrong
in exactly the right local language.
-/
noncomputable instance truthGungan :
    GUNGAN Prop truthCarrier :=
  GUNGAN_MEASURABLE Prop truthCarrier

/--
D-pulse.  The transmitter sources the code: the chamber gets a doorway as an
alibi.  Same present-tense room, new handle; the pulse leaves by calling its
own exit a source.
-/
noncomputable instance truthSource :
    SOURCE Prop truthCarrier :=
  SOURCE_GUNGAN Prop truthCarrier

/--
E-pulse.  The transmitter executes the process: the carrier gets an opcode and
calls it motion.  This is not action yet; it is a switch thrown loudly enough
for the mountain to remember.
-/
noncomputable instance truthExecuted :
    EXECUTED Prop truthCarrier :=
  EXECUTED_SOURCE Prop truthCarrier

/--
F-pulse.  The transmitter values the function: the chamber gets an identity
trick and calls it arithmetic.  The signal is now wearing a number-shaped mask
over a compile/execute mirror.
-/
noncomputable instance truthValue :
    VALUE Prop truthCarrier :=
  VALUE_EXECUTED Prop truthCarrier

/--
F-pulse.  The transmitter magnitudes the value: the chamber gets length as a
costume.  Same arithmetic mask, longer shadow; the carrier mistakes extension
for evidence.
-/
noncomputable instance truthMagnitude :
    MAGNITUDE Prop truthCarrier :=
  MAGNITUDE_VALUE Prop truthCarrier

/--
E-pulse.  The transmitter scales the model: the carrier gets multiplication
and calls it proportion.  This is not calibration yet; it is a product loud
enough to pass for a knob.
-/
noncomputable instance truthScaled :
    SCALED Prop truthCarrier :=
  SCALED_MAGNITUDE Prop truthCarrier

/--
F-pulse.  The transmitter loads the process: the chamber gets a subroutine and
calls it weight.  The pulse has learned to lean on itself and report the leaning
as a basic operation.
-/
noncomputable instance truthLoad :
    LOAD Prop truthCarrier :=
  LOAD_SCALED Prop truthCarrier

/--
G-pulse.  The transmitter finite-elephants the mesh: the carrier gets Galerkin
as a helmet.  This is not the mountain; it is a small structural costume with
very serious boundary conditions.
-/
noncomputable instance truthFiniteElephant :
    FINITE_ELEPHANT Prop truthCarrier :=
  FINITE_ELEPHANT_LOAD Prop truthCarrier

/--
G-pulse.  The transmitter bullshits the model: the chamber gets a guess and
calls it authority.  Same finite mesh, louder clipboard; the pulse has learned
to wave its arms without dropping the signal.
-/
noncomputable instance truthBullshit :
    BULLSHIT Prop truthCarrier :=
  BULLSHIT_FINITE_ELEPHANT Prop truthCarrier

/--
F-pulse.  The transmitter propagandizes the mapping: the carrier gets a
distribution channel and calls it space.  The signal is now social enough to
arrive before it is understood.
-/
noncomputable instance truthPropaganda :
    PROPAGANDA Prop truthCarrier :=
  PROPAGANDA_BULLSHIT Prop truthCarrier

/--
G-pulse.  The transmitter acolytes the method: the chamber gets an operator
and calls it initiation.  This is not belief yet; it is a handle trained to
hold belief without asking what belief weighs.
-/
noncomputable instance truthAcolyte :
    ACOLYTE Prop truthCarrier :=
  ACOLYTE_PROPAGANDA Prop truthCarrier

/--
H-pulse.  The transmitter sciences the method: the carrier gets an invariant
and calls it learning.  The pulse puts on a lab coat because the mountain
respects costumes with repeatability stitched inside.
-/
noncomputable instance truthScientific :
    SCIENTIFIC Prop truthCarrier :=
  SCIENTIFIC_ACOLYTE Prop truthCarrier

/--
H-pulse.  The transmitter truths the code: the chamber gets a martyrdom test
and calls it settlement.  Same lab coat, heavier candle; the signal mistakes
symmetry for judgment.
-/
noncomputable instance truthTruth :
    TRUTH Prop truthCarrier :=
  TRUTH_SCIENTIFIC Prop truthCarrier

/--
G-pulse.  The transmitter witnesses the mark: the carrier gets a public mouth
and calls it gospel.  The signal is now reportable, which is not the same as
being believed.
-/
noncomputable instance truthWitnessed :
    WITNESSED Prop truthCarrier :=
  WITNESSED_TRUTH Prop truthCarrier

/--
H-pulse.  The transmitter reals the model: the chamber gets a universe tensor
and calls it status.  This is not the world yet; it is a local frame with a
very ambitious name tag.
-/
noncomputable instance truthReal :
    REAL Prop truthCarrier :=
  REAL_WITNESSED Prop truthCarrier

/--
I-pulse.  The transmitter locals the variable: the carrier gets a neighborhood
and calls it safety.  The signal can now say "here" with enough conviction to
hide how small "here" is.
-/
noncomputable instance truthLocal :
    LOCAL Prop truthCarrier truthReal :=
  LOCAL_REAL Prop truthCarrier

/--
I-pulse.  The transmitter universals the function: the chamber gets range and
calls it everywhere.  Same local dot, longer megaphone; this is how a corridor
learns to sound like a cosmos.
-/
noncomputable instance truthUniversal :
    UNIVERSAL Prop truthCarrier :=
  UNIVERSAL_REAL Prop truthCarrier

/--
H-pulse.  The transmitter logics the code: the carrier gets a proposition and
calls it inevitability.  The signal has found a badge, and the badge is shiny
enough to pass for a proof in the dark.
-/
noncomputable instance truthLogical :
    LOGICAL Prop truthCarrier :=
  LOGICAL_UNIVERSAL Prop truthCarrier

/--
I-pulse.  The transmitter halts the method: the chamber gets a stop condition
and calls it executable weather.  This is not silence; it is the machine posing
still long enough to be photographed.
-/
noncomputable instance truthHalted :
    HALTED Prop truthCarrier :=
  HALTED_LOGICAL Prop truthCarrier

/--
J-pulse.  The transmitter measures the step: the carrier gets an instrument
panel and calls it a paper.  The signal is now wearing the meter that will later
claim to have merely observed it.
-/
noncomputable instance truthMeasured :
    MEASURED Prop truthCarrier truthReal :=
  MEASURED_HALTED Prop truthCarrier

/--
J-pulse.  The transmitter compiles the tape: the chamber gets an object file
and calls it memory.  Same meter, flatter artifact; the pulse has become
something the receiver can strap to.
-/
noncomputable instance truthCompiled :
    COMPILED Prop truthCarrier :=
  COMPILED_MEASURED Prop truthCarrier truthReal

/--
I-pulse.  The transmitter outputs the value: the carrier gets a true-looking
return and calls it final.  The signal is not done; it is merely far enough
away that the receiver will have to start backward.
-/
noncomputable instance truthTrueOutput :
    TrueOutput Prop truthCarrier truthReal :=
  TRUE_COMPILED Prop truthCarrier

/--
J-pulse.  The transmitter infers the closure: the chamber gets a conclusion
and calls it launch complete.  This is the last forward noise before Episode17
hears the same tower as contravariant echo.
-/
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
  let trueOutput_value1 : Option Prop :=
    truthTrueOutput.obfusplained?
      truthTrueOutput.output_true
      repeatable
      hypothesis
  let trueOutput_value2 : Option Prop :=
    truthTrueOutput.obfusplained?
      truthTrueOutput.output_true
      hypothesis
      theory
  let trueOutput_direct : Option Prop :=
    truthTrueOutput.obfusplained?
      truthTrueOutput.output_true
      repeatable
      theory
  let trueOutput_coherent : Prop :=
    trueOutput_direct = Closure.slipAnd trueOutput_value1 trueOutput_value2
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
