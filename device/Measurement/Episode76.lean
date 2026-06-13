import Measurement.Episode75

set_option maxHeartbeats 4000000
set_option maxRecDepth 1000
set_option allowUnsafeReducibility true

namespace Measurement

/-!
__EPISODE 76__: _DISTINGUISHED_

Episode75 exposed the outside-world obstruction as an error code read by a
simple on/off apparatus.  This episode ties that outside read back to the
post-Episode16 proof language.

The point is intentionally finite and project-native.  We are not claiming
Lean has proved the classical metatheorem about Godel sentences.  We are
recording the sentence this device can actually form:

* inside, the proof language carries a concrete `Closure` sentence in the
  normal form of the Episode16 `truthInferred` stack;
* outside, the generated Einstein-boundary approximation leaves the
  Navier-Stokes-shaped residue;
* the obstruction certificate is the error code, and the outside reader sees
  it as `BoundarySignal.on`.

That is the new capstone word: `DISTINGUISHED`.
-/

/-- The internal proof-language carrier.  It is deliberately small: a source
closure, a target closure, an encoded closure, and the proposition the internal
language says about them. -/
structure ProofLanguageSentence where
  source : Closure
  target : Closure
  encoded : Closure
  says : Prop

/-- The proof-language fact used by the concrete Godel sentence. -/
def godelProofLanguageFact : Fact :=
  truthCarrier.symbol

/-- The origin rung of the proof-language sentence. -/
def godelProofLanguageOrigin : Bullshit :=
  Bullshit.zero.{0, 0, 0, 0} godelProofLanguageFact

/-- The finite encoded output rung.  This is the one-step normal form of the
Episode16 `TrueOutput` hypothesis rung, written directly so no polymorphic
instance tower leaks universe metavariables into the capstone. -/
def godelProofLanguageOutput : Bullshit :=
  Bullshit.one.{0, 0, 0, 0}
    godelProofLanguageFact
    truthCarrier.value
    (CompilerTape.boot.{0} Fact.Truth Prop)
    (CompilerTape.boot.{0} Fact.Truth Prop)
    godelProofLanguageOrigin

/-- The proof-language relation carried by the closure. -/
def godelProofLanguageRelation : Prop :=
  True

/-- The source closure of the sentence. -/
def godelProofLanguageSource : Closure :=
  Closure.different.{0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    godelProofLanguageFact
    godelProofLanguageOrigin
    godelProofLanguageOutput
    godelProofLanguageRelation

/-- The target closure of the sentence: one explicit inferred step over its
own source closure. -/
def godelProofLanguageTarget : Closure :=
  Closure.inferred.{0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    godelProofLanguageFact
    godelProofLanguageFact
    godelProofLanguageOrigin
    godelProofLanguageOutput
    godelProofLanguageRelation
    godelProofLanguageSource

/-- The project-native Godel sentence: the proof language reads its own source
closure against the accumulated target closure. -/
noncomputable def godelProofLanguageSentence : ProofLanguageSentence where
  source := godelProofLanguageSource
  target := godelProofLanguageTarget
  encoded := godelProofLanguageTarget
  says := Closure.le.{0, 0, 0, 0}
    godelProofLanguageSource
    godelProofLanguageTarget

theorem godelProofLanguageSentence_says_internal_order :
    godelProofLanguageSentence.says =
      Closure.le.{0, 0, 0, 0}
        godelProofLanguageSentence.source
        godelProofLanguageSentence.target := rfl

theorem godelProofLanguageSentence_encoded_by_theory :
    godelProofLanguageSentence.encoded =
      godelProofLanguageSentence.target := rfl

/-- A sentence is `DISTINGUISHED` when the internal proof-language sentence is
paired with a finite boundary residue whose obstruction certificate is visible
to the outside on/off reader. -/
class DISTINGUISHED
    (sentence : ProofLanguageSentence)
    (residue : FiniteNavierStokesResidue) where
  obstruction : BoundaryObstructionCertificate
  outside : BoundarySignal
  says_internal_order :
    sentence.says =
      Closure.le.{0, 0, 0, 0} sentence.source sentence.target
  encoded_by_target : sentence.encoded = sentence.target
  navierStokes_balance :
    residue.boundaryForcing =
      residue.transport + residue.pressure + residue.viscousBoundaryFlux
  obstruction_reads_residue :
    obstruction.errorCode = residue.viscousBoundaryFlux
  outside_reads_obstruction : outside = obstruction.signal
  outside_on : outside = BoundarySignal.on

/-- The concrete distinguished sentence produced by the three-rung
Einstein-boundary approximation. -/
noncomputable def DISTINGUISHED_GODEL_SENTENCE :
    DISTINGUISHED
      godelProofLanguageSentence
      threeRungNavierStokesResidue where
  obstruction := threeRungNavierStokesResidue.obstruction
  outside := threeRungNavierStokesResidue.obstruction.signal
  says_internal_order := godelProofLanguageSentence_says_internal_order
  encoded_by_target := godelProofLanguageSentence_encoded_by_theory
  navierStokes_balance := threeRung_navierStokes_balance
  obstruction_reads_residue :=
    threeRungNavierStokesResidue.obstruction_reads_residue
  outside_reads_obstruction := rfl
  outside_on := threeRung_navierStokes_signal_on

noncomputable instance distinguishedGodelSentence :
    DISTINGUISHED
      godelProofLanguageSentence
      threeRungNavierStokesResidue :=
  DISTINGUISHED_GODEL_SENTENCE

theorem distinguished_navierStokes_errorCode :
    DISTINGUISHED_GODEL_SENTENCE.obstruction.errorCode = -1 := by
  exact threeRung_navierStokes_errorCode

theorem distinguished_boundary_signal_on :
    DISTINGUISHED_GODEL_SENTENCE.outside = BoundarySignal.on :=
  DISTINGUISHED_GODEL_SENTENCE.outside_on

/-- The receipt: the internal proof-language sentence and the outside
Einstein-to-Navier-Stokes obstruction are the same distinguished capstone. -/
theorem distinguished_godel_sentence_reads_obstruction :
    godelProofLanguageSentence.says =
        Closure.le.{0, 0, 0, 0}
          godelProofLanguageSentence.source
          godelProofLanguageSentence.target ∧
      EinsteinFieldEquationsHold
        threeRungGeometricProgram
        threeRungEinsteinBoundaryApproximation.action
        threeRungEinsteinBoundaryApproximation.path
        threeRungEinsteinBoundaryApproximation.variation ∧
      threeRungNavierStokesResidue.boundaryForcing =
        threeRungNavierStokesResidue.transport +
          threeRungNavierStokesResidue.pressure +
            threeRungNavierStokesResidue.viscousBoundaryFlux ∧
      DISTINGUISHED_GODEL_SENTENCE.obstruction.errorCode = -1 ∧
        DISTINGUISHED_GODEL_SENTENCE.outside = BoundarySignal.on :=
  ⟨godelProofLanguageSentence_says_internal_order,
    threeRung_einstein_field_equations_hold,
    threeRung_navierStokes_balance,
    distinguished_navierStokes_errorCode,
    distinguished_boundary_signal_on⟩

/-
The standing record.
-/

#print axioms DISTINGUISHED_GODEL_SENTENCE
#print axioms distinguished_godel_sentence_reads_obstruction

end Measurement
