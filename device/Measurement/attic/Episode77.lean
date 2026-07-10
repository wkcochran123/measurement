import Measurement.Episode76

set_option maxHeartbeats 4000000
set_option maxRecDepth 1000
set_option allowUnsafeReducibility true

namespace Measurement

/-!
__EPISODE 77__: _succ_succ_

Episode76 made the first distinguished proof-language sentence.  Counting now
only needs the next one.  We do not prove successor here; Episode60 already
contains the local counting receipt `Natural.succ_succ`.

This episode does the trivial thing on purpose:

* index 0 is the trivial starting point;
* index 1 is the first `DISTINGUISHED` sentence from Episode76;
* index 2 is the next proof-language closure, certified by `succ_succ`;
* the outside obstruction certificate remains the finite
  Einstein-to-Navier-Stokes residue, with error code `-1`.
-/

/-- The trivial zero index of the proof-language sequence. -/
def trivialGodelIndex : Natural :=
  (0 : Natural)

/-- The first nontrivial index: the distinguished sentence from Episode76. -/
def firstGodelIndex : Natural :=
  Natural.succ trivialGodelIndex

/-- The next index, obtained by using the existing successor operation. -/
def secondGodelIndex : Natural :=
  Natural.succ firstGodelIndex

/-- The imported counting receipt.  Godel gives successor; the device only
uses the already-present `succ_succ` certificate. -/
theorem secondGodelIndex_is_succ_succ :
    secondGodelIndex = (2 : Natural) + trivialGodelIndex := by
  exact Natural.succ_succ trivialGodelIndex

/-- The next proof-language target: one more explicit inferred step over the
first distinguished target. -/
def secondGodelProofLanguageTarget : Closure :=
  Closure.inferred.{0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    godelProofLanguageFact
    godelProofLanguageFact
    godelProofLanguageOrigin
    godelProofLanguageOutput
    godelProofLanguageRelation
    godelProofLanguageTarget

/-- The second proof-language sentence in the sequence. -/
noncomputable def secondGodelProofLanguageSentence :
    ProofLanguageSentence where
  source := godelProofLanguageTarget
  target := secondGodelProofLanguageTarget
  encoded := secondGodelProofLanguageTarget
  says := Closure.le.{0, 0, 0, 0}
    godelProofLanguageTarget
    secondGodelProofLanguageTarget

theorem secondGodelProofLanguageSentence_says_internal_order :
    secondGodelProofLanguageSentence.says =
      Closure.le.{0, 0, 0, 0}
        secondGodelProofLanguageSentence.source
        secondGodelProofLanguageSentence.target := rfl

theorem secondGodelProofLanguageSentence_encoded_by_target :
    secondGodelProofLanguageSentence.encoded =
      secondGodelProofLanguageSentence.target := rfl

/-- The second distinguished sentence: same outside obstruction, next internal
proof-language step. -/
noncomputable def SECOND_DISTINGUISHED_GODEL_SENTENCE :
    DISTINGUISHED
      secondGodelProofLanguageSentence
      threeRungNavierStokesResidue where
  obstruction := threeRungNavierStokesResidue.obstruction
  outside := threeRungNavierStokesResidue.obstruction.signal
  says_internal_order :=
    secondGodelProofLanguageSentence_says_internal_order
  encoded_by_target := secondGodelProofLanguageSentence_encoded_by_target
  navierStokes_balance := threeRung_navierStokes_balance
  obstruction_reads_residue :=
    threeRungNavierStokesResidue.obstruction_reads_residue
  outside_reads_obstruction := rfl
  outside_on := threeRung_navierStokes_signal_on

noncomputable instance secondDistinguishedGodelSentence :
    DISTINGUISHED
      secondGodelProofLanguageSentence
      threeRungNavierStokesResidue :=
  SECOND_DISTINGUISHED_GODEL_SENTENCE

theorem second_distinguished_navierStokes_errorCode :
    SECOND_DISTINGUISHED_GODEL_SENTENCE.obstruction.errorCode = -1 := by
  exact threeRung_navierStokes_errorCode

theorem second_distinguished_boundary_signal_on :
    SECOND_DISTINGUISHED_GODEL_SENTENCE.outside = BoundarySignal.on :=
  SECOND_DISTINGUISHED_GODEL_SENTENCE.outside_on

/-- The receipt for "another one": the second distinguished sentence sits at
`succ_succ 0` and reads the same outside obstruction certificate. -/
theorem second_distinguished_godel_sentence_reads_obstruction :
    secondGodelIndex = (2 : Natural) + trivialGodelIndex ∧
      secondGodelProofLanguageSentence.says =
        Closure.le.{0, 0, 0, 0}
          secondGodelProofLanguageSentence.source
          secondGodelProofLanguageSentence.target ∧
      EinsteinFieldEquationsHold
        threeRungGeometricProgram
        threeRungEinsteinBoundaryApproximation.action
        threeRungEinsteinBoundaryApproximation.path
        threeRungEinsteinBoundaryApproximation.variation ∧
      threeRungNavierStokesResidue.boundaryForcing =
        threeRungNavierStokesResidue.transport +
          threeRungNavierStokesResidue.pressure +
            threeRungNavierStokesResidue.viscousBoundaryFlux ∧
      SECOND_DISTINGUISHED_GODEL_SENTENCE.obstruction.errorCode = -1 ∧
        SECOND_DISTINGUISHED_GODEL_SENTENCE.outside = BoundarySignal.on :=
  ⟨secondGodelIndex_is_succ_succ,
    secondGodelProofLanguageSentence_says_internal_order,
    threeRung_einstein_field_equations_hold,
    threeRung_navierStokes_balance,
    second_distinguished_navierStokes_errorCode,
    second_distinguished_boundary_signal_on⟩

/-
The standing record.
-/

#print axioms secondGodelIndex_is_succ_succ
#print axioms SECOND_DISTINGUISHED_GODEL_SENTENCE
#print axioms second_distinguished_godel_sentence_reads_obstruction

end Measurement
