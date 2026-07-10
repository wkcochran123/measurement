import Measurement.Episode78

set_option maxHeartbeats 4000000
set_option maxRecDepth 1000
set_option allowUnsafeReducibility true

namespace Measurement

/-!
__EPISODE 79__: _Close INFERRED_

The binary split has already been carried through the Episode16 tower.  This
episode names that tower one last time and closes it at the final
proof-language target:

* binary is the first post-residue read;
* the tower climbs through repeatable, numeric, physical, measured, compiled,
  and `TrueOutput`;
* `INFERRED` is the closure calculus over that compiled output;
* the last sentence is the `succ_succ` sentence from Episode77;
* false is the closed `Fact.FALSE` zero-strain residue from Episode78;
* true is the distinguished nonzero obstruction read.

This is the final local close: binary has become an inferred closure, and the
outside read separates that closure from the zero-strain false residue.
-/

/-- Names for the explicit Episode16 tower from the binary read to
`INFERRED`.  The class instances themselves carry a long universe braid, so the
closeout records the stable rung names and keeps the proof obligation at the
closure target. -/
inductive BinaryToInferredRung where
  | binary
  | repeatable
  | numeric
  | representable
  | physical
  | comparable
  | observed
  | present
  | measurable
  | gungan
  | source
  | executed
  | value
  | magnitude
  | scaled
  | load
  | finiteElephant
  | bullshit
  | propaganda
  | acolyte
  | scientific
  | truth
  | witnessed
  | real
  | local
  | universal
  | logical
  | halted
  | measured
  | compiled
  | trueOutput
  | inferred

/-- The written tower, from binary to inferred, in Episode16 order. -/
def binaryToInferredStages : List BinaryToInferredRung :=
  [.binary,
    .repeatable,
    .numeric,
    .representable,
    .physical,
    .comparable,
    .observed,
    .present,
    .measurable,
    .gungan,
    .source,
    .executed,
    .value,
    .magnitude,
    .scaled,
    .load,
    .finiteElephant,
    .bullshit,
    .propaganda,
    .acolyte,
    .scientific,
    .truth,
    .witnessed,
    .real,
    .local,
    .universal,
    .logical,
    .halted,
    .measured,
    .compiled,
    .trueOutput,
    .inferred]

/-- The explicit Episode16 tower as a named finite sequence. -/
structure BinaryToInferredTower where
  first : BinaryToInferredRung
  stages : List BinaryToInferredRung
  last : BinaryToInferredRung
  starts_at_binary : first = .binary
  closes_at_inferred : last = .inferred

/-- The concrete truth-carrier tower as named rungs. -/
def truthBinaryToInferredTower :
    BinaryToInferredTower where
  first := .binary
  stages := binaryToInferredStages
  last := .inferred
  starts_at_binary := rfl
  closes_at_inferred := rfl

theorem truthBinaryToInferredTower_starts :
    truthBinaryToInferredTower.first = BinaryToInferredRung.binary :=
  truthBinaryToInferredTower.starts_at_binary

theorem truthBinaryToInferredTower_closes :
    truthBinaryToInferredTower.last = BinaryToInferredRung.inferred :=
  truthBinaryToInferredTower.closes_at_inferred

/-- The final target is explicitly an inferred closure over the first
distinguished target. -/
theorem finalGodelTarget_is_inferred :
    secondGodelProofLanguageSentence.target =
      Closure.inferred.{0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0}
        godelProofLanguageFact
        godelProofLanguageFact
        godelProofLanguageOrigin
        godelProofLanguageOutput
        godelProofLanguageRelation
        godelProofLanguageTarget := rfl

/-- The final source is the first distinguished target. -/
theorem finalGodelSource_is_previous_target :
    secondGodelProofLanguageSentence.source = godelProofLanguageTarget := rfl

/-- The final sentence is closed: what it encodes is exactly its inferred
target. -/
theorem finalGodelSentence_encoded_by_inferred :
    secondGodelProofLanguageSentence.encoded =
      secondGodelProofLanguageSentence.target :=
  secondGodelProofLanguageSentence_encoded_by_target

/-- One compact receipt for the final close. -/
structure FinalInferredClose where
  tower : BinaryToInferredTower
  sentence : ProofLanguageSentence
  distinguished : DISTINGUISHED sentence threeRungNavierStokesResidue
  source_is_previous :
    sentence.source = godelProofLanguageTarget
  target_is_inferred :
    sentence.target =
      Closure.inferred.{0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0}
        godelProofLanguageFact
        godelProofLanguageFact
        godelProofLanguageOrigin
        godelProofLanguageOutput
        godelProofLanguageRelation
        godelProofLanguageTarget
  encoded_by_inferred :
    sentence.encoded = sentence.target
  says_internal_order :
    sentence.says =
      Closure.le.{0, 0, 0, 0} sentence.source sentence.target
  false_is_zero_strain :
    zeroStrainResidue.fact = Fact.FALSE ∧
      zeroStrainResidue.strain = 0 ∧
        zeroStrainResidue.signal = BoundarySignal.off
  true_is_not_false :
    Distinguished.trueRead distinguished ≠
      Distinguished.falseRead distinguished
  obstruction_error_code :
    distinguished.obstruction.errorCode = -1
  outside_on :
    distinguished.outside = BoundarySignal.on

/-- The final closed inferred receipt. -/
noncomputable def FINAL_INFERRED_CLOSE :
    FinalInferredClose where
  tower := truthBinaryToInferredTower
  sentence := secondGodelProofLanguageSentence
  distinguished := SECOND_DISTINGUISHED_GODEL_SENTENCE
  source_is_previous := finalGodelSource_is_previous_target
  target_is_inferred := finalGodelTarget_is_inferred
  encoded_by_inferred := finalGodelSentence_encoded_by_inferred
  says_internal_order := secondGodelProofLanguageSentence_says_internal_order
  false_is_zero_strain := Fact_FALSE_is_zero_strain_residue
  true_is_not_false :=
    second_distinguished_true_neq_false
  obstruction_error_code :=
    second_distinguished_navierStokes_errorCode
  outside_on :=
    second_distinguished_boundary_signal_on

/-- The last theorem: the binary tower has reached `INFERRED`, the final
proof-language sentence is an inferred closure, its encoded form is closed at
that target, and the outside distinguished read is separated from the
`Fact.FALSE` zero-strain residue. -/
theorem inferred_closed_for_the_last_time :
    truthBinaryToInferredTower.first = BinaryToInferredRung.binary ∧
      truthBinaryToInferredTower.last = BinaryToInferredRung.inferred ∧
      secondGodelProofLanguageSentence.source = godelProofLanguageTarget ∧
      secondGodelProofLanguageSentence.target =
        Closure.inferred.{0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0}
          godelProofLanguageFact
          godelProofLanguageFact
          godelProofLanguageOrigin
          godelProofLanguageOutput
          godelProofLanguageRelation
          godelProofLanguageTarget ∧
      secondGodelProofLanguageSentence.encoded =
        secondGodelProofLanguageSentence.target ∧
      secondGodelProofLanguageSentence.says =
        Closure.le.{0, 0, 0, 0}
          secondGodelProofLanguageSentence.source
          secondGodelProofLanguageSentence.target ∧
      zeroStrainResidue.fact = Fact.FALSE ∧
      zeroStrainResidue.strain = 0 ∧
      zeroStrainResidue.signal = BoundarySignal.off ∧
      Distinguished.trueRead SECOND_DISTINGUISHED_GODEL_SENTENCE ≠
        Distinguished.falseRead SECOND_DISTINGUISHED_GODEL_SENTENCE ∧
      SECOND_DISTINGUISHED_GODEL_SENTENCE.obstruction.errorCode = -1 ∧
        SECOND_DISTINGUISHED_GODEL_SENTENCE.outside = BoundarySignal.on :=
  ⟨truthBinaryToInferredTower_starts,
    truthBinaryToInferredTower_closes,
    finalGodelSource_is_previous_target,
    finalGodelTarget_is_inferred,
    finalGodelSentence_encoded_by_inferred,
    secondGodelProofLanguageSentence_says_internal_order,
    zeroStrainResidue_fact_false,
    zeroStrainResidue_strain_zero,
    zeroStrainResidue_signal_off,
    second_distinguished_true_neq_false,
    second_distinguished_navierStokes_errorCode,
    second_distinguished_boundary_signal_on⟩

/-
The standing record.
-/

#print axioms truthBinaryToInferredTower
#print axioms finalGodelTarget_is_inferred
#print axioms FINAL_INFERRED_CLOSE
#print axioms inferred_closed_for_the_last_time

end Measurement
