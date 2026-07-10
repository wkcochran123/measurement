import Measurement.Episode77

set_option maxHeartbeats 4000000
set_option maxRecDepth 1000
set_option allowUnsafeReducibility true

namespace Measurement

/-!
__EPISODE 78__: _true neq false_

The distinguished sentence is graded by the outside on/off reader.  Here the
last lock is explicit:

* distinguished true  := the outside signal reads `on`;
* distinguished false := the outside signal reads the `Fact.FALSE`
  zero-strain residue, hence `off`;
* for any `DISTINGUISHED` sentence, true is not false.

This does not re-open Episode16's internal `true_eq_false` joke.  It says the
outside obstruction certificate has separated the two reads.
-/

namespace BoundarySignal

theorem on_ne_off : BoundarySignal.on ≠ BoundarySignal.off := by
  intro h
  cases h

theorem off_ne_on : BoundarySignal.off ≠ BoundarySignal.on := by
  intro h
  cases h

def toBool : BoundarySignal -> Bool
  | .off => false
  | .on => true

theorem toBool_on : BoundarySignal.toBool BoundarySignal.on = true := rfl

theorem toBool_off : BoundarySignal.toBool BoundarySignal.off = false := rfl

end BoundarySignal

namespace Fact

/-- The project-native false fact: the canonical fact carried by the zero
strain residue. -/
def FALSE : Fact where
  truth := false
  decTruth := Decidable.isFalse (by
    intro h
    cases h)

end Fact

/-- The false side of the outside reader is not a nonzero obstruction.  It is
the zero-strain residue, tagged by `Fact.FALSE` and read as `off`. -/
structure BoundaryStrainResidue where
  fact : Fact
  strain : Int
  signal : BoundarySignal
  fact_false : fact = Fact.FALSE
  zero_strain : strain = 0
  signal_off : signal = BoundarySignal.off

/-- The canonical zero-strain residue. -/
def zeroStrainResidue : BoundaryStrainResidue where
  fact := Fact.FALSE
  strain := 0
  signal := BoundarySignal.ofErrorCode 0
  fact_false := rfl
  zero_strain := rfl
  signal_off := BoundarySignal.ofErrorCode_off

theorem zeroStrainResidue_fact_false :
    zeroStrainResidue.fact = Fact.FALSE :=
  zeroStrainResidue.fact_false

theorem zeroStrainResidue_strain_zero :
    zeroStrainResidue.strain = 0 :=
  zeroStrainResidue.zero_strain

theorem zeroStrainResidue_signal_off :
    zeroStrainResidue.signal = BoundarySignal.off :=
  zeroStrainResidue.signal_off

theorem Fact_FALSE_is_zero_strain_residue :
    zeroStrainResidue.fact = Fact.FALSE ∧
      zeroStrainResidue.strain = 0 ∧
        zeroStrainResidue.signal = BoundarySignal.off :=
  ⟨zeroStrainResidue_fact_false,
    zeroStrainResidue_strain_zero,
    zeroStrainResidue_signal_off⟩

namespace Distinguished

def trueRead
    {sentence : ProofLanguageSentence} {residue : FiniteNavierStokesResidue}
    (D : DISTINGUISHED sentence residue) : Prop :=
  D.outside = BoundarySignal.on

def falseRead
    {sentence : ProofLanguageSentence} {residue : FiniteNavierStokesResidue}
    (D : DISTINGUISHED sentence residue) : Prop :=
  D.outside = zeroStrainResidue.signal

theorem falseRead_zero_strain
    {sentence : ProofLanguageSentence} {residue : FiniteNavierStokesResidue}
    (D : DISTINGUISHED sentence residue) :
    falseRead D -> zeroStrainResidue.fact = Fact.FALSE ∧
        zeroStrainResidue.strain = 0 ∧
          zeroStrainResidue.signal = BoundarySignal.off := by
  intro _
  exact Fact_FALSE_is_zero_strain_residue

def truthBit
    {sentence : ProofLanguageSentence} {residue : FiniteNavierStokesResidue}
    (D : DISTINGUISHED sentence residue) : Bool :=
  D.outside.toBool

theorem truthBit_true
    {sentence : ProofLanguageSentence} {residue : FiniteNavierStokesResidue}
    (D : DISTINGUISHED sentence residue) :
    truthBit D = true := by
  unfold truthBit
  rw [D.outside_on]
  exact BoundarySignal.toBool_on

theorem truthBit_neq_false
    {sentence : ProofLanguageSentence} {residue : FiniteNavierStokesResidue}
    (D : DISTINGUISHED sentence residue) :
    truthBit D ≠ false := by
  rw [truthBit_true D]
  decide

/-- The final outside-reader separation: distinguished true is not
distinguished false. -/
theorem true_neq_false
    {sentence : ProofLanguageSentence} {residue : FiniteNavierStokesResidue}
    (D : DISTINGUISHED sentence residue) :
    trueRead D ≠ falseRead D := by
  intro h
  have hFalse : falseRead D := Eq.mp h D.outside_on
  unfold falseRead at hFalse
  rw [zeroStrainResidue_signal_off] at hFalse
  exact BoundarySignal.on_ne_off (D.outside_on.symm.trans hFalse)

end Distinguished

theorem first_distinguished_true_neq_false :
    Distinguished.trueRead DISTINGUISHED_GODEL_SENTENCE ≠
      Distinguished.falseRead DISTINGUISHED_GODEL_SENTENCE :=
  Distinguished.true_neq_false DISTINGUISHED_GODEL_SENTENCE

theorem second_distinguished_true_neq_false :
    Distinguished.trueRead SECOND_DISTINGUISHED_GODEL_SENTENCE ≠
      Distinguished.falseRead SECOND_DISTINGUISHED_GODEL_SENTENCE :=
  Distinguished.true_neq_false SECOND_DISTINGUISHED_GODEL_SENTENCE

theorem distinguished_sequence_true_neq_false :
    Distinguished.trueRead DISTINGUISHED_GODEL_SENTENCE ≠
        Distinguished.falseRead DISTINGUISHED_GODEL_SENTENCE ∧
      Distinguished.trueRead SECOND_DISTINGUISHED_GODEL_SENTENCE ≠
        Distinguished.falseRead SECOND_DISTINGUISHED_GODEL_SENTENCE :=
  ⟨first_distinguished_true_neq_false,
    second_distinguished_true_neq_false⟩

/-
The standing record.
-/

#print axioms BoundarySignal.on_ne_off
#print axioms Fact_FALSE_is_zero_strain_residue
#print axioms Distinguished.falseRead_zero_strain
#print axioms Distinguished.truthBit_neq_false
#print axioms Distinguished.true_neq_false
#print axioms distinguished_sequence_true_neq_false

end Measurement
