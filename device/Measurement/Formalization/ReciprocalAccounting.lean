import Measurement.Episode65

set_option autoImplicit false

/-!
# Reciprocal finite accounting

This orphan module records TODO 8.3 as finite apparatus bookkeeping.  It does
not import analytic rationals or reals: the reciprocal residue is represented
by numerator accounting at one fixed positive denominator.
-/

namespace Measurement

structure ReciprocalFiniteIndex where
  count : Nat
  positive : 0 < count

structure UnitFractionLedger where
  numerator : Nat
  denominator : Nat
  denominator_positive : 0 < denominator

namespace ReciprocalFiniteIndex

def naturalCount (i : ReciprocalFiniteIndex) : Natural :=
  Natural.ofNat i.count

theorem naturalCount_canonical (i : ReciprocalFiniteIndex) :
    Natural.Canonical i.naturalCount :=
  Natural.canonical_ofNat i.count

end ReciprocalFiniteIndex

def wholeCountUnit (i : ReciprocalFiniteIndex) : UnitFractionLedger where
  numerator := i.count
  denominator := i.count
  denominator_positive := i.positive

def unresolvedPartScale (i : ReciprocalFiniteIndex) : UnitFractionLedger where
  numerator := 1
  denominator := i.count
  denominator_positive := i.positive

def resolvedComplement (i : ReciprocalFiniteIndex) : UnitFractionLedger where
  numerator := i.count - 1
  denominator := i.count
  denominator_positive := i.positive

theorem resolved_add_unresolved_eq_whole
    (i : ReciprocalFiniteIndex) :
    (resolvedComplement i).numerator + (unresolvedPartScale i).numerator =
      (wholeCountUnit i).numerator := by
  change (i.count - 1) + 1 = i.count
  exact Nat.sub_add_cancel (Nat.succ_le_of_lt i.positive)

inductive TruthParity where
  | same
  | different

inductive AccountingOrientation where
  | covariantWhole
  | contravariantPart

def orientationOfParity : TruthParity -> AccountingOrientation
  | .same => .covariantWhole
  | .different => .contravariantPart

def WholeCountLE (a b : ReciprocalFiniteIndex) : Prop :=
  a.count <= b.count

def UnitPartScaleLE (a b : UnitFractionLedger) : Prop :=
  b.denominator <= a.denominator

theorem whole_count_order_covariant
    {a b : ReciprocalFiniteIndex} (h : WholeCountLE a b) :
    a.count <= b.count :=
  h

theorem whole_order_reverses_unresolved_part
    {a b : ReciprocalFiniteIndex} (h : WholeCountLE a b) :
    UnitPartScaleLE (unresolvedPartScale b) (unresolvedPartScale a) :=
  h

theorem same_truth_parity_selects_whole :
    orientationOfParity .same = .covariantWhole := rfl

theorem different_truth_parity_selects_reciprocal :
    orientationOfParity .different = .contravariantPart := rfl

structure RepresentableReciprocalThreshold where
  denominator : Nat
  positive : 0 < denominator

def unresolvedBelow
    (i : ReciprocalFiniteIndex)
    (threshold : RepresentableReciprocalThreshold) : Prop :=
  threshold.denominator <= i.count

theorem reciprocal_residue_eventually_below
    (threshold : RepresentableReciprocalThreshold) :
    exists N : Nat,
      forall i : ReciprocalFiniteIndex,
        N <= i.count -> unresolvedBelow i threshold := by
  exact ⟨threshold.denominator, by
    intro i h
    exact h⟩

def reciprocalIndexEnumerable : NatEnumerable ReciprocalFiniteIndex where
  code := fun i => i.count
  every_entry_has_code := by
    intro i
    exact ⟨i.count, rfl⟩

theorem reciprocal_index_has_nat_code
    (i : ReciprocalFiniteIndex) :
    exists code : Nat, reciprocalIndexEnumerable.code i = code := by
  exact ⟨i.count, rfl⟩

structure ReciprocalResidueCertificate
    (epsilon : Nat) (i : ReciprocalFiniteIndex) where
  finiteCohen : FiniteCohenCompliantEpsilon epsilon
  accounting_identity :
    (resolvedComplement i).numerator + (unresolvedPartScale i).numerator =
      (wholeCountUnit i).numerator
  generated_residue_closeout :
    GaugeFrechetLinearTermCloses generatedThreeRungQEDProgram /\
      QEDResidueIsMixedPairTerm generatedThreeRungQEDProgram

theorem reciprocal_residue_certificate
    (epsilon : Nat) (i : ReciprocalFiniteIndex) :
    exists _cert : ReciprocalResidueCertificate epsilon i, True := by
  refine ⟨?_, trivial⟩
  exact
    { finiteCohen := splineCondition_finiteCohenCompliant epsilon
      accounting_identity := resolved_add_unresolved_eq_whole i
      generated_residue_closeout :=
        finiteGauge_successor_commutator_residue_theorem }

structure PreHilbertReciprocalEnergyLedger
    {epsilon : Nat} {D : SobolevHilbertDoor}
    (skeleton : FiniteCohenPreHilbertSkeleton epsilon D)
    (i : ReciprocalFiniteIndex) where
  accounting_identity :
    (resolvedComplement i).numerator + (unresolvedPartScale i).numerator =
      (wholeCountUnit i).numerator
  every_condition_coded :
    forall condition : SplineCondition epsilon,
      exists code : Nat, skeleton.enumeration.code condition = code

theorem finiteCohen_preHilbert_reciprocal_energy
    {epsilon : Nat} {D : SobolevHilbertDoor}
    (skeleton : FiniteCohenPreHilbertSkeleton epsilon D)
    (i : ReciprocalFiniteIndex) :
    exists _energy : PreHilbertReciprocalEnergyLedger skeleton i, True := by
  refine ⟨?_, trivial⟩
  exact
    { accounting_identity := resolved_add_unresolved_eq_whole i
      every_condition_coded := skeleton.every_condition_coded }

end Measurement
