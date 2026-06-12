import Measurement.Episode64

namespace Measurement

/-!
Episode 65 opens the Hilbert-completion arc without importing analysis that is
not present in the project.

Episodes38 and 56 already provide the finite Hilbert door: a normed energy
door plus an integer pairing.  Episode64 provides the finite Cohen-compliant
spline ledger and the generated QED residue closeout.  This episode packages
those facts as the conservative interface the continuum theorem will later
consume.

No continuum orthogonality, real Hilbert completion, or standard GR/QED theorem
is claimed here.  The door merely names the obligations and shows that the
finite three-rung object can stand at the entrance.
-/

structure SobolevHilbertDoor where
  H : Type
  completionDoor : HilbertCompletionDoor H
  Pair : Type
  pairZero : Pair
  dotH : H -> H -> Pair
  dotH_symmetric : forall x y, dotH x y = dotH y x
  dotH_zero_left : forall x, dotH completionDoor.cert.zero x = pairZero
  coercive : Prop
  coercive_proof : coercive
  complete : Prop
  complete_proof : complete

namespace SobolevHilbertDoor

def zero (D : SobolevHilbertDoor) : D.H :=
  D.completionDoor.cert.zero

def norm (D : SobolevHilbertDoor) : D.H -> D.completionDoor.scale.R :=
  D.completionDoor.norm

theorem norm_zero (D : SobolevHilbertDoor) :
    D.norm D.zero = D.completionDoor.scale.rzero := by
  unfold norm zero
  rw [D.completionDoor.norm_matches]
  exact realNorm_zero D.completionDoor.scale D.completionDoor.cert

theorem norm_zero_detects (D : SobolevHilbertDoor)
    (x : D.H) (h : D.norm x = D.completionDoor.scale.rzero) :
    x = D.zero := by
  unfold norm at h
  unfold zero
  exact D.completionDoor.norm_zero_detects x h

theorem dot_zero_left (D : SobolevHilbertDoor) (x : D.H) :
    D.dotH D.zero x = D.pairZero := by
  exact D.dotH_zero_left x

def ofPairingDoor {H : Type} (door : HilbertPairingDoor H) :
    SobolevHilbertDoor where
  H := H
  completionDoor := door.toHilbertCompletionDoor
  Pair := Int
  pairZero := 0
  dotH := door.dot
  dotH_symmetric := door.dot_symmetric
  dotH_zero_left := door.dot_zero_left
  coercive :=
    forall x : H,
      door.toHilbertCompletionDoor.norm x =
        door.toHilbertCompletionDoor.scale.rzero ->
          x = door.toHilbertCompletionDoor.cert.zero
  coercive_proof := door.toHilbertCompletionDoor.norm_zero_detects
  complete := door.toHilbertCompletionDoor.completionAvailable
  complete_proof := door.toHilbertCompletionDoor.completionAvailable_proof

end SobolevHilbertDoor

noncomputable def threeRungSobolevHilbertDoor : SobolevHilbertDoor :=
  SobolevHilbertDoor.ofPairingDoor threeRungPairingDoor

structure FiniteCohenPreHilbertSkeleton
    (epsilon : Nat) (D : SobolevHilbertDoor) where
  ledger : FiniteCohenCompliantEpsilon epsilon
  enumeration : NatEnumerable (SplineCondition epsilon)
  embed : SplineCondition epsilon -> D.H
  embed_zero_norm :
    forall condition,
      D.norm (embed condition) = D.completionDoor.scale.rzero
  every_condition_coded :
    forall condition,
      exists code : Nat, enumeration.code condition = code

def zeroFiniteCohenPreHilbertSkeleton
    (epsilon : Nat) (D : SobolevHilbertDoor) :
    FiniteCohenPreHilbertSkeleton epsilon D where
  ledger := splineCondition_finiteCohenCompliant epsilon
  enumeration := splineCondition_conditions_countable epsilon
  embed := fun _ => D.zero
  embed_zero_norm := by
    intro _condition
    exact D.norm_zero
  every_condition_coded := by
    intro condition
    exact finiteCohen_ledger_has_nat_code epsilon condition

structure HilbertCompletionArc where
  epsilon : Nat
  door : SobolevHilbertDoor
  skeleton : FiniteCohenPreHilbertSkeleton epsilon door
  finiteResidue :
    GaugeFrechetLinearTermCloses generatedThreeRungQEDProgram /\
      QEDResidueIsMixedPairTerm generatedThreeRungQEDProgram

noncomputable def threeRungHilbertCompletionArc (epsilon : Nat) :
    HilbertCompletionArc where
  epsilon := epsilon
  door := threeRungSobolevHilbertDoor
  skeleton :=
    zeroFiniteCohenPreHilbertSkeleton epsilon threeRungSobolevHilbertDoor
  finiteResidue := finiteGauge_successor_commutator_residue_theorem

theorem hilbertCompletionArc_setup (epsilon : Nat) :
    exists arc : HilbertCompletionArc, arc.epsilon = epsilon := by
  exact ⟨threeRungHilbertCompletionArc epsilon, rfl⟩

theorem hilbertCompletionArc_has_completion_token (epsilon : Nat) :
    (threeRungHilbertCompletionArc epsilon).door.complete := by
  exact (threeRungHilbertCompletionArc epsilon).door.complete_proof

theorem hilbertCompletionArc_retains_finite_residue (epsilon : Nat) :
    GaugeFrechetLinearTermCloses generatedThreeRungQEDProgram /\
      QEDResidueIsMixedPairTerm generatedThreeRungQEDProgram := by
  exact (threeRungHilbertCompletionArc epsilon).finiteResidue

#print axioms SobolevHilbertDoor.norm_zero
#print axioms SobolevHilbertDoor.norm_zero_detects
#print axioms threeRungSobolevHilbertDoor
#print axioms zeroFiniteCohenPreHilbertSkeleton
#print axioms threeRungHilbertCompletionArc
#print axioms hilbertCompletionArc_setup
#print axioms hilbertCompletionArc_has_completion_token
#print axioms hilbertCompletionArc_retains_finite_residue

end Measurement
