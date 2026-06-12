import Measurement.Episode61

namespace Measurement

/-!
Episode 62 records the order that was implicit in the finite Cohen ledger.
The conditions themselves carry proof fields, so the order is closed only up
to the extensional equality of their atom lists.
-/

namespace SplineCondition

def SameAtoms {epsilon : Nat} (left right : SplineCondition epsilon) : Prop :=
  forall atom : SplineAtom, atom ∈ left.atoms <-> atom ∈ right.atoms

theorem sameAtoms_refl {epsilon : Nat} (condition : SplineCondition epsilon) :
    SameAtoms condition condition := by
  intro atom
  exact Iff.rfl

theorem sameAtoms_symm {epsilon : Nat} {left right : SplineCondition epsilon}
    (h : SameAtoms left right) : SameAtoms right left := by
  intro atom
  exact (h atom).symm

theorem sameAtoms_trans {epsilon : Nat} {a b c : SplineCondition epsilon}
    (hab : SameAtoms a b) (hbc : SameAtoms b c) : SameAtoms a c := by
  intro atom
  exact Iff.trans (hab atom) (hbc atom)

theorem sameAtoms_of_extends_both {epsilon : Nat} {left right : SplineCondition epsilon}
    (hlr : Extends left right) (hrl : Extends right left) :
    SameAtoms left right := by
  intro atom
  exact ⟨fun h => hrl atom h, fun h => hlr atom h⟩

theorem sameAtoms_extends_left {epsilon : Nat} {left right : SplineCondition epsilon}
    (h : SameAtoms left right) : Extends left right := by
  intro atom hmem
  exact (h atom).2 hmem

theorem sameAtoms_extends_right {epsilon : Nat} {left right : SplineCondition epsilon}
    (h : SameAtoms left right) : Extends right left := by
  intro atom hmem
  exact (h atom).1 hmem

theorem merge_extensional_comm {epsilon : Nat} (left right : SplineCondition epsilon) :
    SameAtoms (merge left right) (merge right left) := by
  intro atom
  constructor
  · intro hmem
    simp [merge] at hmem ⊢
    exact hmem.symm
  · intro hmem
    simp [merge] at hmem ⊢
    exact hmem.symm

end SplineCondition

structure ExtensionalConditionOrder (epsilon : Nat) where
  le : SplineCondition epsilon -> SplineCondition epsilon -> Prop
  equiv : SplineCondition epsilon -> SplineCondition epsilon -> Prop
  refl : forall condition, le condition condition
  trans : forall a b c, le a b -> le b c -> le a c
  antisymm :
    forall a b, le a b -> le b a -> equiv a b
  equiv_refl : forall condition, equiv condition condition
  equiv_symm : forall a b, equiv a b -> equiv b a
  equiv_trans : forall a b c, equiv a b -> equiv b c -> equiv a c
  merge :
    forall left right,
      le (SplineCondition.merge left right) left /\
      le (SplineCondition.merge left right) right
  merge_comm :
    forall left right,
      equiv (SplineCondition.merge left right) (SplineCondition.merge right left)
  dense_decides :
    forall condition knot,
      knot <= epsilon ->
        exists stronger,
          le stronger condition /\ SplineCondition.Decides stronger knot

def splineCondition_extensional_order (epsilon : Nat) :
    ExtensionalConditionOrder epsilon where
  le := SplineCondition.Extends
  equiv := SplineCondition.SameAtoms
  refl := SplineCondition.extends_refl
  trans := by
    intro a b c hab hbc
    exact SplineCondition.extends_trans hab hbc
  antisymm := by
    intro a b hab hba
    exact SplineCondition.sameAtoms_of_extends_both hab hba
  equiv_refl := SplineCondition.sameAtoms_refl
  equiv_symm := by
    intro a b h
    exact SplineCondition.sameAtoms_symm h
  equiv_trans := by
    intro a b c hab hbc
    exact SplineCondition.sameAtoms_trans hab hbc
  merge := by
    intro left right
    exact ⟨SplineCondition.merge_extends_left left right,
      SplineCondition.merge_extends_right left right⟩
  merge_comm := SplineCondition.merge_extensional_comm
  dense_decides := by
    intro condition knot hbound
    exact SplineCondition.dense_decides_knot condition knot hbound

theorem splineCondition_order_up_to_extensionality (epsilon : Nat) :
    exists _order : ExtensionalConditionOrder epsilon, True := by
  exact ⟨splineCondition_extensional_order epsilon, trivial⟩

#print axioms SplineCondition.sameAtoms_of_extends_both
#print axioms SplineCondition.merge_extensional_comm
#print axioms splineCondition_extensional_order
#print axioms splineCondition_order_up_to_extensionality

end Measurement
