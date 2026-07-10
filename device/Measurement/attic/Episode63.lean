import Measurement.Episode62

namespace Measurement

/-!
Episode 63 makes the finite Cohen ledger explicitly countable: a condition
has a finite atom list, and finite atom lists carry natural-number codes.

This is the constructive side of the "the list remains countable" claim.  It
does not assert a completed continuum enumeration; it records the finite
ledger code that the later closeout can depend on.
-/

namespace SplineAtom

def code (atom : SplineAtom) : Nat :=
  atom.knot * (atom.value + 1) + atom.value

theorem code_witness (atom : SplineAtom) :
    exists code : Nat, atom.code = code := by
  exact ⟨atom.code, rfl⟩

end SplineAtom

def splineAtomListCode : List SplineAtom -> Nat
  | [] => 0
  | atom :: rest => (atom.code + 1) * (splineAtomListCode rest + 1)

theorem splineAtomListCode_witness (atoms : List SplineAtom) :
    exists code : Nat, splineAtomListCode atoms = code := by
  exact ⟨splineAtomListCode atoms, rfl⟩

namespace SplineCondition

def code {epsilon : Nat} (condition : SplineCondition epsilon) : Nat :=
  splineAtomListCode condition.atoms

theorem code_witness {epsilon : Nat}
    (condition : SplineCondition epsilon) :
    exists code : Nat, condition.code = code := by
  exact ⟨condition.code, rfl⟩

end SplineCondition

structure NatEnumerable (A : Type) where
  code : A -> Nat
  every_entry_has_code : forall entry : A, exists n : Nat, code entry = n

def splineCondition_conditions_countable (epsilon : Nat) :
    NatEnumerable (SplineCondition epsilon) where
  code := SplineCondition.code
  every_entry_has_code := by
    intro condition
    exact ⟨SplineCondition.code condition, rfl⟩

theorem splineCondition_countable_ledger (epsilon : Nat) :
    exists _enumeration : NatEnumerable (SplineCondition epsilon), True := by
  exact ⟨splineCondition_conditions_countable epsilon, trivial⟩

theorem finiteCohen_ledger_has_nat_code (epsilon : Nat)
    (condition : SplineCondition epsilon) :
    exists code : Nat,
      (splineCondition_conditions_countable epsilon).code condition = code := by
  exact ⟨(splineCondition_conditions_countable epsilon).code condition, rfl⟩

theorem finiteCohen_countable_up_to_epsilon (epsilon : Nat) :
    (exists _ledger : FiniteCohenUpToEpsilon epsilon, True) /\
    (exists _enumeration : NatEnumerable (SplineCondition epsilon), True) := by
  exact ⟨⟨splineCondition_cohen_up_to_epsilon epsilon, trivial⟩,
    ⟨splineCondition_conditions_countable epsilon, trivial⟩⟩

#print axioms SplineAtom.code_witness
#print axioms splineAtomListCode_witness
#print axioms SplineCondition.code_witness
#print axioms splineCondition_conditions_countable
#print axioms finiteCohen_ledger_has_nat_code
#print axioms finiteCohen_countable_up_to_epsilon

end Measurement
