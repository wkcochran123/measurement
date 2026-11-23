/-
The quaternions, with no choice: a pair of complex numbers.

Doubled once more, the way the complex numbers doubled the signed reals.  A quaternion is two complex numbers, a first and
a second.  Each for each: the first by the first, less the second turned across by the second, is the first; the second
by the first and the second by the first turned across is the second.  Doubling this time costs something: the order of
a product.  One quarter turn by another is a third; the other by the one is that third owed.
-/
import Meanings.Complex

namespace Meanings

structure QuaternionReal where
  first : ComplexReal
  second : ComplexReal

namespace QuaternionReal

def ofNat (k : Nat) : QuaternionReal := ⟨ComplexReal.ofNat k, ComplexReal.ofNat 0⟩

instance : Add QuaternionReal := ⟨fun p q => ⟨p.first + q.first, p.second + q.second⟩⟩
instance : Neg QuaternionReal := ⟨fun p => ⟨-p.first, -p.second⟩⟩
instance : Sub QuaternionReal := ⟨fun p q => ⟨p.first - q.first, p.second - q.second⟩⟩
instance : Mul QuaternionReal :=
  ⟨fun p q => ⟨p.first * q.first - q.second.conjugate * p.second, q.second * p.first + p.second * q.first.conjugate⟩⟩

def Same (p q : QuaternionReal) : Prop := p.first.Same q.first ∧ p.second.Same q.second

--| The three quarter turns.
def i : QuaternionReal := ⟨ComplexReal.quarterTurn, ComplexReal.ofNat 0⟩
def j : QuaternionReal := ⟨ComplexReal.ofNat 0, ComplexReal.ofNat 1⟩
def k : QuaternionReal := ⟨ComplexReal.ofNat 0, ComplexReal.quarterTurn⟩

end QuaternionReal

open QuaternionReal

--| Every wall below is a whole number, the same at every stage, so two stages are read alike.  Reading them is long work
--| for the elaborator, which does not keep what it has read, so these are given a larger budget of heartbeats.
macro "read_the_walls" : tactic =>
  `(tactic| (refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> intro _ _ <;>
      exact ⟨Nat.le_of_ble_eq_true rfl, Nat.le_of_ble_eq_true rfl⟩))

--| ONE QUARTER TURN BY ANOTHER IS THE THIRD.
set_option maxHeartbeats 4000000 in
theorem i_by_j_is_k : (i * j).Same k := by read_the_walls
set_option maxHeartbeats 4000000 in
theorem j_by_k_is_i : (j * k).Same i := by read_the_walls
set_option maxHeartbeats 4000000 in
theorem k_by_i_is_j : (k * i).Same j := by read_the_walls

--| THE OTHER BY THE ONE IS THE THIRD OWED.
set_option maxHeartbeats 4000000 in
theorem j_by_i_is_k_owed : (j * i).Same (-k) := by read_the_walls

--| Each, twice, is one owed.
set_option maxHeartbeats 4000000 in
theorem i_twice_is_one_owed : (i * i).Same (-ofNat 1) := by read_the_walls
set_option maxHeartbeats 4000000 in
theorem j_twice_is_one_owed : (j * j).Same (-ofNat 1) := by read_the_walls
set_option maxHeartbeats 4000000 in
theorem k_twice_is_one_owed : (k * k).Same (-ofNat 1) := by read_the_walls

--| AND THE ORDER IS SEEN.  The one by the other is not the other by the one: at the first stage, the second's across of the
--| one is past the other's by two.
theorem i_by_j_is_not_j_by_i : ¬ (i * j).Same (j * i) := fun h =>
  absurd (h.2.2 0 0).1 (by decide +kernel)

end Meanings
