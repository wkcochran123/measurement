/-
The baker's transform, on records.

A record of a number between nothing and one is its cut at every halving: nothing at first, and then twice the cut before
or twice and one more.  Halving reads a new bit from outside.  Its reciprocal is doubling: read the top bit off the record,
take it away, and what is left is the record of twice the number, wrapped round.  Doubling alone forgets the bit it read:
two records that differ only there double to one.  The baker keeps it: it stretches the one record and lays the bit it
read on top of a second, which it halves.  Run backward, the baker takes the bit back off the second record and lays it
under the first.  So the pair goes there and back exactly; the first record alone does not.
-/
import Meanings.Correspondence
import Meanings.Real

namespace Meanings

--| A RECORD OF A NUMBER BETWEEN NOTHING AND ONE.  Nothing at first; then twice, or twice and one more.
structure UnitCut where
  cut : Nat → Nat
  doubles : ∀ n, 2 * cut n ≤ cut (n + 1) ∧ cut (n + 1) ≤ 2 * cut n + 1
  starts : cut 0 = 0

namespace UnitCut

theorem ext {x y : UnitCut} (h : ∀ n, x.cut n = y.cut n) : x = y := by
  cases x with
  | mk c d s => cases y with
    | mk c' d' s' =>
      have e : c = c' := funext h
      subst e; rfl

def toDyadic (x : UnitCut) : DyadicCut := ⟨x.cut, x.doubles⟩

--| The top bit: the first halving's cut, nothing or one.
theorem top_le (x : UnitCut) : x.cut 1 ≤ 1 := by
  have d := (x.doubles 0).2; have s := x.starts; rw [s] at d; exact d

theorem pow_succ_two (n : Nat) : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [Nat.pow_succ, Nat.mul_comm]

--| The top bit is held all the way down.
theorem top_held (x : UnitCut) : ∀ n, x.cut 1 * 2 ^ n ≤ x.cut (n + 1)
  | 0 => by rw [Nat.pow_zero, Nat.mul_one]; exact Nat.le_refl _
  | n + 1 => by
    have ih := top_held x n
    have d := (x.doubles (n + 1)).1
    rw [pow_succ_two, Nat.mul_left_comm]
    omega

--| DOUBLING.  The top bit taken away, and the rest read one halving sooner.
def doubled (x : UnitCut) : UnitCut where
  cut n := x.cut (n + 1) - x.cut 1 * 2 ^ n
  doubles n := by
    have h0 := top_held x n
    have h1 := top_held x (n + 1)
    have d := x.doubles (n + 1)
    have e : x.cut 1 * 2 ^ (n + 1) = 2 * (x.cut 1 * 2 ^ n) := by rw [pow_succ_two, Nat.mul_left_comm]
    rw [e] at h1 ⊢
    exact ⟨by omega, by omega⟩
  starts := by show x.cut 1 - x.cut 1 * 2 ^ 0 = 0; rw [Nat.pow_zero, Nat.mul_one, Nat.sub_self]

--| HALVING, WITH A BIT GIVEN.  The bit laid on top; the record read one halving later.
def pushed (t : Nat) (ht : t ≤ 1) (y : UnitCut) : UnitCut where
  cut
    | 0 => 0
    | n + 1 => t * 2 ^ n + y.cut n
  doubles
    | 0 => by
      show 2 * 0 ≤ t * 2 ^ 0 + y.cut 0 ∧ t * 2 ^ 0 + y.cut 0 ≤ 2 * 0 + 1
      rw [Nat.pow_zero, Nat.mul_one, y.starts]; exact ⟨by omega, by omega⟩
    | n + 1 => by
      show 2 * (t * 2 ^ n + y.cut n) ≤ t * 2 ^ (n + 1) + y.cut (n + 1)
        ∧ t * 2 ^ (n + 1) + y.cut (n + 1) ≤ 2 * (t * 2 ^ n + y.cut n) + 1
      have d := y.doubles n
      rw [pow_succ_two, Nat.mul_left_comm]
      exact ⟨by omega, by omega⟩
  starts := rfl

theorem pushed_top (t : Nat) (ht : t ≤ 1) (y : UnitCut) : (pushed t ht y).cut 1 = t := by
  show t * 2 ^ 0 + y.cut 0 = t; rw [Nat.pow_zero, Nat.mul_one, y.starts, Nat.add_zero]

--| DOUBLING UNDOES HALVING WITH A BIT.
theorem doubled_pushed (t : Nat) (ht : t ≤ 1) (y : UnitCut) : doubled (pushed t ht y) = y :=
  ext fun n => by
    show (pushed t ht y).cut (n + 1) - (pushed t ht y).cut 1 * 2 ^ n = y.cut n
    rw [pushed_top]; show t * 2 ^ n + y.cut n - t * 2 ^ n = y.cut n; omega

--| HALVING WITH THE TOP BIT UNDOES DOUBLING.
theorem pushed_doubled (x : UnitCut) : pushed (x.cut 1) (top_le x) (doubled x) = x :=
  ext fun n => by
    cases n with
    | zero => exact x.starts.symm
    | succ n =>
      show x.cut 1 * 2 ^ n + (x.cut (n + 1) - x.cut 1 * 2 ^ n) = x.cut (n + 1)
      have := top_held x n; omega

--| DOUBLING FORGETS.  Two records that differ in the top bit alone double to one, and they are not one.
theorem doubling_forgets (z : UnitCut) :
    doubled (pushed 0 (by decide) z) = doubled (pushed 1 (by decide) z) ∧ pushed 0 (by decide) z ≠ pushed 1 (by decide) z := by
  refine ⟨by rw [doubled_pushed, doubled_pushed], fun e => ?_⟩
  have := congrArg (fun x : UnitCut => x.cut 1) e
  simp only [pushed_top] at this
  exact absurd this (by decide)

--| THE BAKER.  Stretch the first record, and lay the bit it lost on the second.
def bake (p : UnitCut × UnitCut) : UnitCut × UnitCut := (doubled p.1, pushed (p.1.cut 1) (top_le p.1) p.2)

--| THE BAKER RUN BACKWARD.  Take the bit off the second record and lay it under the first.
def unbake (p : UnitCut × UnitCut) : UnitCut × UnitCut := (pushed (p.2.cut 1) (top_le p.2) p.1, doubled p.2)

--| THERE AND BACK, EXACTLY.  The pair corresponds to itself by the baker, whichever end you start from.
def theBaker : Correspondence (UnitCut × UnitCut) (UnitCut × UnitCut) where
  there := bake
  back := unbake
  there_then_back p := by
    show (pushed ((pushed (p.1.cut 1) (top_le p.1) p.2).cut 1) _ (doubled p.1), doubled (pushed (p.1.cut 1) (top_le p.1) p.2)) = p
    have e : pushed ((pushed (p.1.cut 1) (top_le p.1) p.2).cut 1) (top_le _) (doubled p.1) = p.1 := by
      have : ∀ t (ht : t ≤ 1), t = p.1.cut 1 → pushed t ht (doubled p.1) = p.1 := by
        intro t ht et; subst et; exact pushed_doubled p.1
      exact this _ _ (pushed_top _ _ _)
    rw [e, doubled_pushed]
  back_then_there p := by
    show (doubled (pushed (p.2.cut 1) (top_le p.2) p.1),
      pushed ((pushed (p.2.cut 1) (top_le p.2) p.1).cut 1) _ (doubled p.2)) = p
    have e : pushed ((pushed (p.2.cut 1) (top_le p.2) p.1).cut 1) (top_le _) (doubled p.2) = p.2 := by
      have : ∀ t (ht : t ≤ 1), t = p.2.cut 1 → pushed t ht (doubled p.2) = p.2 := by
        intro t ht et; subst et; exact pushed_doubled p.2
      exact this _ _ (pushed_top _ _ _)
    rw [e, doubled_pushed]

--| The record of nothing.
def nothing : UnitCut := ⟨fun _ => 0, fun _ => ⟨Nat.le_refl 0, Nat.zero_le _⟩, rfl⟩

end UnitCut
end Meanings
