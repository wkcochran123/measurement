/-
The least, the largest, and no largest at all.

A zero is not the naturals.  Every ordinal is well ordered and has a least element.  The naturals are the well order in
which every place has one after it and every place but the first has one before it.  The one after is free: it is the
successor.  The first place where a statement holds is not free.  It is found by looking, one place at a time, and looking
needs the statement to click at every place.  A statement that comes with its click is found with nothing more.  A bare
statement has to be handed a click from outside, and the only place Lean keeps one is `Classical.choice`.

So the bill is the click.  Each theorem below is written once with the click and once without, and the one without is the
one with, handed a click made by choice.
-/
import Meanings.Counted

namespace Meanings

--| THE SEARCH.  The first place up to n where P clicks, or n and one if it never does: found by looking.
def firstUpTo (P : Nat → Prop) [DecidablePred P] : Nat → Nat
  | 0     => if P 0 then 0 else 1
  | n + 1 => if firstUpTo P n ≤ n then firstUpTo P n else if P (n + 1) then n + 1 else n + 2

theorem firstUpTo_finds (P : Nat → Prop) [DecidablePred P] (n : Nat) :
    firstUpTo P n ≤ n + 1
      ∧ (firstUpTo P n ≤ n → P (firstUpTo P n))
      ∧ (∀ k, k < firstUpTo P n → ¬ P k) := by
  induction n with
  | zero =>
    simp only [firstUpTo]
    split
    · exact ⟨Nat.zero_le _, fun _ => by assumption, fun k hk => absurd hk (Nat.not_lt_zero k)⟩
    · refine ⟨Nat.le_refl _, fun h => absurd h (by decide), fun k hk => ?_⟩
      have : k = 0 := Nat.lt_one_iff.mp hk
      subst this; assumption
  | succ n ih =>
    obtain ⟨b, found, before⟩ := ih
    simp only [firstUpTo]
    split
    · rename_i h
      exact ⟨Nat.le_succ_of_le (Nat.le_succ_of_le h), fun _ => found h, before⟩
    · rename_i h
      have eq : firstUpTo P n = n + 1 := Nat.le_antisymm b (Nat.lt_of_not_le h)
      split
      · exact ⟨Nat.le_succ _, fun _ => by assumption, fun k hk => before k (eq ▸ hk)⟩
      · refine ⟨Nat.le_refl _, fun h' => absurd h' (Nat.not_succ_le_self _), fun k hk => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hk with lt | e
        · exact before k (eq ▸ lt)
        · subst e; assumption

--| THE LEAST, WITH THE CLICK.  Where P clicks and holds somewhere, there is a first place it holds.
theorem the_least_with_the_click (P : Nat → Prop) [DecidablePred P] (n : Nat) (h : P n) :
    ∃ m, P m ∧ ∀ k, k < m → ¬ P k := by
  obtain ⟨_, found, before⟩ := firstUpTo_finds P n
  exact ⟨firstUpTo P n, found (Nat.le_of_not_lt (fun lt => before n lt h)), before⟩

--| THE LEAST, WITHOUT IT.  The same for any statement at all, with the click handed in.
theorem the_least_without_the_click (P : Nat → Prop) (n : Nat) (h : P n) :
    ∃ m, P m ∧ ∀ k, k < m → ¬ P k :=
  @the_least_with_the_click P (fun k => Classical.propDecidable (P k)) n h

--| THE LARGEST, WITH THE CLICK.  Below a bound, where P holds somewhere, there is a last place it holds.
theorem the_largest_with_the_click (P : Nat → Prop) [DecidablePred P] (bound n : Nat) (below : n ≤ bound) (h : P n) :
    ∃ m, m ≤ bound ∧ P m ∧ ∀ k, m < k → k ≤ bound → ¬ P k := by
  obtain ⟨j, hj, before⟩ := the_least_with_the_click (fun j => P (bound - j)) (bound - n)
    (by show P (bound - (bound - n)); rw [Nat.sub_sub_self below]; exact h)
  refine ⟨bound - j, Nat.sub_le _ _, hj, fun k gt le hk => before (bound - k) ?_ ?_⟩
  · omega
  · show P (bound - (bound - k)); rw [Nat.sub_sub_self le]; exact hk

--| THE LARGEST, WITHOUT IT.
theorem the_largest_without_the_click (P : Nat → Prop) (bound n : Nat) (below : n ≤ bound) (h : P n) :
    ∃ m, m ≤ bound ∧ P m ∧ ∀ k, m < k → k ≤ bound → ¬ P k :=
  @the_largest_with_the_click P (fun k => Classical.propDecidable (P k)) bound n below h

--| AND NO LARGEST AT ALL.  Every place has one after it.  This costs nothing.
theorem there_is_always_one_more : ∀ n : Nat, ∃ m, n < m := fun n => ⟨n + 1, Nat.lt_succ_self n⟩

namespace CountedAsNat
universe u
variable {α : Type u} [Add α] [Mul α] [Sub α] [LT α] [CountedAsNat α]

--| On anything counted as the naturals: nothing is largest, for the deal of one more is always more.
theorem nothing_counted_is_largest (a : α) : ∃ b, a < b :=
  ⟨deal (count a + 1), (less _ _).2 (by rw [count_deal]; exact Nat.lt_succ_self _)⟩

--| Less is well founded: there is no walk down forever.
theorem less_is_well_founded : WellFounded (fun a b : α => a < b) :=
  Subrelation.wf (fun h => (less _ _).1 h) (InvImage.wf count Nat.lt_wfRel.wf)

--| A statement the reader cannot tell apart on two things of one count.
def ReadAlike (P : α → Prop) : Prop := ∀ a b, count a = count b → (P a ↔ P b)

--| THE LEAST COUNTED, WITH THE CLICK.  A statement read alike, that clicks and holds of something, holds of something with
--| nothing less holding it.
theorem the_least_counted_with_the_click (P : α → Prop) [DecidablePred P] (alike : ReadAlike P) (a : α) (h : P a) :
    ∃ b, P b ∧ ∀ c, c < b → ¬ P c := by
  have dealt : ∀ c : α, P c ↔ P (deal (count c)) := fun c => alike _ _ (count_deal (count c)).symm
  obtain ⟨m, hm, before⟩ := the_least_with_the_click (fun n => P (deal n)) (count a) ((dealt a).1 h)
  refine ⟨deal m, hm, fun c lt hc => before (count c) ?_ ((dealt c).1 hc)⟩
  have := (less _ _).1 lt
  rwa [count_deal] at this

--| THE LEAST COUNTED, WITHOUT IT.
theorem the_least_counted_without_the_click (P : α → Prop) (alike : ReadAlike P) (a : α) (h : P a) :
    ∃ b, P b ∧ ∀ c, c < b → ¬ P c :=
  @the_least_counted_with_the_click α _ _ _ _ _ P (fun c => Classical.propDecidable (P c)) alike a h

end CountedAsNat
end Meanings
