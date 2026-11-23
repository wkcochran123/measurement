/-
Continuity, and where the choice is.

A function is continuous when for every closeness of the answers there is a closeness of the questions that buys it:
for every k, some m.  That is a statement.  A modulus is a function: for every k, this m.  The statement says something
is there; the modulus says where.  Going from the one to the other is choosing, for every k at once, one m, and that is
choice itself, the countable kind.

Unless every question "does this m serve this k?" clicks.  Then the least m is found by looking, from nothing upward,
and the looking stops because the statement says something is there.  The proof of existence is not opened; it is only
leaned on to say the looking ends.  So with the click, the modulus is found and no choice is billed; without it, the
same theorem must be handed a click, and the only one Lean keeps is choice.

The reals here already carry their moduli: a sum reads each real at stage two n and one, and a product as far on as the
walls are high.  That is why nothing built so far needed choice: every operation said where, not only that.
-/
import Meanings.Least
import Meanings.Arithmetic

namespace Meanings

section search
variable (P : Nat → Prop) [DecidablePred P]

--| Not yet: the next place, when nothing up to here has held.
def notYet (m n : Nat) : Prop := m = n + 1 ∧ ∀ k, k ≤ n → ¬ P k

--| The looking ends, because something holds.
omit [DecidablePred P] in
theorem the_looking_ends (H : ∃ n, P n) : WellFounded (notYet P) :=
  ⟨let ⟨n, pn⟩ := H
    suffices ∀ m k, n ≤ k + m → Acc (notYet P) k from fun _ => this _ _ (Nat.le_add_left _ _)
    fun m =>
      Nat.recOn m
        (fun _ kn => ⟨_, fun y r => match y, r with
          | _, ⟨rfl, a⟩ => absurd pn (a _ kn)⟩)
        fun m IH k kn => ⟨_, fun y r => match y, r with
          | _, ⟨rfl, _⟩ => IH _ (by rw [Nat.add_right_comm]; exact kn)⟩⟩

--| THE LEAST PLACE, FOUND BY LOOKING.  With the click, and a proof that something holds, the least place that holds.
def findByLooking (H : ∃ n, P n) : { n // P n ∧ ∀ m, m < n → ¬ P m } :=
  @WellFounded.fix _ (fun k => (∀ n, n < k → ¬ P n) → { n // P n ∧ ∀ m, m < n → ¬ P m }) (notYet P)
    (the_looking_ends P H)
    (fun m IH before => if pm : P m then ⟨m, pm, before⟩ else
        have upTo : ∀ n, n ≤ m → ¬ P n := fun n h =>
          Or.elim (Nat.lt_or_eq_of_le h) (before n) fun e => by rw [e]; exact pm
        IH _ ⟨rfl, upTo⟩ fun n h => upTo n (Nat.le_of_succ_le_succ h))
    0 fun _ h => absurd h (Nat.not_lt_zero _)

end search

--| A MODULUS, WITH THE CLICK.  For every k some m serves, and serving clicks: then a modulus, the least m for every k.
theorem a_modulus_with_the_click (serves : Nat → Nat → Prop) [∀ k, DecidablePred (serves k)]
    (continuous : ∀ k, ∃ m, serves k m) :
    ∃ modulus : Nat → Nat, ∀ k, serves k (modulus k) ∧ ∀ m, m < modulus k → ¬ serves k m :=
  ⟨fun k => (findByLooking (serves k) (continuous k)).1, fun k => (findByLooking (serves k) (continuous k)).2⟩

--| A MODULUS, WITHOUT IT.  The same theorem, for any statement, handed a click by choice.
theorem a_modulus_without_the_click (serves : Nat → Nat → Prop) (continuous : ∀ k, ∃ m, serves k m) :
    ∃ modulus : Nat → Nat, ∀ k, serves k (modulus k) ∧ ∀ m, m < modulus k → ¬ serves k m :=
  @a_modulus_with_the_click serves (fun k m => Classical.propDecidable (serves k m)) continuous

--| THE MODULI ALREADY CARRIED.  A sum reads each real at stage two n and one; a product as far on as the walls are high.
theorem the_sum_carries_its_modulus (x y : Bracketed) (n : Nat) :
    (x.add y).low n = (x.low (2 * n + 1)).add (y.low (2 * n + 1))
      ∧ (x.add y).high n = (x.high (2 * n + 1)).add (y.high (2 * n + 1)) := ⟨rfl, rfl⟩

theorem the_product_carries_its_modulus (x y : Bracketed) (n : Nat) :
    (x.mul y).low n = (x.low (x.stageForProduct y n)).mul (y.low (x.stageForProduct y n))
      ∧ (x.mul y).high n = (x.high (x.stageForProduct y n)).mul (y.high (x.stageForProduct y n)) := ⟨rfl, rfl⟩

end Meanings
