/-
The gap: what a finite stage shows, and what it cannot.

Two reals are one when no wall of either is ever past a wall of the other, at every pair of stages.  A difference shows
at a finite stage: a pair of stages where a wall has passed is enough, and from such a pair that the two are not one
follows with nothing handed in.  The other way is not free.  From only that the two are not one, to produce the pair of
stages where they part, is to choose: it is Markov's principle, and in Lean it bills choice.  So is deciding, of any two
reals, whether they are one: with the click handed in, nothing is billed; for any two, the decision is choice itself.

So the gap is never closed by anything computed from the walls.  Showing it open takes finitely many symbols; showing it
closed takes every stage; and the only decision of it for every pair is the one handed in.
-/
import Meanings.Real

namespace Meanings
namespace Bracketed

--| At a pair of stages, a wall of the one has passed a wall of the other.
def PartedAt (x y : Bracketed) (n m : Nat) : Prop := ¬ (x.low n).le (y.high m) ∨ ¬ (y.low n).le (x.high m)

--| A DIFFERENCE SHOWS AT A FINITE STAGE.  Parted at a pair of stages, the two are not one: nothing handed in.
theorem parted_is_not_same {x y : Bracketed} (h : ∃ n m, x.PartedAt y n m) : ¬ x.Same y := fun same =>
  let ⟨n, m, parted⟩ := h
  parted.elim (fun no => no (same n m).1) (fun no => no (same n m).2)

--| FROM NOT ONE TO WHERE THEY PART IS CHOICE.  Markov's principle: the pair of stages is produced from a negation.
theorem not_same_is_parted {x y : Bracketed} (h : ¬ x.Same y) : ∃ n m, x.PartedAt y n m :=
  Classical.byContradiction fun none => h fun n m =>
    ⟨Classical.byContradiction fun no => none ⟨n, m, Or.inl no⟩,
     Classical.byContradiction fun no => none ⟨n, m, Or.inr no⟩⟩

--| ONE OR NOT, WITH THE CLICK.  Handed a decision, nothing is billed.
theorem same_or_not_with_the_click (x y : Bracketed) [Decidable (x.Same y)] : x.Same y ∨ ¬ x.Same y :=
  Decidable.em _

--| ONE OR NOT, FOR ANY TWO.  The decision is choice itself.
theorem same_or_not_by_choice (x y : Bracketed) : x.Same y ∨ ¬ x.Same y := Classical.em _

end Bracketed
end Meanings
