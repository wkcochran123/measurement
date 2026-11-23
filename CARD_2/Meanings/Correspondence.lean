/-
What it is for two kinds of thing to correspond.

Meanings holds what a reading is taken to mean, as interfaces, in Lean's core and nothing else.  It names nothing of the
device.  Episode 13 imports it and meets the interfaces with what it has already proved; where a proof is missing, Episode
13 does not compile.  So that it compiles is that the interface is met.

Lean's core has the naturals, the integers and the ratios, and no word for two kinds being the same.  The word is here: a
way there and a way back, each undoing the other.
-/

namespace Meanings
universe u v

--| Two kinds correspond when a way there and a way back undo each other, whichever end you start from.
structure Correspondence (α : Type u) (β : Type v) where
  there : α → β
  back  : β → α
  there_then_back : ∀ a, back (there a) = a
  back_then_there : ∀ b, there (back b) = b

end Meanings
