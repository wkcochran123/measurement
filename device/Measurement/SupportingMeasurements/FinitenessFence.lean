import Measurement.Episode24

/-! # FinitenessFence — the impossibility, finished as a machine-checked theorem.
Operator: "finish the proof."  External review P5: "the machine proves it cannot derive it" lived only
in comments — no Lean theorem. This finishes it, on the HONEST (narrow, true) content:

  The coupling is the RESIDUE between the first variation (`gateaux`) and the second (`frechet`).
  The machine reads only through `boxOf` — its finite resolution (`boxCount = 2`).
  `gateaux_indist_frechet` (rfl): the two variations fall in the SAME box; the residue that separates
  them is BELOW the representation's resolution.
  ⟹  EVERY reading the machine computes off its boxes returns first variation = second variation.
      The machine cannot resolve the residue to a value — it is fenced, by its own finiteness,
      from deriving the magnitude. THAT is the theorem, choice-free.

This is the narrow true claim (this finite construction cannot resolve THIS residue below its floor),
NOT the false-in-general claim that no finite machine can compute any real. Marked accordingly. -/

namespace Measurement.FinitenessFence
open Measurement

/-- THE FENCE. For ANY reading the machine computes from a box, the first variation and the second
variation read the SAME — so no machine reading resolves the residue between them. -/
theorem machine_cannot_resolve_residue {M : Type} (read : Fin boxCount → M)
    (g : Gospel) (a b c : Prop) (v1 v2 tail : Variation) :
    read (boxOf (.gateaux g a b tail)) = read (boxOf (.frechet g a b c v1 v2)) := by
  rw [gateaux_indist_frechet g a b c v1 v2 tail]

#print axioms machine_cannot_resolve_residue

/-- The GENERAL PRINCIPLE the fence rests on (the book's "a quantity every act leaves untouched is a
quantity no act can arrive at"): a reading invariant under one step is invariant under any number of
steps, so no finite count changes it. -/
def iter {X : Type} (step : X → X) : Nat → X → X
  | 0,   x => x
  | n+1, x => iter step n (step x)

theorem invariant_is_unreachable {X M : Type} (step : X → X) (inv : X → M)
    (h : ∀ x, inv (step x) = inv x) : ∀ (n : Nat) (x : X), inv (iter step n x) = inv x := by
  intro n
  induction n with
  | zero => intro x; rfl
  | succ k ih => intro x; exact (ih (step x)).trans (h x)

#print axioms invariant_is_unreachable

end Measurement.FinitenessFence
