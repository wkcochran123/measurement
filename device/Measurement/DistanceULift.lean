/-! # DistanceULift — the one-universe gap in `.distance` is real:
distance cannot be ULifted.

COMMISSION (operator, 2026-08-16 07:50, verbatim): "Theorem: distance can
be ulifted" — "Cannot."

GROUNDING (Beastmaster, same hour): the device's `.distance` is not
universe-neutral. Episode13:12 declares the constructor

  |distance: Fact → Number → Number → Type i → Type (i+1) →
             Measurement → Measurement

and Episode13:55 constructs it always ACROSS the one-universe gap:

  | .origin fact number _ =>
      .distance fact number length Value (ULift.{i+1} Value) velocity

— the fifth slot is exactly `ULift.{i+1}` of the fourth. Distance, as the
device builds it, lives ON the arrow `V ↦ ULift.{i+1} V` from `Type i`
into `Type (i+1)`. Call that arrow the GAP ARROW.

THE CLAIM, TYPED (the name is the operator's sentence; the TYPE is the
claim, and nothing broader): the gap arrow cannot be inverted —

  * `gap_arrow_not_surjective` — the arrow `V ↦ ULift.{i+1} V` does not
    reach every inhabitant of `Type (i+1)`: the room one universe up is
    strictly larger than everything liftable from below.
  * `distance_cannot_be_ulifted` — headline: there is NO down-map
    `down : Type (i+1) → Type i` with `ULift.{i+1} (down W) = W` for all
    `W`. The gap `.distance` is built across has no section; the upper
    address cannot be re-founded from the lower room, so the identification
    that would make a lifted distance THE SAME distance does not exist.

THE ENGINE, proved here from nothing (no imports):
  * `false_of_eq_not`, `cantor_diagonal` — the diagonal argument,
    axiom-free: no `f : α → (α → Prop)` is surjective.
  * `cantor_injective` — no `g : (α → Prop) → α` is injective
    (uses propext + funext, i.e. census [propext, Quot.sound]).
  * `not_surjective_type` — no family `f : α → Type u` with `α : Type u`
    is surjective: a universe cannot be indexed from within itself.

THE HONEST ASYMMETRY, stated so the fence is sharp:
  * `content_ascends` / `content_roundtrips` — pointwise, CONTENT moves
    freely both ways (`ULift.up`, `ULift.down`, round-trip `rfl`). The
    impossibility is not about the values a distance carries; it is about
    the ADDRESS: the type-level gap has no inverse. The reading is pinned
    to the room it was built in.

WHY THIS IS THE FENCE (Beastmaster's gloss, now a receipt): the device's
distance is constructed AT the one-universe gap. If the gap arrow had an
inverse, the local distance could be re-addressed as a universal one —
the crank's cosmic step. The kernel refuses the inverse. There is no path
from the electron's distance to a cosmic one; the wall is not a judgment
but a theorem.

NOT CLAIMED: anything about physical distance, space, spacetime, or
cosmology ("distance" here is the device's `.distance`, a constructor of
`Measurement`, and its gap arrow — nothing else); anything about the
VALUES a measurement carries (those lift and return pointwise, proved);
any statement broader than the non-existence typed below. -/

namespace Measurement.DistanceULift

universe u v i

/-- Surjectivity, defined locally (this leaf imports nothing). -/
def Surjective {α : Sort u} {β : Sort v} (f : α → β) : Prop :=
  ∀ b, ∃ a, f a = b

/-- Injectivity, defined locally. -/
def Injective {α : Sort u} {β : Sort v} (f : α → β) : Prop :=
  ∀ a b, f a = f b → a = b

/-- A proposition cannot equal its own negation. Axiom-free. -/
theorem false_of_eq_not {p : Prop} (e : p = ¬ p) : False :=
  have np : ¬ p := fun hp => (cast e hp) hp
  np (cast e.symm np)

#print axioms false_of_eq_not

/-- The diagonal: no `f : α → (α → Prop)` is surjective. Axiom-free. -/
theorem cantor_diagonal {α : Type u} (f : α → (α → Prop)) :
    ¬ Surjective f := by
  intro hf
  cases hf (fun a => ¬ f a a) with
  | intro a ha =>
    exact false_of_eq_not (congrFun ha a)

#print axioms cantor_diagonal

/-- The mirror: no `g : (α → Prop) → α` is injective. -/
theorem cantor_injective {α : Type u} (g : (α → Prop) → α) :
    ¬ Injective g := by
  intro hg
  apply cantor_diagonal (fun a b => ∀ S : α → Prop, g S = a → S b)
  intro S
  refine ⟨g S, funext fun b => propext ⟨fun h => h S rfl, fun hb T e => ?_⟩⟩
  exact (hg T S e).symm ▸ hb

#print axioms cantor_injective

/-- A universe cannot be indexed from within itself: no `f : α → Type u`
    with `α : Type u` is surjective. -/
theorem not_surjective_type {α : Type u} (f : α → Type u) :
    ¬ Surjective f := by
  intro hf
  cases hf ((Sigma f) → Prop) with
  | intro U hU =>
    apply cantor_injective
      (fun s : (Sigma f) → Prop => (⟨U, cast hU.symm s⟩ : Sigma f))
    intro s t h
    injection h with h1 h2
    exact eq_of_heq
      ((cast_heq hU.symm s).symm.trans
        ((heq_of_eq h2).trans (cast_heq hU.symm t)))

#print axioms not_surjective_type

/-- The gap arrow `.distance` is built across (Episode13:55): the fourth
    slot `V : Type i` addressed one room up as the fifth slot
    `ULift.{i+1} V : Type (i+1)`. -/
def gapArrow : Type i → Type (i + 1) := fun V => ULift.{i + 1} V

/-- The room above is strictly larger: the gap arrow does not reach every
    type one universe up. -/
theorem gap_arrow_not_surjective : ¬ Surjective (gapArrow.{i}) :=
  not_surjective_type gapArrow

#print axioms gap_arrow_not_surjective

/-- HEADLINE — the operator's sentence, typed exactly: there is no
    down-map inverting the gap arrow. The one-universe gap in `.distance`
    has no section; the distance's address cannot be re-founded from
    below, and no lifted copy is ever identified back with the original.
    Nothing broader is claimed. -/
theorem distance_cannot_be_ulifted :
    ¬ ∃ down : Type (i + 1) → Type i,
        ∀ W : Type (i + 1), gapArrow.{i} (down W) = W :=
  fun ⟨down, hdown⟩ =>
    gap_arrow_not_surjective (fun W => ⟨down W, hdown W⟩)

#print axioms distance_cannot_be_ulifted

/-- The honest positive half: CONTENT ascends freely — every value of
    `V` lifts, and the map is exhibited as data, not merely asserted.
    The impossibility above is about the address, not the cargo.
    Axiom-free. -/
def contentAscends : ∀ (V : Type i), V → gapArrow.{i} V :=
  fun _ v => ULift.up v

#print axioms contentAscends

/-- And content round-trips, definitionally: up then down is the
    identity on values. The gap costs the values nothing; only the
    type-level address never comes back. Axiom-free. -/
theorem content_roundtrips :
    ∀ (V : Type i) (x : V), (ULift.up.{i + 1} x).down = x :=
  fun _ _ => rfl

#print axioms content_roundtrips

end Measurement.DistanceULift
