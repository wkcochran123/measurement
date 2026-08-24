/-
# Ep5Implicits — Equivalation, proved out (batch 5, the last rung below Abstraction)

(operator-gated, 2026-08-13: "finish proving out … implicits from episode1 ->
(but not including) Abstraction. DO NOT IMPLEMENT ABSTRACTION for JAR.")

The stratum's last rung. THE FENCE CHANGES FORM HERE, stated honestly:
Episode 5 CONTAINS Abstraction (Ep5:359), so an import-graph guarantee is no
longer possible — the guarantee is UNREFERENCED, checkable by grep: outside
this header, the token `Abstraction` appears nowhere in this file. The
Jar fence was fully discharged at batch 4 (Jar proved at its own rung, from
a file that cannot import Ep5); this file touches Jar only where
Equivalation's own definition does — the `j₁ ≤ j₂` payload comparison in
the physics arm, which is Ep4's order, nothing higher.

SCOPE NOTE, so nothing is smuggled: ENCODING (Ep5:236) carries NO intrinsic
order — no `le`, no `LE` instance. Its comparison machinery (`execute?`,
`output?`) lives as INSTANCE FIELDS of CompiledProcess/EXECUTED behind the
typeclass tower, which is a different stratum of claim (instance-dependent,
like `obfusplained?`) and is left for its own gated leaf rather than
half-proved here. Equivalation is the rung's order-carrier, and it is
proved out below.

THE LAWS — the conjunctive register, ascending:
* THE PHYSICS ARM is conjunctive like Jar's color (both truths REQUIRED,
  plus the Jars ordered): the light-on law, one rung up.
* THE ZERO_LIKE ARM is PURELY conjunctive — `f₁.truth ∧ f₂.truth`, no
  payload comparison at all. Two nothings compare exactly when both lights
  are on; there is nothing else to compare ("is it evidence of absence or
  absence of evidence?").
* zero_like is the MOBILE FLOOR: below physics and below one_like,
  unconditionally — but physics never sits below zero_like (the arm is the
  Bool `false`): something never rounds down to nothing.
* physics sits below one_like unconditionally.
* THE ONE_LIKE ARM CARRIES BARE PROPS — the first carrier on the whole
  ladder whose order demands arbitrary PROPOSITIONS hold (`p₁ ∧ p₂ ∧ …`,
  with `p : Prop`, not a Fact — no decidability attached), and it recurses
  on the FIRST components only: the second Equivalation of each one_like
  is INVISIBLE to the order (partial blindness, stated as swap-invariance).
* one_like never sits below physics or zero_like (the catch-all `false`).

CENSUS (graded off the build): UNIFORMLY `[propext, Quot.sound]` — all ten
theorems, not just the physics arm. The WF closure from Area rides in the
DEFINITION of `Equivalation.le` itself (its physics arm mentions Jar's
order, whose closure includes Area's WF scaffolding), so every theorem
touching `Equivalation.le` inherits the base, zero_like arms included.
Batch 4's finding, completed: from the Area rung upward, the ladder's
census floor is the device's own `[propext, Quot.sound]` — the WF cost is
definitional, not per-arm. Still nothing beyond the jar's base.
-/
import Measurement.Episode5

namespace Measurement.Ep5Implicits

open Measurement

-- ═════════════════════════ EQUIVALATION ═══════════════════════════

/-- THE PHYSICS ARM, conjunctive: both truths required, Jars ordered —
Jar's color law, one rung up. -/
theorem equivalation_physics_conjunctive (f₁ f₂ : Fact) (j₁ j₂ : Jar) :
    Equivalation.le (.physics f₁ j₁) (.physics f₂ j₂)
      ↔ f₁.truth ∧ f₂.truth ∧ j₁ ≤ j₂ := Iff.rfl

/-- Something never rounds down to nothing: physics never sits below a
zero_like (the arm is the Bool `false`). -/
theorem equivalation_physics_never_below_zero_like (f : Fact) (j : Jar)
    (g : Fact) (e : Equivalation) :
    ¬ Equivalation.le (.physics f j) (.zero_like g e) := fun h => nomatch h

/-- Physics sits below one_like, unconditionally. -/
theorem equivalation_physics_below_one_like (f : Fact) (j : Jar) (p : Prop)
    (e₁ e₂ : Equivalation) :
    Equivalation.le (.physics f j) (.one_like p e₁ e₂) := rfl

/-- THE ZERO_LIKE ARM, purely conjunctive: two nothings compare exactly when
both lights are on — there is no payload to compare. -/
theorem equivalation_zero_like_conjunctive (f₁ f₂ : Fact) (e₁ e₂ : Equivalation) :
    Equivalation.le (.zero_like f₁ e₁) (.zero_like f₂ e₂)
      ↔ f₁.truth ∧ f₂.truth := Iff.rfl

/-- zero_like is the mobile floor: below physics, unconditionally. -/
theorem equivalation_zero_like_below_physics (f : Fact) (e : Equivalation)
    (g : Fact) (j : Jar) :
    Equivalation.le (.zero_like f e) (.physics g j) := rfl

/-- zero_like is the mobile floor: below one_like, unconditionally. -/
theorem equivalation_zero_like_below_one_like (f : Fact) (e : Equivalation)
    (p : Prop) (e₁ e₂ : Equivalation) :
    Equivalation.le (.zero_like f e) (.one_like p e₁ e₂) := rfl

/-- THE BARE-PROP ARM: one_like/one_like demands two arbitrary PROPOSITIONS
hold (no Fact, no decidability) and recurses on the first components. -/
theorem equivalation_one_like_fork (p₁ p₂ : Prop) (e f : Equivalation)
    (x y : Equivalation) :
    Equivalation.le (.one_like p₁ e x) (.one_like p₂ f y)
      ↔ p₁ ∧ p₂ ∧ Equivalation.le e f := Iff.rfl

/-- PARTIAL BLINDNESS: the second component of each one_like is invisible to
the order — swap them freely, the comparison is untouched. -/
theorem equivalation_one_like_second_blind (p₁ p₂ : Prop) (e f : Equivalation)
    (x₁ x₂ y₁ y₂ : Equivalation) :
    Equivalation.le (.one_like p₁ e x₁) (.one_like p₂ f y₁)
      ↔ Equivalation.le (.one_like p₁ e x₂) (.one_like p₂ f y₂) := Iff.rfl

/-- one_like never sits below physics (the catch-all `false`). -/
theorem equivalation_one_like_never_below_physics (p : Prop) (e x : Equivalation)
    (f : Fact) (j : Jar) :
    ¬ Equivalation.le (.one_like p e x) (.physics f j) := fun h => nomatch h

/-- one_like never sits below zero_like (the catch-all `false`). -/
theorem equivalation_one_like_never_below_zero_like (p : Prop) (e x : Equivalation)
    (f : Fact) (g : Equivalation) :
    ¬ Equivalation.le (.one_like p e x) (.zero_like f g) := fun h => nomatch h

end Measurement.Ep5Implicits
