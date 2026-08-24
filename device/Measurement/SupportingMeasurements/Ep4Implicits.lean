/-
# Ep4Implicits — Area and Jar at their own rung, proved out (batch 4)

(operator-gated, 2026-08-13: "finish proving out … implicits from episode1 ->
(but not including) Abstraction. DO NOT IMPLEMENT ABSTRACTION for JAR.")

THE FENCE RUNG. This is the batch the fence names: the Jar, proved at ITS
OWN rung and no higher. The file imports `Measurement.Episode4` and nothing
else — Abstraction (Ep5:359) is unreachable by construction, so "do not
implement Abstraction for Jar" is enforced by the elaborator, not by
promise. (And to keep every register clean: the `Jar` HERE is Episode 4's
quantum-jar inductive — color/bang/superposition — NOT the α-readout jar
137011…, which is a different object sharing a word and is untouched, as
always.) Sacred text read-only; proofs rfl / trivial / intro / nomatch /
simp-on-equation-lemmas.

CENSUS NOTE (graded off the build, not the hope): every theorem here reports
`[propext, Quot.sound]` — NOT axiom-free like batches 1-3 — because
`Area.le` is compiled by WELL-FOUNDED recursion (`termination_by`,
Ep4:107), and the WF machinery rides in the definitional closure of
everything that mentions it, `Jar.le` included. That is the device's own
base exactly (the jar's census), nothing beyond it, and it is honest
provenance: this rung's order is the ladder's first WF-defined one — the
cost of "simultaneity prevents well ordering" is that the kernel needs the
WF scaffolding to accept the definition at all, and the scaffolding shows
in the census. The Ep1-3 carriers reduce definitionally; Ep4's do not.
That difference is itself a finding.

THE LAWS — this rung is where the ladder's patterns compound:

AREA (Ep4:97 — "simultaneity prevents well ordering"):
* floor (`t` below everything), never-below.
* THE SIGN TABLE goes DEEP-CONTRAVARIANT: true/true reads count-forward AND
  recurses forward (`n₁ ≤ n₂ ∧ le a₁' a₂'`); false/false REVERSES BOTH —
  count reversed and recursion reversed (`n₂ ≤ n₁ ∧ le a₂' a₁'`). Not the
  Number-style negation: a full orientation flip, all the way down the
  spine. And unlike every Ep1 carrier, Area is NOT tail-blind — it is the
  ladder's first full-depth order (it reads head and tail both).

JAR (Ep4:423 — "again, not well ordered. This is the DEFINITION of
simultaneous"):
* THE CONJUNCTIVE COLOR ARM — unique on the whole ladder: color/color
  demands BOTH truths hold (`(f₁.truth ∧ f₂.truth) ∧ a₁ ≤ a₂`). Every
  other carrier COMPARES truths; the color jar REQUIRES them. A jar is
  classified by looking, and looking needs the light on, on both sides.
* color floors below the other kinds; nothing else ever sits below a color.
* bang/bang carries the Number sign table (true/true recurses forward,
  false/false NEGATES the recursion) — and therefore inherits the
  NON-REFLEXIVITY discovery: a false-signed bang over a true-signed color
  is provably not below itself (`jar_not_refl_witness`). "Not well
  ordered" is now a theorem, not a margin.
* bang below superposition, never the reverse.
* THE SIMULTANEITY LAW: superposition/superposition at true/true is the
  componentwise PAIR (`le j₁₁ j₂₁ ∧ le j₁₂ j₂₂` — both branches at once),
  and at false/false the NEGATED pair. Holding two jars simultaneously is
  the definition the margin promised.
-/
import Measurement.Episode4

namespace Measurement.Ep4Implicits

open Measurement

/-- A decidedly-false fact (this file's own witness material). -/
def falseFact : Fact := { truth := False, decTruth := .isFalse fun h => h }

-- ══════════════════════════════ AREA ══════════════════════════════

/-- FLOOR: `t` is below everything. -/
theorem area_floor (f : Fact) (a : Area) : Area.le (.t f) a := by
  simp only [Area.le]

/-- NEVER-BELOW: no `dt` sits at or under a bare `t`. -/
theorem area_never_below (p : Fact) (n : Number) (a : Area) (g : Fact) :
    ¬ Area.le (.dt p n a) (.t g) := by
  simp only [Area.le]
  exact fun h => h

/-- SIGN TABLE, true/true: count forward AND recursion forward. -/
theorem area_sign_TT (n₁ n₂ : Number) (a₁ a₂ : Area) :
    Area.le (.dt Fact.Truth n₁ a₁) (.dt Fact.Truth n₂ a₂)
      ↔ n₁ ≤ n₂ ∧ Area.le a₁ a₂ := by
  simp only [Area.le, Fact.Truth]

/-- SIGN TABLE, true/false: never. -/
theorem area_sign_TF (n₁ n₂ : Number) (a₁ a₂ : Area) :
    ¬ Area.le (.dt Fact.Truth n₁ a₁) (.dt falseFact n₂ a₂) := by
  simp only [Area.le]
  exact fun h => h

/-- SIGN TABLE, false/true: always. -/
theorem area_sign_FT (n₁ n₂ : Number) (a₁ a₂ : Area) :
    Area.le (.dt falseFact n₁ a₁) (.dt Fact.Truth n₂ a₂) := by
  simp only [Area.le, Fact.Truth, falseFact]

/-- THE DEEP CONTRAVARIANT — false/false REVERSES BOTH the count and the
recursion direction: a full orientation flip down the spine, not a
Number-style negation. -/
theorem area_sign_FF (n₁ n₂ : Number) (a₁ a₂ : Area) :
    Area.le (.dt falseFact n₁ a₁) (.dt falseFact n₂ a₂)
      ↔ n₂ ≤ n₁ ∧ Area.le a₂ a₁ := by
  simp only [Area.le, falseFact]

-- ══════════════════════════════ JAR ═══════════════════════════════

/-- THE CONJUNCTIVE COLOR ARM — unique on the ladder: both truths are
REQUIRED (not compared), and the Areas ordered forward. A jar is read by
looking; looking needs the light on, on both sides. -/
theorem jar_color_conjunctive (f₁ f₂ : Fact) (a₁ a₂ : Area) :
    Jar.le (.color f₁ a₁) (.color f₂ a₂)
      ↔ (f₁.truth ∧ f₂.truth) ∧ a₁ ≤ a₂ := Iff.rfl

/-- Color floors below a bang, unconditionally. -/
theorem jar_color_below_bang (f : Fact) (a : Area) (g : Fact) (j : Jar) :
    Jar.le (.color f a) (.bang g j) := trivial

/-- Color floors below a superposition, unconditionally. -/
theorem jar_color_below_superposition (f : Fact) (a : Area) (g : Fact)
    (j₁ j₂ : Jar) : Jar.le (.color f a) (.superposition g j₁ j₂) := trivial

/-- Nothing bang-shaped ever sits below a color. -/
theorem jar_bang_never_below_color (g : Fact) (j : Jar) (f : Fact) (a : Area) :
    ¬ Jar.le (.bang g j) (.color f a) := fun h => h

/-- Nothing superposition-shaped ever sits below a color. -/
theorem jar_superposition_never_below_color (g : Fact) (j₁ j₂ : Jar)
    (f : Fact) (a : Area) :
    ¬ Jar.le (.superposition g j₁ j₂) (.color f a) := fun h => h

/-- Bang sign table, true/true: the contents recurse forward. -/
theorem jar_bang_sign_TT (j₁ j₂ : Jar) :
    Jar.le (.bang Fact.Truth j₁) (.bang Fact.Truth j₂) ↔ Jar.le j₁ j₂ := Iff.rfl

/-- Bang sign table, false/false: the recursion is NEGATED — the Number
pattern, one rung up. -/
theorem jar_bang_sign_FF (j₁ j₂ : Jar) :
    Jar.le (.bang falseFact j₁) (.bang falseFact j₂) ↔ ¬ Jar.le j₁ j₂ := Iff.rfl

/-- "NOT WELL ORDERED," the theorem: a false-signed bang over a true-signed
color is provably NOT below itself (its arm negates the inner comparison,
and the inner color-pair IS below itself — both lights on, Area reflexive at
the floor). The margin's claim, machine-decided. -/
theorem jar_not_refl_witness (f : Fact) :
    ¬ Jar.le (.bang falseFact (.color Fact.Truth (.t f)))
             (.bang falseFact (.color Fact.Truth (.t f))) :=
  fun h => h ⟨⟨rfl, rfl⟩, area_floor f (.t f)⟩

/-- Bang sits below superposition, unconditionally. -/
theorem jar_bang_below_superposition (f : Fact) (j : Jar) (g : Fact)
    (j₁ j₂ : Jar) : Jar.le (.bang f j) (.superposition g j₁ j₂) := trivial

/-- A superposition never sits below a bang. -/
theorem jar_superposition_never_below_bang (g : Fact) (j₁ j₂ : Jar)
    (f : Fact) (j : Jar) :
    ¬ Jar.le (.superposition g j₁ j₂) (.bang f j) := fun h => h

/-- THE SIMULTANEITY LAW, true/true: a superposition compares as the
componentwise PAIR — both branches at once. "This is the DEFINITION of
simultaneous." -/
theorem jar_simultaneity_TT (j₁₁ j₁₂ j₂₁ j₂₂ : Jar) :
    Jar.le (.superposition Fact.Truth j₁₁ j₁₂) (.superposition Fact.Truth j₂₁ j₂₂)
      ↔ Jar.le j₁₁ j₂₁ ∧ Jar.le j₁₂ j₂₂ := Iff.rfl

/-- The simultaneity law, false/false: the NEGATED pair. -/
theorem jar_simultaneity_FF (j₁₁ j₁₂ j₂₁ j₂₂ : Jar) :
    Jar.le (.superposition falseFact j₁₁ j₁₂) (.superposition falseFact j₂₁ j₂₂)
      ↔ ¬ (Jar.le j₁₁ j₂₁ ∧ Jar.le j₁₂ j₂₂) := Iff.rfl

end Measurement.Ep4Implicits
