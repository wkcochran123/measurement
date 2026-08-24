/-
# LadderImplicits — the Episode 1 order-carriers, proved out (batch 1)

(operator-gated, 2026-08-13: "you are gated to finish proving out all the
implicits for the jfnk result and implicits from episode1 -> (but not
including) Abstraction. DO NOT IMPLEMENT ABSTRACTION for JAR.")

This is batch 1 of the pre-Abstraction implicits: the six order-carriers of
Episode 1 — Number, Natural, Rational, Sequence, Limit, Sample — whose `le`
definitions have carried the covariant/contravariant fork all along with no
theorem stating it. Every law below has lived IMPLICITLY inside a `le` match;
now each is a named claim the kernel checks.

## THE STRATUM FENCE, held by the import graph itself

This file imports `Measurement.Episode1` and NOTHING else. Abstraction lives
at Episode5:359; this file cannot reach it, reference it, or extend anything
toward it — the elaborator enforces the "episode1 → (not including)
Abstraction" boundary as a build fact. Nothing here touches the Jar (Ep4),
the jar chain, or any sacred text: additive leaf, read-only imports, and the
Berry stratum discipline rides on top — this is the LOW stratum naming its
own laws, never reaching for the number that only the full tower can license.

## WHAT IS PROVED (grouped per type; proofs are rfl / trivial / intro / id —
   expected census: every theorem axiom-free)

For each carrier: the FLOOR (zero/nil below everything), the NEVER-BELOW
boundary (nothing nonzero at or under the floor), the FORK stated both ways
(covariant: same truth ⇒ forward; contravariant: different truth ⇒ REVERSED —
the branch the gauge book was corrected on, now a theorem), the fork
DICHOTOMY (the two arms are the whole story), and TAIL-BLINDNESS (each rung's
order reads exactly one layer — the recursive tail is never consulted).

Two genuine discoveries, machine-decided:

* NUMBER'S SIGN TABLE IS NOT REFLEXIVE. `Number.le` forks on the DECIDED
  truth pair: true/true reads the tails forward, false/false reads the tails
  NEGATED — so `le x x` FAILS on a false-signed head (witness below:
  `¬ le (one false 0) (one false 0)` reduces to `¬¬True → False`... i.e. it
  is provably NOT below itself). Reflexivity on this ladder is a
  truth-polarity property, not a given. The true-signed spine IS reflexive
  (exhibited to depth three).

* RATIONAL FORKS ON THE WHOLE FACT, THE REST ON ITS TRUTH. `Rational.le`
  compares `p1 = p2 : Fact` (identity of the carried fact); Natural,
  Sequence, Limit, Sample compare `p1.truth = p2.truth` (identity of the
  truth only). Stated side by side, not smoothed over.

And Sample's contravariant arm falls back to the STIMULI (`s1 ≤ s2`), not a
reversed response — the fact the gauge refresh tightened in prose is here as
a machine law (`sample_signal_fork`).
-/
import Measurement.Episode1

namespace Measurement.LadderImplicits

open Measurement

/-- A decidedly-false fact, this file's own witness material (the sacred
text's `Fact.Truth` is the decidedly-true one). -/
def falseFact : Fact := { truth := False, decTruth := .isFalse fun h => h }

-- ═════════════════════════════ NUMBER ═════════════════════════════

/-- FLOOR: zero is below everything. -/
theorem number_floor (f : Fact) (n : Number) : Number.le (.zero f) n := trivial

/-- NEVER-BELOW: no one-headed number sits at or under zero. -/
theorem number_never_below (p : Fact) (n : Number) (g : Fact) :
    ¬ Number.le (.one p n) (.zero g) := fun h => h

/-- SIGN TABLE, true/true: forward — the order reads the tails as-is. -/
theorem number_sign_TT (a b : Number) :
    Number.le (.one Fact.Truth a) (.one Fact.Truth b) ↔ Number.le a b := Iff.rfl

/-- SIGN TABLE, false/true: unconditionally below (the negative side). -/
theorem number_sign_FT (a b : Number) :
    Number.le (.one falseFact a) (.one Fact.Truth b) := trivial

/-- SIGN TABLE, true/false: unconditionally not below. -/
theorem number_sign_TF (a b : Number) :
    ¬ Number.le (.one Fact.Truth a) (.one falseFact b) := fun h => h

/-- SIGN TABLE, false/false: the tails read NEGATED — the reversal is not a
convention, it is the definition. -/
theorem number_sign_FF (a b : Number) :
    Number.le (.one falseFact a) (.one falseFact b) ↔ ¬ Number.le a b := Iff.rfl

/-- THE DISCOVERY: the sign table is NOT reflexive. A false-signed head is
provably not below itself (its arm negates the tails, and the zero tail is
below itself). Reflexivity on this ladder is a truth-polarity property. -/
theorem number_not_refl_witness (f : Fact) :
    ¬ Number.le (.one falseFact (.zero f)) (.one falseFact (.zero f)) :=
  fun h => h trivial

/-- The true-signed spine IS reflexive — depth one. -/
theorem number_refl_true_1 (f : Fact) :
    Number.le (.one Fact.Truth (.zero f)) (.one Fact.Truth (.zero f)) := trivial

/-- The true-signed spine IS reflexive — depth two. -/
theorem number_refl_true_2 (f : Fact) :
    Number.le (.one Fact.Truth (.one Fact.Truth (.zero f)))
              (.one Fact.Truth (.one Fact.Truth (.zero f))) := trivial

/-- The true-signed spine IS reflexive — depth three. -/
theorem number_refl_true_3 (f : Fact) :
    Number.le (.one Fact.Truth (.one Fact.Truth (.one Fact.Truth (.zero f))))
              (.one Fact.Truth (.one Fact.Truth (.one Fact.Truth (.zero f)))) :=
  trivial

-- ═════════════════════════════ NATURAL ════════════════════════════

/-- FLOOR: zero is below everything. -/
theorem natural_floor (f : Fact) (n : Natural) : Natural.le (.zero f) n := trivial

/-- NEVER-BELOW: no nonzero natural sits at or under zero. -/
theorem natural_never_below (p : Fact) (n : Number) (t : Natural) (g : Fact) :
    ¬ Natural.le (.number p n t) (.zero g) := fun h => h

/-- FORK, covariant: same truth ⇒ the Numbers are ordered forward. -/
theorem natural_fork_covariant (p₁ p₂ : Fact) (n₁ n₂ : Number)
    (t₁ t₂ : Natural) (h : p₁.truth = p₂.truth) (hn : n₁ ≤ n₂) :
    Natural.le (.number p₁ n₁ t₁) (.number p₂ n₂ t₂) := Or.inl ⟨h, hn⟩

/-- FORK, contravariant: different truth ⇒ the SAME Numbers, REVERSED — the
branch the book was corrected on, as a theorem. -/
theorem natural_fork_contravariant (p₁ p₂ : Fact) (n₁ n₂ : Number)
    (t₁ t₂ : Natural) (h : p₁.truth ≠ p₂.truth) (hn : n₂ ≤ n₁) :
    Natural.le (.number p₁ n₁ t₁) (.number p₂ n₂ t₂) := Or.inr ⟨h, hn⟩

/-- FORK DICHOTOMY: the two arms are the whole story (definitional). -/
theorem natural_fork_complete (p₁ p₂ : Fact) (n₁ n₂ : Number) (t₁ t₂ : Natural) :
    Natural.le (.number p₁ n₁ t₁) (.number p₂ n₂ t₂)
      → (p₁.truth = p₂.truth ∧ n₁ ≤ n₂) ∨ (p₁.truth ≠ p₂.truth ∧ n₂ ≤ n₁) := id

/-- TAIL-BLINDNESS: the order reads one layer; the recursive tails are never
consulted. -/
theorem natural_tail_blind (p₁ p₂ : Fact) (n₁ n₂ : Number) (t₁ t₂ u₁ u₂ : Natural) :
    Natural.le (.number p₁ n₁ t₁) (.number p₂ n₂ t₂)
      ↔ Natural.le (.number p₁ n₁ u₁) (.number p₂ n₂ u₂) := Iff.rfl

-- ═════════════════════════════ RATIONAL ═══════════════════════════
-- NB: Rational forks on the WHOLE FACT (`p₁ = p₂`), not just its truth —
-- the one carrier on this rung that compares fact identity.

theorem rational_floor (f : Fact) (r : Rational) : Rational.le (.zero f) r := trivial

theorem rational_never_below (p : Fact) (n : Natural) (t : Rational) (g : Fact) :
    ¬ Rational.le (.number p n t) (.zero g) := fun h => h

theorem rational_fork_covariant (p₁ p₂ : Fact) (n₁ n₂ : Natural)
    (t₁ t₂ : Rational) (h : p₁ = p₂) (hn : n₁ ≤ n₂) :
    Rational.le (.number p₁ n₁ t₁) (.number p₂ n₂ t₂) := Or.inl ⟨h, hn⟩

theorem rational_fork_contravariant (p₁ p₂ : Fact) (n₁ n₂ : Natural)
    (t₁ t₂ : Rational) (h : p₁ ≠ p₂) (hn : n₂ ≤ n₁) :
    Rational.le (.number p₁ n₁ t₁) (.number p₂ n₂ t₂) := Or.inr ⟨h, hn⟩

theorem rational_fork_complete (p₁ p₂ : Fact) (n₁ n₂ : Natural) (t₁ t₂ : Rational) :
    Rational.le (.number p₁ n₁ t₁) (.number p₂ n₂ t₂)
      → (p₁ = p₂ ∧ n₁ ≤ n₂) ∨ (p₁ ≠ p₂ ∧ n₂ ≤ n₁) := id

theorem rational_tail_blind (p₁ p₂ : Fact) (n₁ n₂ : Natural)
    (t₁ t₂ u₁ u₂ : Rational) :
    Rational.le (.number p₁ n₁ t₁) (.number p₂ n₂ t₂)
      ↔ Rational.le (.number p₁ n₁ u₁) (.number p₂ n₂ u₂) := Iff.rfl

-- ═════════════════════════════ SEQUENCE ═══════════════════════════

theorem sequence_floor (f : Fact) (s : Sequence) : Sequence.le (.nil f) s := trivial

theorem sequence_never_below (p : Fact) (r : Rational) (t : Sequence) (g : Fact) :
    ¬ Sequence.le (.index p r t) (.nil g) := fun h => h

theorem sequence_fork_covariant (p₁ p₂ : Fact) (r₁ r₂ : Rational)
    (t₁ t₂ : Sequence) (h : p₁.truth = p₂.truth) (hr : r₁ ≤ r₂) :
    Sequence.le (.index p₁ r₁ t₁) (.index p₂ r₂ t₂) := Or.inl ⟨h, hr⟩

theorem sequence_fork_contravariant (p₁ p₂ : Fact) (r₁ r₂ : Rational)
    (t₁ t₂ : Sequence) (h : p₁.truth ≠ p₂.truth) (hr : r₂ ≤ r₁) :
    Sequence.le (.index p₁ r₁ t₁) (.index p₂ r₂ t₂) := Or.inr ⟨h, hr⟩

theorem sequence_fork_complete (p₁ p₂ : Fact) (r₁ r₂ : Rational) (t₁ t₂ : Sequence) :
    Sequence.le (.index p₁ r₁ t₁) (.index p₂ r₂ t₂)
      → (p₁.truth = p₂.truth ∧ r₁ ≤ r₂) ∨ (p₁.truth ≠ p₂.truth ∧ r₂ ≤ r₁) := id

theorem sequence_tail_blind (p₁ p₂ : Fact) (r₁ r₂ : Rational)
    (t₁ t₂ u₁ u₂ : Sequence) :
    Sequence.le (.index p₁ r₁ t₁) (.index p₂ r₂ t₂)
      ↔ Sequence.le (.index p₁ r₁ u₁) (.index p₂ r₂ u₂) := Iff.rfl

-- ═════════════════════════════ LIMIT ══════════════════════════════

theorem limit_floor (f : Fact) (l : Limit) : Limit.le (.nil f) l := trivial

theorem limit_never_below (p : Fact) (s : Sequence) (t : Limit) (g : Fact) :
    ¬ Limit.le (.index p s t) (.nil g) := fun h => h

theorem limit_fork_covariant (p₁ p₂ : Fact) (s₁ s₂ : Sequence)
    (t₁ t₂ : Limit) (h : p₁.truth = p₂.truth) (hs : s₁ ≤ s₂) :
    Limit.le (.index p₁ s₁ t₁) (.index p₂ s₂ t₂) := Or.inl ⟨h, hs⟩

theorem limit_fork_contravariant (p₁ p₂ : Fact) (s₁ s₂ : Sequence)
    (t₁ t₂ : Limit) (h : p₁.truth ≠ p₂.truth) (hs : s₂ ≤ s₁) :
    Limit.le (.index p₁ s₁ t₁) (.index p₂ s₂ t₂) := Or.inr ⟨h, hs⟩

theorem limit_fork_complete (p₁ p₂ : Fact) (s₁ s₂ : Sequence) (t₁ t₂ : Limit) :
    Limit.le (.index p₁ s₁ t₁) (.index p₂ s₂ t₂)
      → (p₁.truth = p₂.truth ∧ s₁ ≤ s₂) ∨ (p₁.truth ≠ p₂.truth ∧ s₂ ≤ s₁) := id

theorem limit_tail_blind (p₁ p₂ : Fact) (s₁ s₂ : Sequence) (t₁ t₂ u₁ u₂ : Limit) :
    Limit.le (.index p₁ s₁ t₁) (.index p₂ s₂ t₂)
      ↔ Limit.le (.index p₁ s₁ u₁) (.index p₂ s₂ u₂) := Iff.rfl

-- ═════════════════════════════ SAMPLE ═════════════════════════════

/-- NEVER-BELOW: a signal response never sits below an initial condition —
the source's own margin: "this shouldn't happen without serious strain." -/
theorem sample_never_below (f₁ : Fact) (s : Limit) (f₂ : Fact) (r : Limit)
    (t : Sample) (g : Fact) (l : Limit) :
    ¬ Sample.le (.signal_response f₁ s f₂ r t) (.initial_condition g l) :=
  fun h => h

/-- THE SIGNAL FORK, whole law: same truth compares the RESPONSES forward;
different truth falls back to the STIMULI — not a reversed response. (The
sentence the gauge refresh tightened in prose, now definitional.) -/
theorem sample_signal_fork (f₁ f₂ : Fact) (s₁ s₂ r₁ r₂ : Limit) (t₁ t₂ : Sample) :
    Sample.le (.signal_response f₁ s₁ f₁ r₁ t₁) (.signal_response f₂ s₂ f₂ r₂ t₂)
      ↔ (f₁.truth = f₂.truth ∧ r₁ ≤ r₂) ∨ (f₁.truth ≠ f₂.truth ∧ s₁ ≤ s₂) :=
  Iff.rfl

/-- The initial/initial fork (covariant/contravariant on the carried Limits). -/
theorem sample_initial_fork (f₁ f₂ : Fact) (l₁ l₂ : Limit) :
    Sample.le (.initial_condition f₁ l₁) (.initial_condition f₂ l₂)
      ↔ (f₁.truth = f₂.truth ∧ l₁ ≤ l₂) ∨ (f₁.truth ≠ f₂.truth ∧ l₂ ≤ l₁) :=
  Iff.rfl

/-- The mixed arm: an initial condition CAN sit below a signal response
(forward on the same fork) — the asymmetry with `sample_never_below` is the
arrow of the record: initials precede responses, never the reverse. -/
theorem sample_mixed_fork (f₁ f₂ : Fact) (l₁ l₂ : Limit) (g : Fact) (r : Limit)
    (t : Sample) :
    Sample.le (.initial_condition f₁ l₁) (.signal_response f₂ l₂ g r t)
      ↔ (f₁.truth = f₂.truth ∧ l₁ ≤ l₂) ∨ (f₁.truth ≠ f₂.truth ∧ l₂ ≤ l₁) :=
  Iff.rfl

end Measurement.LadderImplicits
