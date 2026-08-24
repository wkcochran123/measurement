/-
# Ep2Implicits — Study and Trial, proved out (pre-Abstraction batch 2)

(operator-gated, 2026-08-13: "finish proving out … implicits from episode1 ->
(but not including) Abstraction. DO NOT IMPLEMENT ABSTRACTION for JAR.")

Batch 2 of the pre-Abstraction implicits: Episode 2's two order-carriers.
Same stratum fence as batch 1, held by the elaborator: this file imports
`Measurement.Episode2` and nothing else — Abstraction (Ep5:359) is
unreachable by construction, no sacred text is touched, the Jar is not
referenced. Proofs are rfl / trivial / intro / nomatch; expected census:
every theorem axiom-free.

WHAT THE LAWS SAY (each lived silently inside a `le` match until tonight):

STUDY — the description-refinement order:
* hypothesis vs hypothesis compares the WHOLE FACT (`f₁ = f₂` — like
  Rational, unlike the truth-forks); hypothesis-below-data compares only
  the TRUTH; and data NEVER sits below a hypothesis (the arm is literally
  the Bool `false` — richer descriptions do not round down).
* data vs data carries the standard fork (same-truth ⇒ Trials forward,
  different-truth ⇒ Trials reversed), tail-blind.

TRIAL — where the surprises live:
* THE TRUTH SHORTCUT: between hypotheses, a decidedly-true target fact
  ALONE places any hypothesis below it — `f.truth ∨ (s₁ ≤ s₂)`, and the
  left disjunct needs no volume comparison at all. The source's margin:
  "our hypothesis has no volume."
* THE HIDDEN INITIAL CONDITION: a signal response CAN sit below a
  hypothesis (`f₂ = hf ∨ l₂ ≤ hs`) — "we can create an hypothesis from a
  signal response! We have hidden our initial condition!" Note the exact
  INVERSION of Sample's asymmetry: in Sample, signal-below-initial is the
  forbidden arm ("serious strain"); in Trial, signal-below-hypothesis is
  lawful and the source celebrates it. Two rungs, opposite arrows — both
  now stated, neither smoothed over.
* THE RIGHT-INTERNAL ARM: the signal/signal comparison has THREE arms, and
  the third (`l₂₁ ≤ l₂₂`) reads only the RIGHT trial's own stimulus-versus-
  response — the left trial is not consulted at all. A trial whose own
  record is internally ordered admits anything beneath it.
-/
import Measurement.Episode2

namespace Measurement.Ep2Implicits

open Measurement

-- ═════════════════════════════ STUDY ══════════════════════════════

/-- Hypothesis vs hypothesis refines on the WHOLE fact (fact identity, not
just its truth — the Rational pattern on this rung). -/
theorem study_hypothesis_refines (f₁ f₂ : Fact) :
    Study.le (.hypothesis f₁) (.hypothesis f₂) ↔ f₁ = f₂ := Iff.rfl

/-- A hypothesis sits below a data point exactly on truth agreement. -/
theorem study_hypothesis_below_data (f₁ f₂ : Fact) (t : Trial) (s : Study) :
    Study.le (.hypothesis f₁) (.data f₂ t s) ↔ f₁.truth = f₂.truth := Iff.rfl

/-- Data NEVER rounds down to a hypothesis — the arm is the Bool `false`
itself; richer descriptions do not become poorer ones. -/
theorem study_data_never_below_hypothesis (f : Fact) (t : Trial) (s : Study)
    (g : Fact) : ¬ Study.le (.data f t s) (.hypothesis g) := fun h => nomatch h

/-- Data fork, covariant: same truth ⇒ the Trials are ordered forward. -/
theorem study_data_fork_covariant (f₁ f₂ : Fact) (t₁ t₂ : Trial) (s₁ s₂ : Study)
    (h : f₁.truth = f₂.truth) (ht : t₁ ≤ t₂) :
    Study.le (.data f₁ t₁ s₁) (.data f₂ t₂ s₂) := Or.inl ⟨h, ht⟩

/-- Data fork, contravariant: different truth ⇒ the same Trials, REVERSED. -/
theorem study_data_fork_contravariant (f₁ f₂ : Fact) (t₁ t₂ : Trial) (s₁ s₂ : Study)
    (h : f₁.truth ≠ f₂.truth) (ht : t₂ ≤ t₁) :
    Study.le (.data f₁ t₁ s₁) (.data f₂ t₂ s₂) := Or.inr ⟨h, ht⟩

/-- Data fork dichotomy: the two arms are the whole story (definitional). -/
theorem study_data_fork_complete (f₁ f₂ : Fact) (t₁ t₂ : Trial) (s₁ s₂ : Study) :
    Study.le (.data f₁ t₁ s₁) (.data f₂ t₂ s₂)
      → (f₁.truth = f₂.truth ∧ t₁ ≤ t₂) ∨ (f₁.truth ≠ f₂.truth ∧ t₂ ≤ t₁) := id

/-- Tail-blindness: the data comparison never consults the prior Study. -/
theorem study_tail_blind (f₁ f₂ : Fact) (t₁ t₂ : Trial) (s₁ s₂ u₁ u₂ : Study) :
    Study.le (.data f₁ t₁ s₁) (.data f₂ t₂ s₂)
      ↔ Study.le (.data f₁ t₁ u₁) (.data f₂ t₂ u₂) := Iff.rfl

-- ═════════════════════════════ TRIAL ══════════════════════════════

/-- The hypothesis/hypothesis law, whole: a true target fact OR a forward
volume comparison. -/
theorem trial_hypothesis_fork (f g : Fact) (s₁ s₂ : Sample) :
    Trial.le (.hypothesis g s₁) (.hypothesis f s₂) ↔ f.truth ∨ s₁ ≤ s₂ := Iff.rfl

/-- THE TRUTH SHORTCUT: a decidedly-true target fact alone suffices — no
volume comparison is consulted ("our hypothesis has no volume"). -/
theorem trial_truth_shortcut (f g : Fact) (s₁ s₂ : Sample) (h : f.truth) :
    Trial.le (.hypothesis g s₁) (.hypothesis f s₂) := Or.inl h

/-- A hypothesis sits below a signal response exactly on the first-in-time
volume comparison. -/
theorem trial_hypothesis_below_signal (g : Fact) (s₁ : Sample) (f : Fact)
    (s₂ : Sample) (f₂ : Fact) (r : Sample) (t : Trial) :
    Trial.le (.hypothesis g s₁) (.signal_response f s₂ f₂ r t) ↔ s₁ ≤ s₂ := Iff.rfl

/-- THE HIDDEN INITIAL CONDITION: a signal response CAN sit below a
hypothesis — by response-fact identity or response-volume — the source's
own celebration ("we have hidden our initial condition!"), and the exact
inversion of Sample's forbidden arm. -/
theorem trial_hidden_initial (f₁ : Fact) (l₁ : Sample) (f₂ : Fact) (l₂ : Sample)
    (t : Trial) (hf : Fact) (hs : Sample) :
    Trial.le (.signal_response f₁ l₁ f₂ l₂ t) (.hypothesis hf hs)
      ↔ f₂ = hf ∨ l₂ ≤ hs := Iff.rfl

/-- The signal/signal law, whole: three arms — covariant on the stimulus
pair, covariant on the response pair, or the right trial's own internal
order. -/
theorem trial_signal_fork (f₁₁ f₁₂ f₂₁ f₂₂ : Fact) (l₁₁ l₁₂ l₂₁ l₂₂ : Sample)
    (t₁ t₂ : Trial) :
    Trial.le (.signal_response f₁₁ l₁₁ f₁₂ l₁₂ t₁)
             (.signal_response f₂₁ l₂₁ f₂₂ l₂₂ t₂)
      ↔ ((f₁₁ = f₂₁) ∧ (l₁₁ ≤ l₂₁)) ∨ ((f₁₂ = f₂₂) ∧ (l₁₂ ≤ l₂₂)) ∨ (l₂₁ ≤ l₂₂) :=
  Iff.rfl

/-- THE RIGHT-INTERNAL ARM, named: the right trial's own stimulus-response
order admits ANY trial beneath it — the left record is never consulted. -/
theorem trial_right_internal (f₁₁ f₁₂ f₂₁ f₂₂ : Fact) (l₁₁ l₁₂ l₂₁ l₂₂ : Sample)
    (t₁ t₂ : Trial) (h : l₂₁ ≤ l₂₂) :
    Trial.le (.signal_response f₁₁ l₁₁ f₁₂ l₁₂ t₁)
             (.signal_response f₂₁ l₂₁ f₂₂ l₂₂ t₂) := Or.inr (Or.inr h)

/-- Tail-blindness: the signal comparison never consults the prior Trials. -/
theorem trial_tail_blind (f₁₁ f₁₂ f₂₁ f₂₂ : Fact) (l₁₁ l₁₂ l₂₁ l₂₂ : Sample)
    (t₁ t₂ u₁ u₂ : Trial) :
    Trial.le (.signal_response f₁₁ l₁₁ f₁₂ l₁₂ t₁)
             (.signal_response f₂₁ l₂₁ f₂₂ l₂₂ t₂)
      ↔ Trial.le (.signal_response f₁₁ l₁₁ f₁₂ l₁₂ u₁)
                 (.signal_response f₂₁ l₂₁ f₂₂ l₂₂ u₂) := Iff.rfl

end Measurement.Ep2Implicits
