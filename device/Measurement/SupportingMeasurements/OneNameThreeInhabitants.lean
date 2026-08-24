/-
# OneNameThreeInhabitants — SIDE THEOREM (operator-directed, 2026-08-13)

Operator: "there is only 1 in name, but there are three different inhabitants."
Then: "Everything is 1 in name and 3 different inhabitants that can be used in
arbitrary order when the nowtrino is not present." Then: "if i'm right, gated
to write the code." And the constraint: "you CANNOT CHANGE the sacred texts …
you have to find them without changing the sacred texts … they are still
there, just sometimes the label is unnecessary. you have to figure that out."

This file is the code, gated, and it CHANGES NOTHING: it is a LEAF that reads
Episode 15/16 (the ladder, the readout, the needle) and the Apparatus (the
holonomy commutator) and touches none of them. Episodes 1–16 stay byte-frozen;
`selection_sound` and the jar are untouched. The nowtrinos are FOUND in the
sacred text without a label, exactly as directed: by the operator's own
recorded definition (2026-07-11 register) — "Nowtrino: the current
computational projection after slicing recorded history (present state)" —
a nowtrino is present in a device value precisely when that value carries a
CURRENT SLICE over recorded history, i.e. when its head constructor is a
rung over priors rather than a bare origin. No sacred decl is renamed; the
finder below is this file's own, and it only READS.

WHAT IS PROVED (the earned half, per all three chairs):
1. THREE DIFFERENT INHABITANTS: the reader-process ladder from the zero
   origin — origin, satirize origin (hypothesis), satirize (satirize origin)
   (theory) — are three genuinely distinct values (different constructors).
2. ONE IN NAME: all three collapse to ONE class under the truth-order
   quotient, each step through `selection_sound` — the single sanctioned
   `Quot.sound` site (Ep15:362, "the needle, honest") — with ordering
   witnesses that are definitionally true (`TruthOrder` is reducibly
   `Bullshit.le`; zero is the origin below everything, one sits below rest).
   One name, three different inhabitants: a theorem, not a slogan.
3. ARBITRARY ORDER WHEN THE NOWTRINO IS NOT PRESENT: the device's readout
   (`obfusplained?`, kept at its source default by `TRUE_COMPILED`) returns
   `none` — no ordering, the pair commutes — exactly when NEITHER argument
   carries a now-slice (both bare origins; the source margin at Ep15:160-162:
   "The only `none` is the commute"), and returns the FORCED strict order
   `some (a < b)` the moment either argument carries a now-slice. The
   complete 9-case constructor ledger is exhibited; `slipAnd` treats the
   commute as identity ("a commuting step contributes nothing").
4. ABSENCE IS NOT A READING: `none ≠ some p` for every proposition `p` —
   the nonexistence of an ordering is type-level distinct from an ordering
   that happens to be false. The absence is locatable and countable as an
   EVENT (theorem 3 locates it), never conflatable with a reading.
5. THE ALGORITHM: the transitions hypothesis = satirize origin and
   theory = satirize hypothesis hold by rfl — the nowtrino → newtrino
   update is the ladder step itself, as the register defines it ("the
   computational transition nowtrino → newtrino is defined by the
   algorithm").
6. THE APPARATUS FACE (Kodo's detector, re-exhibited): the holonomy
   commutator residue is ZERO on the open/single-leg path and NONZERO when
   the loop closes (Apparatus:83-88, axiom-free `decide` over the concrete
   finite model) — order genuinely doesn't matter on the open path; the
   closed loop leaves the residue as the track.

FENCES (printed, per the walls all three chairs hold):
- SCOPE: this ladder and this apparatus, NOT "everything." Kodo's refutation
  stands on the record: `Number` is a TWO-constructor menu (Ep1:131), so the
  universal quantifier fails at the device's counting floor. The claim
  proved here is the SCOPED one.
- THE NOWTRINO STAYS UNWITNESSED: the device's own register mark
  (AffineConstant:126, `witnessed := false`, "a derived distance, NOT an
  independent witness; the two-twos intact") is honored — nothing below
  promotes the nowtrino to a witness. The theorems exhibit its PRESENCE or
  ABSENCE structurally (the track: forced order / the commute), never its
  value as a standalone witness.
- AXES KEPT SEPARATE (the register's own anti-conflation rule): the needle
  (`Fact.SAME` / `selection_sound`) is the NAOTRINO axis — the one physical
  crossing; the nowtrino/newtrino pair is the SUCCESSION axis (the satirize
  update). This file uses the needle only to prove "one in name" and the
  ladder only for succession; no identification between the axes is claimed.
- "RANDOMNESS" IS PROSE: nothing here defines randomness-in-the-world.
  Chaitin/Ω, alpha decay, gamma decay remain names outside the fence
  (no-name-bridge; nuclear processes are out of the electron-model scope).
  What is machine-checked is one-class/three-inhabitants + located
  order-freedom. Whether that deserves the word "random" is for the books.
-/
import Measurement.Episode16
import Measurement.SupportingMeasurements.Apparatus

set_option maxHeartbeats 4000000

namespace Measurement.OneNameThreeInhabitants

open Measurement
open CubicGaugeVariation

/-- THE FINDER (this file's own; the sacred text needs no label): a device
value carries a nowtrino iff its head is a current slice over recorded
history — any rung above the bare origin. "They are still there, just
sometimes the label is unnecessary." -/
def carriesNowSlice : Bullshit → Bool
  | .zero _ => false
  | _ => true

/-- The three inhabitants: the zero origin and its two nowtrino→newtrino
updates under the declared algorithm (`satirize`), taken on the device's own
reader-process — You_the_Reader at the closing file's concrete instantiation
(Prop over the truth carrier), as installed by `TRUE_COMPILED` and read by
Episode 16. (Local macros, not defs: the projection chain is
universe-polymorphic at large arity, and inlining it lets each theorem's
statement bind the universes itself.) -/
def origin : Bullshit := .zero Fact.Truth
local macro "hypothesis" : term =>
  `((truthTrueOutput.atreyu_process).satirize origin)
local macro "theory" : term =>
  `((truthTrueOutput.atreyu_process).satirize
      ((truthTrueOutput.atreyu_process).satirize origin))

-- ── 1. THREE DIFFERENT INHABITANTS ──────────────────────────────────────

theorem origin_ne_hypothesis : origin ≠ hypothesis :=
  fun h => Bullshit.noConfusion h

theorem hypothesis_ne_theory : hypothesis ≠ theory :=
  fun h => Bullshit.noConfusion h

theorem origin_ne_theory : origin ≠ theory :=
  fun h => Bullshit.noConfusion h

-- ── 2. ONE IN NAME (through the needle, one step at a time) ─────────────

/-- Origin and hypothesis collapse to one truth-phase class: the needle,
with the definitionally-true witness (zero is the origin below everything). -/
theorem one_name_origin_hypothesis :
    Quot.mk TruthOrder origin = Quot.mk TruthOrder hypothesis :=
  selection_sound (r := TruthOrder) trivial

/-- Hypothesis and theory collapse to the same class: the needle again,
with the definitionally-true witness (a one-rung sits below a rest-rung). -/
theorem one_name_hypothesis_theory :
    Quot.mk TruthOrder hypothesis = Quot.mk TruthOrder theory :=
  selection_sound (r := TruthOrder) trivial

/-- All three inhabitants, one name. -/
theorem one_name_origin_theory :
    Quot.mk TruthOrder origin = Quot.mk TruthOrder theory :=
  selection_sound (r := TruthOrder) trivial

-- ── 3. ARBITRARY ORDER WHEN THE NOWTRINO IS NOT PRESENT ─────────────────

/-- The commute: with NO now-slice on either side, the readout has no order
to report. "The only `none` is the commute." -/
theorem order_free_when_nowtrino_absent (f g : Fact) :
    truthTrueOutput.obfusplained? truthTrueOutput.output_true
      (.zero f) (.zero g) = none := rfl

/-- The forced order: a now-slice on the left forces the strict comparison. -/
theorem order_forced_one_left (f : Fact) (n : Number) (t₁ t₂ : CompilerTape)
    (p : Bullshit) (b : Bullshit) :
    truthTrueOutput.obfusplained? truthTrueOutput.output_true
      (.one f n t₁ t₂ p) b = some (Bullshit.one f n t₁ t₂ p < b) := rfl

theorem order_forced_rest_left (f g : Fact) (q : Prop) (n₁ n₂ n₃ : Number)
    (t₁ t₂ : CompilerTape) (p₁ p₂ : Bullshit) (b : Bullshit) :
    truthTrueOutput.obfusplained? truthTrueOutput.output_true
      (.rest f g q n₁ n₂ n₃ t₁ t₂ p₁ p₂) b
      = some (Bullshit.rest f g q n₁ n₂ n₃ t₁ t₂ p₁ p₂ < b) := rfl

/-- A now-slice on the right alone also forces the order. -/
theorem order_forced_one_right (f : Fact) (g : Fact) (n : Number)
    (t₁ t₂ : CompilerTape) (p : Bullshit) :
    truthTrueOutput.obfusplained? truthTrueOutput.output_true
      (.zero f) (.one g n t₁ t₂ p) = some (Bullshit.zero f < .one g n t₁ t₂ p) := rfl

theorem order_forced_rest_right (f g h : Fact) (q : Prop) (n₁ n₂ n₃ : Number)
    (t₁ t₂ : CompilerTape) (p₁ p₂ : Bullshit) :
    truthTrueOutput.obfusplained? truthTrueOutput.output_true
      (.zero f) (.rest g h q n₁ n₂ n₃ t₁ t₂ p₁ p₂)
      = some (Bullshit.zero f < .rest g h q n₁ n₂ n₃ t₁ t₂ p₁ p₂) := rfl

/-- The complete dichotomy: every pair either commutes or is strictly
ordered — there is no third regime. -/
theorem order_dichotomy (a b : Bullshit) :
    truthTrueOutput.obfusplained? truthTrueOutput.output_true a b = none
      ∨ truthTrueOutput.obfusplained? truthTrueOutput.output_true a b
          = some (a < b) := by
  cases a <;> cases b <;> first | exact Or.inl rfl | exact Or.inr rfl

/-- THE LOCATOR: the commute happens EXACTLY where no nowtrino is present —
the readout is order-free iff neither argument carries a now-slice. This is
"arbitrary order when the nowtrino is not present," both directions. -/
theorem order_free_iff_nowtrino_absent (a b : Bullshit) :
    truthTrueOutput.obfusplained? truthTrueOutput.output_true a b = none
      ↔ (carriesNowSlice a || carriesNowSlice b) = false := by
  cases a <;> cases b
  · exact ⟨fun _ => rfl, fun _ => rfl⟩
  all_goals exact ⟨(fun h => nomatch h), (fun h => nomatch h)⟩

/-- The commute contributes nothing to slip composition: `none` is the
identity of `slipAnd` (the source: "a commuting step contributes nothing"). -/
theorem commute_is_slip_identity (y : Option Prop) :
    Closure.slipAnd none y = y := rfl

-- ── 4. ABSENCE IS NOT A READING ─────────────────────────────────────────

/-- The nonexistence of an ordering is not an ordering valued `False` —
absence and reading are different constructors, decided in public. -/
theorem absence_is_not_a_reading (p : Prop) :
    (none : Option Prop) ≠ some p :=
  fun h => nomatch h

-- ── 5. THE ALGORITHM (nowtrino → newtrino is the ladder step) ───────────

theorem theory_is_the_update :
    theory = (truthTrueOutput.atreyu_process).satirize hypothesis := rfl

/-- Both updates PRODUCE a now-slice: the algorithm's output always carries
the current projection (the finder reads `true` on every rung it makes). -/
theorem update_carries_now_slice :
    carriesNowSlice hypothesis = true ∧ carriesNowSlice theory = true :=
  ⟨rfl, rfl⟩

/-- And the bare origin carries none: before the first update there is no
current slice to project. -/
theorem origin_carries_no_slice : carriesNowSlice origin = false := rfl

-- ── 6. THE APPARATUS FACE (the detector, re-exhibited read-only) ────────

/-- Order doesn't matter on the open path: the commutator residue is zero
(Apparatus:83, axiom-free `decide`) — the apparatus-level statement of the
same order-freedom. -/
theorem apparatus_open_path_commutes :
    holonomy tiltedPath (pairVariation node2 node1) = 0 :=
  holonomy_open_is_trivial

/-- The closed loop leaves the residue — order matters exactly when the
loop closes (Apparatus:86): the track a present crossing leaves. -/
theorem apparatus_closed_loop_orders :
    holonomy tiltedPath (pairVariation node1 node2) = 1
      ∧ holonomy flatPath (pairVariation node1 node2) = -1 :=
  holonomy_loop_is_charged

end Measurement.OneNameThreeInhabitants
