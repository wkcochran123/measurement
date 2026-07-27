/-! # DivisionNeedle — the QUANTITATIVE needle (self-founding trunk, task 1, first stone).

SPEC.md (0c-i2): replace the BINARY needle — `Quot.sound`, which identifies iff the residue is
null and DISCARDS the amount — with the DIVISION ALGORITHM, the QUANTITATIVE needle that computes
the REMAINDER (= how much residue). Where an identification was really a computation, this makes
it one: the needle defs are `abbrev`s, so the identification unfolds in defeq and holds by `rfl`
— computed at elaboration, no axiom.

LANE + FENCES (operator greenlight 2026-07-26, tasks 1-6; Beastmaster's three gates):
- 16+ lane, PURE LEAF: no imports at all. Episodes 1-16 are UNTOUCHED (the review-tripwire never
  fires); the sanctioned binary needle `Episode15.selection_sound` STANDS exactly as it is.
- This file is the INSTRUMENT, not the rewiring: it exhibits constructive identification on the
  device's own quantities with an axiom print the build displays. Re-pointing any existing
  call-site at it is LATER work, site by site, each gated (sacred sites → operator review).
  A first stone is not the trunk; nothing here claims the device's axiom basis has changed.
- The jar is untouched by construction: no existing file is modified, so the jar chain and its
  oleans are byte-identical.

GRADE OFF THE BUILD: every claim about axioms below is the `#print axioms` directive's output,
not prose. The load-bearing identification theorems are by `rfl`/`decide` and print axiom-FREE;
the general total-correctness spec prints what it prints (reported, not asserted in advance). -/

namespace Measurement.DivisionNeedle

/-- The device's own division, earned by counted subtraction: remove the divisor and count the
    removals. `fuel` is a PROVABLE bound (each step removes `d ≥ 1`, so `n` steps always
    suffice — the `FloorSqrt` fuel discipline). Returns (quotient, REMAINDER): the box and the
    residue together — the quantitative reading the binary needle discarded. -/
def divModGo : Nat → Nat → Nat → Nat × Nat
  | 0, n, _ => (0, n)
  | fuel + 1, n, d =>
    if 0 < d ∧ d ≤ n then
      let qr := divModGo fuel (n - d) d
      (qr.1 + 1, qr.2)
    else
      (0, n)

/-- The division: quotient (the box) and remainder (the residue) of a reading at a floor. -/
def divMod (n d : Nat) : Nat × Nat := divModGo n n d

/-- Total correctness of the fuel loop: with enough fuel and a positive floor, the computed
    (quotient, remainder) reconstruct the reading exactly, and the remainder sits under the
    floor. Proved by induction on the fuel, Mathlib-free. -/
theorem divModGo_spec (fuel n d : Nat) (hd : 0 < d) (hn : n ≤ fuel) :
    d * (divModGo fuel n d).1 + (divModGo fuel n d).2 = n ∧ (divModGo fuel n d).2 < d := by
  induction fuel generalizing n with
  | zero =>
    have hn0 : n = 0 := Nat.le_zero.mp hn
    subst hn0
    exact ⟨rfl, hd⟩
  | succ fuel ih =>
    by_cases h : 0 < d ∧ d ≤ n
    · have hrec : n - d ≤ fuel := by omega
      obtain ⟨hq, hr⟩ := ih (n - d) hrec
      simp only [divModGo, if_pos h]
      refine ⟨?_, hr⟩
      -- distribute d * (q + 1) so the goal is linear in the atom (d * q), then close
      rw [Nat.mul_add, Nat.mul_one]
      omega
    · have hnd : n < d := Nat.lt_of_not_le (fun hle => h ⟨hd, hle⟩)
      simp only [divModGo, if_neg h]
      exact ⟨by omega, hnd⟩

#print axioms divModGo_spec

/-- Total correctness at the surface: `divMod` reconstructs the reading and bounds the residue. -/
theorem divMod_spec (n d : Nat) (hd : 0 < d) :
    d * (divMod n d).1 + (divMod n d).2 = n ∧ (divMod n d).2 < d :=
  divModGo_spec n n d hd (Nat.le_refl n)

#print axioms divMod_spec

/-- The box of a reading at a floor (the quotient). `abbrev`: unfolds in defeq. -/
abbrev box (reading floor : Nat) : Nat := (divMod reading floor).1

/-- The residue of a reading at a floor (the remainder) — the quantity the binary needle
    threw away. `abbrev`: unfolds in defeq. -/
abbrev residue (reading floor : Nat) : Nat := (divMod reading floor).2

/-- CONSTRUCTIVE IDENTIFICATION: two readings identify at a floor iff the division algorithm
    computes the same box. A `Bool` the kernel evaluates — identification by computation,
    where the binary needle identified by axiom. -/
abbrev identifies (a b floor : Nat) : Bool := box a floor == box b floor

set_option linter.unnecessarySimpa false in
/-- The identification is exactly same-box — the bridge from the computed `Bool` to the
    propositional reading. -/
theorem identifies_iff (a b floor : Nat) :
    identifies a b floor = true ↔ box a floor = box b floor := by
  simpa using Nat.beq_eq (box a floor) (box b floor)

#print axioms identifies_iff

/-! ## The needle on the device's own quantities (the real inputs)

`C = 18` (the measured displacement, one coupling read on one of its three paths) and `T = 5`
(the target) are the device's own; the exhibits below show the quantitative needle computing on
them — by `rfl`, at elaboration, with nothing assumed. These are exhibits of the INSTRUMENT
working; they claim nothing about α, the jar, or any identification the sacred needle currently
carries. -/

/-- The quantitative reading at the crossing's own pair: eighteen at floor five is box 3,
    residue 3 — the remainder the binary needle would have discarded, computed and kept.
    By `rfl`: the identification-by-computation, no axiom. -/
theorem eighteen_at_five : divMod 18 5 = (3, 3) := rfl

#print axioms eighteen_at_five

/-- A reading identifies with itself by computation (`rfl`, no axiom): the reflexive case the
    binary needle needed no axiom for either — recovered here as evaluation. -/
theorem identifies_self : identifies 18 18 5 = true := rfl

/-- Two readings the floor separates are DISTINGUISHED by computation: box 18 5 = 3 ≠ 1 =
    box 5 5. The binary needle reported only "not identified"; the quantitative needle also
    holds their residues (3 and 0). By `rfl`. -/
theorem distinguishes_across_boxes : identifies 18 5 5 = false := rfl

/-- Same box, different residues: 18 and 16 share box 3 at floor 5 — the binary verdict
    "identified" — while the quantitative needle retains what it cost: residues 3 and 1.
    The needle refines, never coarsens, the binary reading. By `rfl`. -/
theorem same_box_residues_kept :
    identifies 18 16 5 = true ∧ residue 18 5 = 3 ∧ residue 16 5 = 1 := ⟨rfl, rfl, rfl⟩

#print axioms identifies_self
#print axioms distinguishes_across_boxes
#print axioms same_box_residues_kept

/-- The division agrees with the kernel's own arithmetic on the real inputs (a cross-check
    that the earned division and the built-in one read the same box and residue here). -/
theorem agrees_with_kernel_at_crossing : divMod 18 5 = (18 / 5, 18 % 5) := rfl

#print axioms agrees_with_kernel_at_crossing

#eval s!"quantitative needle: divMod 18 5 = {divMod 18 5} (box, residue) — the remainder kept, not discarded"
#eval s!"identifies 18 16 at floor 5? {identifies 18 16 5} (same box 3; residues {residue 18 5} vs {residue 16 5} retained)"

end Measurement.DivisionNeedle
