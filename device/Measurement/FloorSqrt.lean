/-! # FloorSqrt — a PROVEN, Mathlib-free integer floor-sqrt (proof-debt #1 discharge, in-tree).

Operator-approved (2026-07-23, item 3) + Kodo GATE 1. The device measures π off its orbit by an
Archimedes squeeze (`ArchimedesPi`) whose geometric-mean step needs an integer square root. This module
provides that sqrt AND its total-correctness proof, so the measurement's walls trace through a PROVEN
floor-sqrt rather than an unproven Newton loop.

`floorSqrt_correct (n) : (floorSqrt n)*(floorSqrt n) ≤ n ∧ n < (floorSqrt n + 1)*(floorSqrt n + 1)` —
axiom-clean [propext, Quot.sound], NO sorryAx, NO Classical.choice, fully Mathlib-free. `floorSqrt` uses
`fuel := n` (a PROVABLE fuel: the Newton iterate strictly decreases ≥1/step to the fixpoint, so `n` steps
always suffice — no log-convergence bound needed); at runtime/`decide` it exits early at the fixpoint
(~log n levels), so it is efficient at the ×1e18 measurement scale. Reusable anywhere the device floors a
root. The `.1` component (undershoot `floorSqrt n · floorSqrt n ≤ n`) is the CONSERVATIVENESS certificate
the squeeze relies on.
-/

namespace Measurement.FloorSqrt
-- ── the three banked lemmas (crux + amgm_mul + step_no_undershoot), Mathlib-free ──
theorem amgm_mul (x r : Nat) : (2 * r - x) * x ≤ r * r := by
  rcases Nat.lt_or_ge r x with hxr | hxr
  · obtain ⟨y, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_lt hxr)
    rcases Nat.lt_or_ge r y with hy | hy
    · have : 2 * r - (r + y) = 0 := by omega
      rw [this]; omega
    · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hy
      have e2 : 2 * (y + m) - (y + m + y) = m := by omega
      rw [e2]
      calc m * (y + m + y) = m * (y + m) + m * y := by rw [← Nat.mul_add]
        _ ≤ (y + m) * m + (y + m) * y := by
            have a2 : m * y ≤ (y + m) * y := Nat.mul_le_mul_right y (Nat.le_add_left m y)
            have a1 : m * (y + m) = (y + m) * m := Nat.mul_comm _ _
            omega
        _ = (y + m) * (y + m) := by rw [← Nat.mul_add]; congr 1; omega
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hxr
    have e1 : 2 * (x + k) - x = x + 2 * k := by omega
    rw [e1]
    calc (x + 2 * k) * x = (x + k) * x + k * x := by rw [← Nat.add_mul]; congr 1; omega
      _ ≤ (x + k) * x + (x + k) * k := by
          have : k * x ≤ (x + k) * k := by
            rw [Nat.mul_comm k x]; exact Nat.mul_le_mul_right k (Nat.le_add_right x k)
          omega
      _ = (x + k) * (x + k) := by rw [← Nat.mul_add]

theorem crux (x r : Nat) (hx : 1 ≤ x) : 2 * r ≤ x + r * r / x := by
  rcases Nat.lt_or_ge x (2 * r) with h | h
  · have hx2 : (2 * r - x) + x = 2 * r := by omega
    have hle : 2 * r - x ≤ r * r / x := by rw [Nat.le_div_iff_mul_le hx]; exact amgm_mul x r
    calc 2 * r = (2 * r - x) + x := hx2.symm
      _ ≤ r * r / x + x := Nat.add_le_add_right hle x
      _ = x + r * r / x := Nat.add_comm _ _
  · exact Nat.le_trans h (Nat.le_add_right x _)

theorem step_no_undershoot (n x r : Nat) (hx : 1 ≤ x) (hr : r * r ≤ n) : r ≤ (x + n / x) / 2 := by
  have hc : 2 * r ≤ x + r * r / x := crux x r hx
  have hmono : r * r / x ≤ n / x := Nat.div_le_div_right hr
  have hkey : 2 * r ≤ x + n / x := Nat.le_trans hc (Nat.add_le_add_left hmono x)
  exact (Nat.le_div_iff_mul_le (by decide)).mpr (by rw [Nat.mul_comm]; exact hkey)

-- ── the loop (fuel := n companion — provable fuel, no log-convergence bound needed) ──
def isqrtLoop : Nat → Nat → Nat → Nat
  | 0, _, x => x
  | fuel + 1, n, x =>
      if (x + n / x) / 2 < x then isqrtLoop fuel n ((x + n / x) / 2) else x

theorem fixpoint_lower (n x : Nat) (hx : 1 ≤ x) (hfix : ¬ ((x + n / x) / 2 < x)) : x * x ≤ n := by
  have h2 : x ≤ n / x := by omega
  have h3 : x * x ≤ x * (n / x) := Nat.mul_le_mul_left x h2
  have h4 : x * (n / x) ≤ n := Nat.mul_div_le n x
  omega

theorem isqrtLoop_spec (fuel : Nat) : ∀ (n x : Nat), 2 ≤ n → 1 ≤ x →
    n < (x + 1) * (x + 1) → x ≤ fuel →
    (isqrtLoop fuel n x) * (isqrtLoop fuel n x) ≤ n ∧
    n < (isqrtLoop fuel n x + 1) * (isqrtLoop fuel n x + 1) := by
  induction fuel with
  | zero => intro n x _ hx1 _ hfuel; omega
  | succ fuel ih =>
      intro n x hn hx1 hub hfuel
      rw [isqrtLoop]
      by_cases hlt : (x + n / x) / 2 < x
      · rw [if_pos hlt]
        have hub' : n < ((x + n / x) / 2 + 1) * ((x + n / x) / 2 + 1) := by
          rcases Nat.lt_or_ge n (((x + n / x) / 2 + 1) * ((x + n / x) / 2 + 1)) with hh | hh
          · exact hh
          · have := step_no_undershoot n x ((x + n / x) / 2 + 1) hx1 hh
            omega
        have hx1' : 1 ≤ (x + n / x) / 2 := by
          rcases Nat.eq_zero_or_pos ((x + n / x) / 2) with h0 | h0
          · rw [h0] at hub'; simp at hub'; omega
          · exact h0
        have hfuel' : (x + n / x) / 2 ≤ fuel := by omega
        exact ih n ((x + n / x) / 2) hn hx1' hub' hfuel'
      · rw [if_neg hlt]
        exact ⟨fixpoint_lower n x hx1 hlt, hub⟩

def floorSqrt (n : Nat) : Nat := if n ≤ 1 then n else isqrtLoop n n n

theorem floorSqrt_correct (n : Nat) :
    (floorSqrt n) * (floorSqrt n) ≤ n ∧ n < (floorSqrt n + 1) * (floorSqrt n + 1) := by
  unfold floorSqrt
  by_cases h : n ≤ 1
  · simp only [h, if_true]
    rcases n with _ | _ | n
    · decide
    · decide
    · omega
  · simp only [h, if_false]
    have hn : 2 ≤ n := by omega
    have hub : n < (n + 1) * (n + 1) := by rw [Nat.mul_succ]; omega
    exact isqrtLoop_spec n n n hn (by omega) hub (Nat.le_refl n)

#print axioms floorSqrt_correct
