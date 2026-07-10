/-
PLAN_RFC §1.2 — the α bound, self-contained (prune-ready), BLIND.

The operator's given relation: **α = m² / (4π)**, where m = the second-variation residue
(mass = second difference; NamingClose:104 `gateaux_indist_frechet`) read against the device's
OWN resolution floor.

- The BARE mass is 0: the second-variation residue sits BELOW the floor, so the box collapses
  (gateaux ≡ frechet) and it reads 0.  α(bare) = 0² / (4π) = 0.   →  a1 = 0.
- a2 = floor² / (4π): the residue at the smallest size the device could still fail to resolve
  (the Dedekind / count-halting floor = one count).
- The guess = a2 (the smallest resolvable α).

BLIND: no `137036`, no CODATA inserted; the floor is the device's own resolution; 4π is the
geometric constant of the GIVEN relation, not the answer. Scaled-integer, NO Floats. Self-contained
(Nat only) so the convergent target stays sacred-only and prune-ready. Sacred Ep1-15 untouched.
-/
namespace Measurement.AlphaBound

/-- The device's resolution floor: the smallest residue it can distinguish (one count). -/
def floorEps : Nat := 1

/-- Read a second-variation residue against the floor: below the floor the box collapses
    (gateaux ≡ frechet) and it reads 0. -/
def readResidue (residue : Nat) : Nat := if residue < floorEps then 0 else residue

/-- The bare mass: the sub-resolution residue → 0. -/
def m_bare : Nat := readResidue 0
theorem bare_mass_is_zero : m_bare = 0 := rfl

/-- The smallest residue the device could still fail to resolve = the floor. -/
def m_floor : Nat := floorEps

-- α = m² / (4π), scaled by 10⁹.  4π is the geometric constant of the given relation.
def E9 : Nat := 1000000000
def fourPiE9 : Nat := 12566370614          -- 4π × 10⁹  (π = 3.14159265358…)

/-- α(m) scaled by 10⁹ = m² · 10¹⁸ / (4π·10⁹), truncated (the floor is a cut). -/
def alphaE9 (m : Nat) : Nat := (m * m * E9 * E9) / fourPiE9

def a1    : Nat := alphaE9 m_bare          -- 0
def a2    : Nat := alphaE9 m_floor         -- 1/(4π), scaled
def guess : Nat := a2

-- THE BOUND (blind, device-derived), scaled by 10⁹:
#eval (a1, guess, a2)
theorem bound_ordered : a1 < a2 := by decide
theorem lower_is_bare_mass : a1 = 0 := rfl
#eval s!"0 = a1={a1} < alpha <= a2={a2}   (scaled 1e9; a2 = 1/(4pi), i.e. inv-alpha >= 4pi)"

end Measurement.AlphaBound

-- footprint (grade off #print):
#print axioms Measurement.AlphaBound.bound_ordered
#print axioms Measurement.AlphaBound.bare_mass_is_zero
