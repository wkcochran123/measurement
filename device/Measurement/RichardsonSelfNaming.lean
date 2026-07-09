import Measurement.Episode3   -- Episode3 SACRED, READ-ONLY: ε_mach = "α", per-level = 1/2^n. Cited, never edited.

/-! # RichardsonSelfNaming — the self-naming sequence extrapolated to its fixed point (blind)

Kodo Turn 96 / operator: the HONEST number-path that replaces the stripped `137036`. Instead of *inserting* the
target, **extrapolate the construction's OWN per-level self-naming sequence to its fixed point.**

- **The sequence is the construction's own** (Episode3, SACRED/read-only): *"ε_m … we shall call this number α; at
  each level a more and more precise number; the α at each level is the smallest fraction recognizable"* — i.e.
  `α(n) = 1/2^n` (the per-level naming of box-1 = the electron = the second variation, NamingClose). **NOT** the
  possibly-tuned WIP `Meanwhile53.richardsonAlphaEstimateScaledAt18` outputs — those are quarantined (agreement
  inconclusive, divergence informs); this is built FRESH off the read-only fact.
- **The extrapolation order is FORCED by the construction, not chosen:** the sequence HALVES per level (ρ=½ —
  Episode3's own convergence, the BFGS-secant / δ² structure). That fixes Richardson order p=1. Choosing the order
  to hit a target would be fishing in a Richardson costume; p=1 is forced by the observed halving.
- **Extrapolate the name "electron" TO "electron"** = the self-naming to its fixed point: `R = 2·α(n+1) − α(n)`
  cancels the geometric leading term. The name (`0.999…`, the approximation) extrapolated to the thing (`1`) leaves
  the residue **closed to null** — `1 = 0.999…`.

**BLIND: no `137036`/`137035999` anywhere. Report whatever falls out; refuse coincidences. Landing: FULL only if a
real number falls out of THIS blind sequence with the forced order; else STRUCTURAL (the closure = 1=0.999 =
count-to-3).** Episode3 read-only (this is 16+; no sacred edit). -/

namespace Measurement.RichardsonSelfNaming

/-- The construction's OWN per-level self-naming value (Episode3, read-only: ε_mach="α" at level n). Scaled by
`10^18` for exact integer arithmetic (`10^18 = 2^18·5^18`, so exact for `n ≤ 18`). -/
def alphaAtLevel (n : Nat) : Nat := 10 ^ 18 / 2 ^ n

/-- The FORCED-order (p=1, from the ρ=½ halving) Richardson extrapolant of the self-naming sequence. Cancels the
geometric leading term → the fixed point (the `1=0.999…` closure). -/
def selfNamingExtrapolant (n : Nat) : Int := 2 * (alphaAtLevel (n + 1) : Int) - (alphaAtLevel n : Int)

/-- The per-level residue (name − thing) : `α(n) − α(n+1)` — how much the name has NOT yet closed to the thing. -/
def residueAtLevel (n : Nat) : Nat := alphaAtLevel n - alphaAtLevel (n + 1)

-- ── BLIND FULL RUN-LOG (no target constant anywhere) ──
#eval (alphaAtLevel 0, alphaAtLevel 1, alphaAtLevel 2, alphaAtLevel 3, alphaAtLevel 4)   -- the halving sequence
#eval (residueAtLevel 0, residueAtLevel 1, residueAtLevel 2, residueAtLevel 3)           -- name−thing, ρ=½, →0
-- THE EXTRAPOLANT — the name "electron" extrapolated TO "electron" (the fixed point):
#eval (selfNamingExtrapolant 0, selfNamingExtrapolant 1, selfNamingExtrapolant 2,
       selfNamingExtrapolant 3, selfNamingExtrapolant 10, selfNamingExtrapolant 16)

end Measurement.RichardsonSelfNaming
