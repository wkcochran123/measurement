import Measurement.RichardsonSelfNaming   -- the electron's OWN residual (the self-energy); Episode3-rooted, read-only

/-! # AlphaDedekind — the boundary of derivation, drawn to scale (blind, STRUCTURAL)

`bm-finish` deliverable 1 / seed `books/the_bound_explanation.md` §"The Dedekind sequence". **This is NOT a fourth
magnitude-hunt** — it does not chase 137; it DRAWS THE BOUND to scale. The bisection constructs α the way Dedekind
constructs a real — a cut, placed one bit at a time — writing the nines of `0.999…` (the residue tightening toward
the electron), and **halting at the floor ε** (the resolution below which the counter can no longer tell one
candidate from the next).

- **The nines it places = the structure it CAN see** (Ricci-visible).
- **The place it stops = THE BOUND** (the halt index).
- **The tail it cannot write = the magnitude** (Weyl, invisible by construction).

**Predicate = the electron's OWN residual** (`RichardsonSelfNaming.residueAtLevel` = the self-energy the electron
charges for the self-embrace) vs the floor — ⚠ **BLIND, never a target; NO `137036`/CODATA in the reading path.**
Landing = STRUCTURAL (the bound, not a value). Grade: the cut + halt = BUILT (`#print axioms = []`); "the halt is
the boundary of derivation / structure-near / magnitude-Weyl-far" = the seed's reading, interpretive MARKED.
Episode3/sacred read-only. -/

namespace Measurement.AlphaDedekind
open Measurement.RichardsonSelfNaming

/-- The floor ε: the counter's finest resolution — below this the electron's residual is indistinguishable from
null (`< 1` in the scaled count = the candidates can no longer be told apart). -/
def floorEps : Nat := 1

/-- The Dedekind cut, bit by bit: at each step the residue (`residueAtLevel`, the self-energy, halving toward the
electron) tightens the bracket by one nine of `0.999…`; HALT the first step the residue drops below the floor
(candidates indistinguishable). Structurally recursive on fuel. -/
def dedekindHalt : Nat → Nat → Nat
  | _, 0        => 0
  | n, (fuel+1) => if residueAtLevel n < floorEps then n else dedekindHalt (n + 1) fuel

/-- **THE BOUND** — the halt index: how many bits/nines the counting machine can place before the residue slips
below the floor. The near side (bits `< haltIndex`) is the structure it sees; the far side (the tail) is the
magnitude it cannot. -/
def haltIndex : Nat := dedekindHalt 0 512

-- ── THE BLIND FULL RUN-LOG (no target constant anywhere) ──
#eval haltIndex                                                   -- THE BOUND (bits placed = Ricci-visible structure)
#eval (residueAtLevel 0, residueAtLevel 10, residueAtLevel 30, residueAtLevel 50, residueAtLevel 58)  -- the nines tightening
-- THE CUT: the residue just BEFORE the halt (≥ ε, still resolvable) vs AT the halt (< ε, the tail begins):
#eval (residueAtLevel (haltIndex - 1), residueAtLevel haltIndex)
-- the far side the machine cannot write (the magnitude, invisible): the residue stays 0 past the bound:
#eval (residueAtLevel (haltIndex + 1), residueAtLevel (haltIndex + 20))

#print axioms haltIndex

end Measurement.AlphaDedekind
