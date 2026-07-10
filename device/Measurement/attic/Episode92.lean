namespace Measurement.Reader

/-
__EPISODE 92__: _Whelmed? -- the Band the Magnitude Gate Was Named For_

MAGNITUDE's gate is `whelmed?` (Episode6).  Its job is NOT the covariance/contravariance domination
that the Episode6 default body computes -- that is the SIGN gate, the charge.  Its job is the BAND:
did the reading land in range?  A measurement is

  underwhelmed   when it dropped to / below the NOISE FLOOR   (lost in the noise)
  whelmed        when it cleared the floor and stayed under MAX SIZE   (a real reading)
  overwhelmed    when it ran past the ceiling   (saturated, clipped)

The floor is the δ²≥0 noise floor proved across 17-90 (`sqDiag_nonneg`, `chainEnergy_nonneg`): a
square cannot read below zero.  The ceiling is the squeeze / pigeonhole / Weierstrass bound
(`residual_squeezed_between_zero_and_bound` Ep27, `tag_lt_three` Ep48): the reading cannot run past
the bound.  Both edges are already theorems; here we read the band off a size and finally ASK the
question the name always meant -- as a function, not a narrated comment.
-/

/-- The size of a reading: its popcount, the count of funges it carries.  The electron ramp `1^p 0…`
has size `p`. -/
def size (bs : List Bool) : Nat := (bs.filter id).length

/-- MAGNITUDE's gate, the band.  A reading of magnitude `s` is whelmed iff it cleared the noise floor
and stayed at or under the max size: `noiseFloor < s ≤ maxSize`. -/
def whelmed? (noiseFloor maxSize s : Nat) : Bool :=
  decide (noiseFloor < s ∧ s ≤ maxSize)

/-- Below the floor: the reading is lost in the noise -- underwhelmed. -/
def underwhelmed? (noiseFloor s : Nat) : Bool :=
  decide (s ≤ noiseFloor)

/-- Past the ceiling: the reading saturated -- overwhelmed. -/
def overwhelmed? (maxSize s : Nat) : Bool :=
  decide (maxSize < s)

/-- THE ELECTRON RAMP `1^p 0…`: `p` funges, then the noise floor.  Here `p = 6`. -/
def electronRamp : List Bool := [true, true, true, true, true, true]

-- The ramp reads in band (0, 6]: a real, whelmed measurement.
example : whelmed? 0 6 (size electronRamp) = true := by decide
-- Nothing at all (size 0) is lost in the noise: underwhelmed, NOT whelmed.
example : underwhelmed? 0 (size ([] : List Bool)) = true := by decide
example : whelmed? 0 6 (size ([] : List Bool)) = false := by decide
-- A reading of size 4 against a ceiling of 3 saturated: overwhelmed, NOT whelmed.
example : overwhelmed? 3 (size [true, true, true, true]) = true := by decide
example : whelmed? 0 3 (size [true, true, true, true]) = false := by decide

/-- The band covers everything: every magnitude falls in at least one of the three ranges --
underwhelmed, whelmed, or overwhelmed.  This is the floor/ceiling pair (`0 ≤ s` and `s ≤ bound`)
read as three ranges -- the 17-90 squeeze, stated as a covering.  Pure consequence of the order on
`Nat`; nothing here is stipulated.
-- CHOICE (fidelity A.8 + B.4): `band_covers` proves COVERAGE (the disjunction -- every magnitude is
-- in at least one range), NOT pairwise exclusivity.  The three ranges are in fact disjoint, but that
-- disjointness is not a built theorem here.  Softened from "trichotomy" (which connotes exclusivity)
-- to "covers"/"covering" rather than gold-plate an unused claim with a B.4 exclusivity build; a
-- future B.4 could promote the disjointness to a theorem if the artifact ever needs the trichotomy. -/
theorem band_covers (noiseFloor maxSize s : Nat) :
    s ≤ noiseFloor ∨ (noiseFloor < s ∧ s ≤ maxSize) ∨ maxSize < s := by
  omega

end Measurement.Reader
