import Measurement.Episode84

set_option maxHeartbeats 4000000

namespace Measurement

/-
__EPISODE 85__: _The Split, Counted -- Pure Matter over the Native Baseline_

OPERATOR / HONESTY GATE (inherited, non-negotiable):
This episode DERIVES the matter/antimatter split by COUNTING orientations over Episode83's trial,
in place of Episode73's hand-typed `sampleEvents`.  It does NOT derive baryogenesis, CP violation,
or a Sakharov condition, and it does NOT prove a general "the geometry forbids antimatter" law.
What it states is a COUNT over the concrete trial, and the prediction read off it:

  PREDICTION (conditional, falsifiable): over the apparatus's NATIVE symmetric (flat) baseline the
  trial reads ZERO antimatter and nonzero matter -- pure matter.  Antimatter appears only once the
  baseline is tilted (an asymmetric flux).  A single positron over the symmetric trial would break
  this.  WHICH baseline is "native" is the symmetric/flat path (a structural fact, not hand-typed);
  WHICH sign is "matter" is the convention (Episode83); the global ENSEMBLE measure (how many of
  each across a population) is the open part Episode73 leaves to convention.  MEASURED, not derived.

----
The whole device collapses to a count.  An `Orientation` is the sign of delta-squared; delta-squared
is the signed imbalance of the tag-comparisons -- the funge bin minus the tange bin, Trues vs
Falses.  So the SPLIT is just: count the positrons, count the electrons.  Here we do exactly that
over the trial and read the prediction off the count.  Each tally is `decide` over the concrete
finite events -- axiom-free; the underlying sign facts are Episode83's
`no_positron_over_flatPath` / `electron_over_flatPath` / `positron_over_tiltedPath`.
-/

/-- The antimatter tally: how many positrons the trial reads. -/
def antimatterCount (es : List Orientation) : Nat :=
  (es.filter (fun o => decide (o = Orientation.positron))).length

/-- The matter tally: how many electrons the trial reads. -/
def matterCount (es : List Orientation) : Nat :=
  (es.filter (fun o => decide (o = Orientation.electron))).length

-- ----------------------------------------------------------------
-- THE PREDICTION: over the native (symmetric) baseline, the count is PURE MATTER.
-- ----------------------------------------------------------------

/-- THE PREDICTION: over the apparatus's native symmetric (flat) baseline, the antimatter count is
ZERO.  The symmetric trial reads only matter and neutral -- pure matter.  (This is Episode83's
`no_positron_over_flatPath`, read as a count.) -/
theorem native_antimatter_is_zero : antimatterCount flatEvents = 0 := by decide

/-- ...and matter IS present natively: the electron count is nonzero. -/
theorem native_matter_is_present : 1 ≤ matterCount flatEvents := by decide

/-- Antimatter requires a baseline asymmetry: over the tilted flux the positron count is nonzero.
The split is not absolute -- it is drawn from the field's asymmetry. -/
theorem antimatter_needs_asymmetry : 1 ≤ antimatterCount tiltedEvents := by decide

/-- THE SPLIT, COUNTED: the native (symmetric) baseline yields some matter and NO antimatter; the
tilted (asymmetric) baseline makes antimatter appear.  Pure matter is the prediction; antimatter is
the field's asymmetry, not the apparatus's default. -/
theorem the_split_counted :
    antimatterCount flatEvents = 0
      ∧ 1 ≤ matterCount flatEvents
      ∧ 1 ≤ antimatterCount tiltedEvents :=
  ⟨native_antimatter_is_zero, native_matter_is_present, antimatter_needs_asymmetry⟩

-- ----------------------------------------------------------------
-- The standing record.
-- ----------------------------------------------------------------

#eval matterCount flatEvents          -- matter, native baseline
#eval antimatterCount flatEvents      -- expect: 0   (NO antimatter natively -- the prediction)
#eval antimatterCount tiltedEvents    -- antimatter, only once the flux is tilted
#print axioms the_split_counted

end Measurement
