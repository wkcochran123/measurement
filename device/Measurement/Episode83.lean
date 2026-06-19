import Measurement.Episode82

set_option maxHeartbeats 4000000

namespace Measurement

/-
__EPISODE 83__: _The Pairwise Sign Trial — Matter/Antimatter Is Baseline-Relative, and the
Apparatus Resolves at Most Three Electrons_

OPERATOR / HONESTY GATE (inherited from Episode82, non-negotiable):
This episode MEASURES the orientation split from pairwise relative electron motion.  It does NOT
derive baryogenesis, CP violation, a Sakharov condition, or the Standard Model asymmetry.  WHICH
sign counts as "matter" is the convention fixed by Episode73's tally (`sampleEvents`,
`dominant_unique`), not derived here.  Claim ceiling: "the matter/antimatter split is the sign of
the per-pair relative-velocity invariant δ², measured by the apparatus; the orientation is
BASELINE-RELATIVE; the apparatus distinguishes AT MOST THREE electrons."

----
Episode82 produced ONE electron pair's relative velocity as the second variation δ² and located
the single `Quot.sound`.  Here the SAME apparatus runs the TRIAL across its distinguishable
electrons:

  * Each electron is a distinct tag-representative (node0/node1/node2 -- the three `Bullshit`
    constructors, tags 0/1/2).  A pair (i,j) is read as δ² = `secondVariation` = the
    frame-invariant.  Pairs are built from DISTINCT nodes (never `pairKick` everywhere) -- that is
    what keeps each δ² genuine, not decorative.

  * THE FLIP (the core demonstration): the SAME pair (node1,node2) reads ELECTRON (δ²=-1) over a
    flat/symmetric baseline but POSITRON (δ²=+1) over a tilted/asymmetric baseline.  Orientation is
    BASELINE-RELATIVE (frame-relative) -- a convention of the apparatus, not an absolute or derived
    asymmetry.  Antimatter requires a baseline asymmetry; a symmetric baseline yields only
    matter+neutral.

  * THE PIGEONHOLE BOUND: `tag : Bullshit0 → Nat` has range exactly {0,1,2} (three constructors).
    A fourth electron is a fourth pigeon in three holes -- it must collide a tag, so the action
    cannot distinguish it (`segmentCost` 0 in that slot).  The apparatus resolves AT MOST THREE
    distinguishable electrons.  This is the device's count-to-three / pigeonhole, exhibited from
    inside.  It is NOT a claim about how many electrons exist; the three tag-representatives ARE the
    apparatus at full resolution.

Honesty/audit: individual electrons are NOT counted as positrons; positron is an orientation read
of a PAIRWISE interaction; the split is interaction-valued (δ²) BEFORE the sign projection; the
scalar sign is the apparatus receipt; this is a repeatable TRIAL (sign stable via Episode82's
`selection_sound` collapse), not a study; MEASURED, not derived.  The dominance/tally STUDY is
dropped -- the ensemble dominance is Episode73's convention; the measurement here is the per-pair
trial + the existence/pigeonhole facts.

All axiom-free (`omega` / `decide` / `rfl`).  δ² is read from `secondVariation` (= `mixedCubicCoupling`,
pure `segmentCost` arithmetic -- computable); `pairRelVel_eq_secondVariation` bridges the
measurement framing (whole - parts) to the invariant.  `decide` runs over the concrete finite lists
-- `decide`, NOT `native_decide` (that would add the `ofReduceBool` axiom and dirty the audit).
-/

namespace CubicGaugeVariation

/-- A pair of (distinct) electrons as a coupled gauge variation: left slip `sL`, right slip `sR`.
Genuine distinctness comes from distinct tag-representatives. -/
def pairVariation (sL sR : Bullshit0) : CubicGaugeVariation0 :=
  { middleLeftSlip := sL, middleRightSlip := sR }

/-- The pair's measured reading over a chosen baseline `path` (reuse Episode82's
`measurementReading`: whole = coupled cost difference, parts = the two first variations). -/
def pairReading (path : CubicGaugePath0) (v : CubicGaugeVariation0) : FrameReading :=
  measurementReading discriminatingAction path v

/-- The measurement-framed relative velocity (whole - parts). -/
def pairRelVel (path : CubicGaugePath0) (v : CubicGaugeVariation0) : Int :=
  (pairReading path v).relVel

/-- The pair's frame-invariant δ², read directly from the second variation
(= `mixedCubicCoupling`, pure `segmentCost` arithmetic -- computable; the sign is read from this). -/
def pairDelta2 (path : CubicGaugePath0) (v : CubicGaugeVariation0) : Int :=
  secondVariation discriminatingAction path v

/-- The measurement framing equals the invariant: pairRelVel = δ².  Axiom-free (the Episode31
identity + `omega`) -- exactly Episode82's `routes_same_invariant`, generalized to any baseline. -/
theorem pairRelVel_eq_secondVariation (path : CubicGaugePath0) (v : CubicGaugeVariation0) :
    pairRelVel path v = pairDelta2 path v := by
  have h :=
    coupledCubicDifference_eq_left_right_plus_secondVariation discriminatingAction path v
  simp only [pairRelVel, pairReading, pairDelta2, measurementReading, FrameReading.relVel]
  omega

end CubicGaugeVariation

open CubicGaugeVariation

/-- The orientation read of a signed δ²: negative = electron (matter), positive = positron
(antimatter), exactly zero = neutral (unresolved).  RAW sign -- the EKG-elaboration ε-band
(`measuredFloor`) is a SEPARATE refinement in different units (heartbeats, not δ²), deferred to the
EKG wire-up.  (Thresholding δ² on the floor would be a units error: δ² ∈ {-2..2}, the floor is
~thousands of heartbeats.) -/
def orientationOfSign (x : Int) : Option Orientation :=
  if x = 0 then none else if x < 0 then some .electron else some .positron

/-- The TRIAL: the orientations read across a list of pairs over a baseline (neutral pairs
dropped). -/
def pairEvents (path : CubicGaugePath0) (vs : List CubicGaugeVariation0) : List Orientation :=
  vs.filterMap (fun v => orientationOfSign (pairDelta2 path v))

/-- A tilted/asymmetric baseline: middleLeft = node0, middleRight = node1 (pL ≠ pR).  The minimal
baseline asymmetry that lets a positron appear. -/
def tiltedPath : CubicGaugePath0 :=
  { source := node0, middleLeft := node0, middleRight := node1, target := node1 }

/-- The three distinct-electron pairs, built from the three tag-representatives. -/
def threePairs : List CubicGaugeVariation0 :=
  [pairVariation node0 node1, pairVariation node0 node2, pairVariation node1 node2]

/-- The trial over the flat (symmetric) baseline. -/
def flatEvents : List Orientation := pairEvents flatPath threePairs

/-- The trial over the tilted (asymmetric) baseline. -/
def tiltedEvents : List Orientation := pairEvents tiltedPath threePairs

/-- A positron was observed in the trial. -/
def HasPositronEvent (es : List Orientation) : Prop := Orientation.positron ∈ es

-- ----------------------------------------------------------------
-- THE FLIP: matter/antimatter is baseline-relative.
-- ----------------------------------------------------------------

/-- Over the flat (symmetric) baseline the trial yields NO positron -- only matter and neutral.
Antimatter needs a baseline asymmetry. -/
theorem no_positron_over_flatPath : ¬ HasPositronEvent flatEvents := by decide

/-- Over the flat baseline an electron IS observed (the pair node1,node2 reads δ² = -1). -/
theorem electron_over_flatPath : Orientation.electron ∈ flatEvents := by decide

/-- Over the tilted (asymmetric) baseline the SAME pairs now yield a positron (node1,node2 reads
δ² = +1).  The orientation FLIPPED with the baseline -- it is frame-relative, a convention. -/
theorem positron_over_tiltedPath : HasPositronEvent tiltedEvents := by decide

/-- The flip, on the single pair: node1,node2 reads electron (δ² = -1) flat, positron (δ² = +1)
tilted.  Matter/antimatter is baseline-relative. -/
theorem baseline_relative_flip :
    pairDelta2 flatPath (pairVariation node1 node2) = -1 ∧
      pairDelta2 tiltedPath (pairVariation node1 node2) = 1 := by decide

-- ----------------------------------------------------------------
-- THE PIGEONHOLE BOUND: the apparatus resolves at most three electrons.
-- ----------------------------------------------------------------

/-- Every tag is one of exactly three values: the apparatus has three distinguishable states. -/
theorem tag_lt_three (s : Bullshit0) : tag s < 3 := by
  cases s <;> (simp only [tag]; omega)

/-- Four electrons cannot have four distinct tags: some pair collides (3 holes, 4 pigeons). -/
theorem four_tags_collide (a b c d : Bullshit0) :
    tag a = tag b ∨ tag a = tag c ∨ tag a = tag d ∨
      tag b = tag c ∨ tag b = tag d ∨ tag c = tag d := by
  have ha := tag_lt_three a
  have hb := tag_lt_three b
  have hc := tag_lt_three c
  have hd := tag_lt_three d
  omega

/-- The apparatus resolves AT MOST THREE distinguishable electrons: there are no four slips with
pairwise-distinct tags.  In any four, some pair collides (and is therefore tag-degenerate to the
action -- see `segmentCost_zero_of_tag_eq`).  NOT a claim about how many electrons exist. -/
theorem apparatus_resolves_at_most_three :
    ¬ ∃ a b c d : Bullshit0,
      tag a ≠ tag b ∧ tag a ≠ tag c ∧ tag a ≠ tag d ∧
        tag b ≠ tag c ∧ tag b ≠ tag d ∧ tag c ≠ tag d := by
  rintro ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd⟩
  have ha := tag_lt_three a
  have hb := tag_lt_three b
  have hc := tag_lt_three c
  have hd := tag_lt_three d
  omega

/-- A tag collision IS indistinguishability to the apparatus: the action's `segmentCost` between
two same-tag slips is zero.  So a colliding (fourth) electron contributes no distinction. -/
theorem segmentCost_zero_of_tag_eq (x y : Bullshit0) (h : tag x = tag y) :
    discriminatingAction.segmentCost x y = 0 := by
  simp only [discriminatingAction, h, if_pos]

/-
The standing record.  Verified by the operator's build (expected results inline).
-/

-- The measurement=invariant bridge is axiom-free (the Episode31 identity + omega).
#print axioms CubicGaugeVariation.pairRelVel_eq_secondVariation
  -- expect: axiom-free (at most [propext])

-- The pigeonhole bound is axiom-free.
#print axioms apparatus_resolves_at_most_three
  -- expect: axiom-free

-- The per-pair δ² experiment readout (read from the computable invariant):
#eval pairDelta2 flatPath (pairVariation node0 node1)    -- expect: 0   (neutral)
#eval pairDelta2 flatPath (pairVariation node0 node2)    -- expect: 0   (neutral)
#eval pairDelta2 flatPath (pairVariation node1 node2)    -- expect: -1  (electron)
#eval pairDelta2 tiltedPath (pairVariation node1 node2)  -- expect: 1   (positron) -- THE FLIP
#eval flatEvents    -- expect: [Measurement.Orientation.electron]
#eval tiltedEvents  -- expect: [Measurement.Orientation.positron]

end Measurement
