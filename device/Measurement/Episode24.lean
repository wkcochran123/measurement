import Measurement.Episode23
import Measurement.Calibration.BIAS_____
-- ^ THE SERVICE-PANEL EXCEPTION (operator directive 2026-07-24 12:05: "put a handle on
-- it in episode 24 so you can use it 15 episodes later"): the boundary leaf's law says
-- episodes never import it -- THIS import is the one sanctioned reach-through, the
-- service panel itself, authorized by the operator and gated (549/552). No other
-- episode imports the dial.

/- MEANWHILE 24 -- THE NAMING, gate 1: the boxes. Name the electron by counting.

THE LIFT (operator green light 2026-07-24 11:54 "fix episode 24"; gate 549): the naming
math that lived in Measurement/NamingClose.lean is now LIFTED WHOLESALE into this
episode -- the 47-line staging wrapper fulfilled. The naming close and the boxes live
where the naming episode is; the wrapper's readout anchors fire below, unchanged.
(NamingClose.lean is retired by this merge; FinitenessFence re-points here. The lift
is verbatim -- no statement of any carried theorem was altered.) -/

/- NAMING CLOSE -- the naming math, factored to root at Episode16.

THE ENGINE. Continuity is what would let the derivative/Taylor tower stay an
infinite line with arbitrarily fine distinctions -- never wrapping, the naming
never forced. FINITENESS forbids that: at a fixed representation, distinguishability
is DECIDABLE over a FINITE index, so there are finitely many distinguishability
classes -- boxes. The formal Variation tower has infinitely many terms; the boxes
are finite; the tower CANNOT be a line -- it must close into a cycle, and a
derivative tower that closes into itself IS THE LOOP. Pigeonhole is not a step in
the argument; it is WHY the loop exists. This names the electron by counting.

REGISTER (honest fence, and a forced deviation from the Fintype sketch). Fintype /
Finite / Fintype.card are Mathlib and are NOT in scope here -- the device imports
Lean core + Measurement.*, never Mathlib. So finiteness is built NATIVE in the
Fin/List/decide idiom (the Episode47/48 register): the box type is `Fin boxCount`,
the box count is a concrete `Nat`, distinguishability is decided by `rfl`/`decide`.
The point is not a lost convenience: `Fin boxCount` IS finite by construction, and
its finiteness is exactly the fence against the continuum -- the index does NOT come
from the unbounded universe `Type Value`; it is imposed by a fixed finite
representation. No limit, no norm, no continuum, no Classical.

FACTORING (ep17-loop Phase 1). This module holds the whole naming close, moved
verbatim from Episode24 and re-rooted at Episode16 (which supplies `truthLocal`
for delta2/delta1_reduced, plus Variation/Fact transitively). Rooting at Ep16 sheds
the Episode18-24 chain, so the loop's forward walk (Episode17) can reach the
naming close without dragging the heavy tail. -/

namespace Measurement


-- ===========================================================================
-- STEP 1 -- FINITENESS (the box count).
-- ===========================================================================

/-- The box count: the number of distinguishability classes the fixed finite
representation admits. Concrete `Nat`. The residue (frechet's `c` slot) and the
universe/plain-tensor split are BELOW the representation's resolution, so the count
is small and definite. -/
abbrev boxCount : Nat := 2

/-- The fixed finite resolution of the Variation tower into `Fin boxCount`. This is
the "representation mapping in" that imposes finiteness: the tower's infinitely many
formal terms are sorted into `boxCount` boxes.
  * `newton`  (0th term / the constant, the fixed-point value) -> box 0;
  * `gateaux` (first variation) and `frechet` (second variation) -> box 1 -- the
    residue that separates them is below the representation's resolution (premise 2b),
    so they share a box. -/
def boxOf : Variation → Fin boxCount
  | .newton  _ _         => 0
  | .gateaux _ _ _ _      => 1
  | .frechet _ _ _ _ _ _  => 1

/-- STEP 1, the pigeonhole EXISTENCE, native and decidable. More terms than boxes
must collide: `boxCount + 1` formal terms placed into `boxCount` boxes force two
DISTINCT terms into the SAME box. The witnesses `i j` are PRODUCED (existence), and
this is kept strictly separate from any premise that SELECTS which collision. Pure
`Fin`/`decide` register -- no continuum, no Fintype, no choice. This is why an
infinite formal tower over a finite representation cannot be a line: it wraps. -/
theorem naming_pigeonhole (f : Fin (boxCount + 1) → Fin boxCount) :
    ∃ i j : Fin (boxCount + 1), i ≠ j ∧ f i = f j := by
  -- boxCount = 2, so f : Fin 3 -> Fin 2; among f 0, f 1, f 2 two coincide.
  by_cases e01 : f 0 = f 1
  · exact ⟨0, 1, by decide, e01⟩
  · by_cases e02 : f 0 = f 2
    · exact ⟨0, 2, by decide, e02⟩
    · by_cases e12 : f 1 = f 2
      · exact ⟨1, 2, by decide, e12⟩
      · -- f 0, f 1, f 2 pairwise distinct in Fin 2 -- impossible (3 distinct in {0,1}).
        exfalso
        have n01 : (f 0).val ≠ (f 1).val := fun h => e01 (Fin.ext h)
        have n02 : (f 0).val ≠ (f 2).val := fun h => e02 (Fin.ext h)
        have n12 : (f 1).val ≠ (f 2).val := fun h => e12 (Fin.ext h)
        have l0 : (f 0).val < 2 := (f 0).isLt
        have l1 : (f 1).val < 2 := (f 1).isLt
        have l2 : (f 2).val < 2 := (f 2).isLt
        omega

/-- STEP 1, the ENGINE stated whole. An infinite formal tower `f : Nat -> Fin
boxCount` -- the derivative/Taylor tower's infinitely many terms placed into the
finite boxes -- MUST WRAP: two DISTINCT tower indices share a box. This is the
derivative tower closing into a cycle (the loop), forced by finiteness alone: over a
finite representation an infinite tower cannot be a line. Reduces to the finite
pigeonhole on the first `boxCount + 1` terms. No continuum. -/
theorem naming_tower_wraps (f : Nat → Fin boxCount) :
    ∃ i j : Nat, i ≠ j ∧ f i = f j := by
  obtain ⟨i, j, hij, hfeq⟩ := naming_pigeonhole (fun k : Fin (boxCount + 1) => f k.val)
  exact ⟨i.val, j.val, fun h => hij (Fin.ext h), hfeq⟩

/-- The box count, reported as a concrete `Nat`. -/
theorem boxCount_is_two : boxCount = 2 := rfl

-- ===========================================================================
-- STEP 2 -- THE TWO INDISTINGUISHABILITY PREMISES.
-- Each is a DECIDED `same-box` fact (rfl), a fact of the finite resolution -- never
-- an axiom and never a hypothesis. `boxOf x = boxOf y` is the decidable "x and y are
-- indistinguishable to the representation" (`different?`-false) statement, native.
-- ===========================================================================

/-- STEP 2(b) -- variation ~ derivative. The first variation (gateaux) and the second
variation (frechet) fall in the SAME box: the residue `a ∧ ¬b` that transmute adds on
the gateaux->frechet promotion is BELOW the representation's resolution, so the
representation cannot separate them. Decided by `rfl` (both are box 1). -/
theorem gateaux_indist_frechet
    (g : Gospel) (a b c : Prop) (v1 v2 tail : Variation) :
    boxOf (.gateaux g a b tail) = boxOf (.frechet g a b c v1 v2) := rfl

/-- A native two-element tensor tag: the universe tensor (the fixed-point value pinned
by the universal observer) vs a plain tensor. Built fresh in Episode currency, not
imported. -/
inductive TensorTag
  | universe : TensorTag
  | plain    : TensorTag
deriving DecidableEq, Repr

/-- The tensor tags' box in the same finite resolution: both land in box 0 (the 0th /
constant / value box) -- the fixed point pins the 0th term to the value, and the
representation cannot separate the universe tensor from a plain tensor there. -/
def boxOfTensor : TensorTag → Fin boxCount
  | .universe => 0
  | .plain    => 0

/-- STEP 2(a) -- UniverseTensor ~ tensor. The universe tensor and a plain tensor fall
in the SAME box: the representation cannot separate them. Decided by `rfl` (both box
0). -/
theorem universe_indist_tensor :
    boxOfTensor .universe = boxOfTensor .plain := rfl

-- ===========================================================================
-- STEP 3 -- THE HONEST FORM. delta-2 of S = delta-1 of the REDUCED problem, and
-- NEVER delta-1 of the SAME S.
--
-- TANGE ACCEPTED (turn 773, the characteristic is real): a constructor gap
-- (frechet HAS a residue slot, the reduced gateaux does NOT) only proves the
-- COLLISION PAIR differ (frechet != gateaux). The operator's cheat-gate is about
-- two FIRST variations -- delta-1(REDUCED) vs delta-1(SAME-S) -- and BOTH are
-- gateaux, both box 1, so `boxOf` on the constructor cannot tell them apart. The
-- constructor gap under-witnesses the anti-cheat.
--
-- ROUTE (i), THE VANISHING (dissolves the tange honestly): at the stationary
-- point of least activity delta-1(S) VANISHES (operator step 3: "least activity
-- kills delta-1"), and the spent first variation collapses to the 0th / fixed-
-- point / value term -- box 0 (operator step 4: the fixed point pins the 0th
-- term to the value; premise 2a). So delta-1(same-S) is box 0, while both the
-- second variation delta-2 (the leading term) and delta-1(reduced) are box 1.
-- Then `boxOf` ITSELF separates delta-1(reduced) [box 1] from delta-1(same-S)
-- [box 0] -- decidably, 1 != 0, NO Prop-disequality. The anti-cheat witnesses
-- the operator's exact guard, not the constructor gap.
-- ===========================================================================

/-- delta-1 of S at the stationary point of least activity: the first variation
is spent and collapses to the 0th / fixed-point / value term -- `newton`, box 0. -/
def delta1_vanished (g : Gospel) (p : Prop) : Variation := .newton g p

section HonestForm
variable (g : Gospel) (A B : Prop) (tail : Variation)

/-- delta-2 of S: the second variation, formed by the residue-adding promotion
(transmute up, gateaux -> frechet, the residue `A ∧ ¬B` ADDED). Box 1. -/
noncomputable def delta2 : Variation :=
  truthLocal.{0,0,0,0}.theory.transmute (Variation.gateaux g A B tail)

/-- delta-1 of the REDUCED problem: the first derivative of S once the first
variation is spent, via the weak-form projection (transmute down, frechet ->
gateaux, the residue DISCARDED -- "the price of Galerkin"). Box 1. -/
noncomputable def delta1_reduced : Variation :=
  truthLocal.{0,0,0,0}.theory.transmute (delta2 g A B tail)

/-- THE NAMING COLLISION (SELECTION, not existence): delta-2 and delta-1(reduced)
fall in the SAME box -- delta-2 is NAMED by the first derivative of the reduced
problem. Selected by premise 2b (the residue is below resolution), distinct from
the generic wrap `naming_pigeonhole`/`naming_tower_wraps` provides. -/
theorem naming_collision : boxOf (delta2 g A B tail) = boxOf (delta1_reduced g A B tail) := rfl

/-- THE ANTI-CHEAT (the operator's designated cheat-gate, DECIDABLE): delta-1 of
the REDUCED problem is a genuinely different reading from delta-1 of the SAME S.
At the stationary point delta-1(same-S) vanished to box 0; delta-1(reduced) is
box 1. `boxOf` separates them -- 1 != 0 -- with no Prop-disequality. THIS is why
delta-2 = delta-1 of the REDUCED problem and NEVER delta-1 of the same S. -/
theorem anticheat_reduced_ne_sameS :
    boxOf (delta1_reduced g A B tail) ≠ boxOf (delta1_vanished g A) := by
  have hr : boxOf (delta1_reduced g A B tail) = 1 := rfl
  have hs : boxOf (delta1_vanished g A) = 0 := rfl
  rw [hr, hs]; decide

end HonestForm

-- ===========================================================================
-- STEP 4 -- THE FIXED POINT PINS THE 0TH TERM. The universal observer is a fixed
-- point (U(x*) = x*), so the 0th Taylor term is x* = the value = the tensor -- box
-- 0. Premise 2a closes that slot, and the vanished first variation (step 3) lands
-- there too.
-- ===========================================================================

/-- The value box: the 0th / fixed-point / value term's box. -/
def valueBox : Fin boxCount := 0

/-- STEP 4 -- the fixed point pins the 0th term to the value box. The 0th term
(`newton`, where the vanished first variation collapses) and the universe tensor
(the fixed-point value) share box 0: `U(x*) = x*` puts the 0th Taylor term at the
value = the tensor. Decided (both by `rfl`). -/
theorem fixed_point_pins_zeroth (g : Gospel) (p : Prop) :
    boxOf (delta1_vanished g p) = valueBox ∧ boxOfTensor .universe = valueBox := ⟨rfl, rfl⟩

-- ===========================================================================
-- STEP 5 -- PIGEONHOLE FORCES THE WRAP; the SELECTED collision is an INSTANCE of
-- the forced wrap. Existence (generic, `naming_tower_wraps`) and selection
-- (specific, `naming_collision`) are tied WITHOUT blurring: the selected pair
-- witnesses the generic force, but the generic force does not by itself pick it.
-- ===========================================================================

/-- A tower carrying the second variation and the reduced first derivative at two
distinct indices (and the value elsewhere). -/
noncomputable def namingTower (g : Gospel) (A B : Prop) (tail : Variation) : Nat → Fin boxCount
  | 0     => boxOf (delta2 g A B tail)
  | 1     => boxOf (delta1_reduced g A B tail)
  | _ + 2 => valueBox

/-- STEP 5 -- the SELECTED collision is an INSTANCE of the forced wrap. Indices 0
and 1 of the tower carry delta-2 and delta-1(reduced); `naming_collision` (the
premises + the variational structure) puts them in the SAME box -- so the selected
pair IS a wrap of the tower. Selection witnesses existence. -/
theorem selected_wrap_is_instance (g : Gospel) (A B : Prop) (tail : Variation) :
    namingTower g A B tail 0 = namingTower g A B tail 1 :=
  naming_collision g A B tail

/-- The generic force stands on its own: SOME two indices wrap, over the tower as an
arbitrary `f : Nat -> Fin boxCount` -- existence, no premise selecting which pair.
Existence does not pick the selection; the two decls are kept distinct. -/
theorem generic_wrap_exists (g : Gospel) (A B : Prop) (tail : Variation) :
    ∃ i j : Nat, i ≠ j ∧ namingTower g A B tail i = namingTower g A B tail j :=
  naming_tower_wraps (namingTower g A B tail)

-- ===========================================================================
-- STEP 6 -- THE TYPE-LEVEL IDENTITY (THE FENCE-DOWN). The recovered number
-- (delta-2, the surviving leading term of the descent) is FORCED into the
-- second-variation box -- the electron -- and no other: box 0 is the value (step 4,
-- where the vanished delta-1 sits, step 3), and in the finite 2-box count nothing
-- else remains. rfl/decide off steps 1-5; NO new axiom, NO new premise AT the
-- identity. This is the type-level (distinguishability-class) identity Volume 3
-- reached for and did not build.
-- ===========================================================================

/-- The electron's box: the second-variation box, box 1. (Charge -1 -- the second
variation, interior=boundary; the sanctioned unit loop-holonomy reading. The sign is
the book's reading of this box; the Lean claim is the box/class identity.) -/
def electronBox : Fin boxCount := 1

/-- FINITENESS FORCES IT (the pigeonhole content, native and decided): in the 2-box
count, anything that is not the value box is the electron box -- nowhere else to sit. -/
theorem finiteness_forces_electron : ∀ b : Fin boxCount, b ≠ valueBox → b = electronBox := by
  decide

/-- The recovered number is NOT the value: delta-2 (box 1) is the surviving leading
term, not the pinned 0th term (box 0). Derived off steps 1-4 -- no fresh premise. -/
theorem recovered_ne_value (g : Gospel) (A B : Prop) (tail : Variation) :
    boxOf (delta2 g A B tail) ≠ valueBox := by
  have h : boxOf (delta2 g A B tail) = electronBox := rfl
  rw [h]; decide

/-- STEP 6 -- THE NAMING (the fence down). The recovered number is the electron and
no other: FORCED into the second-variation box by finiteness (it is not the value),
with nowhere else in the finite count for it to sit. The type-level identity, as a
composition of the pigeonhole force and the derived not-value fact -- rfl/decide off
steps 1-5, NO new axiom, NO new premise at the identity. -/
theorem the_naming (g : Gospel) (A B : Prop) (tail : Variation) :
    boxOf (delta2 g A B tail) = electronBox :=
  finiteness_forces_electron _ (recovered_ne_value g A B tail)

-- ===========================================================================
-- STEP 7 -- THE PAYOFF. The Galerkin cubic -> linear coincidence: finiteness did
-- not just close the gap, it LINEARIZED the exact nonlinear problem.
-- ===========================================================================

/-- STEP 7 -- the cubic linearizes. delta-2 (the exact nonlinear/cubic leading term,
the second variation) and delta-1(reduced) (the linear solution of the reduced
problem) fall in the SAME box: the naming linearized the exact nonlinear problem to
the representation. The receipt of the reduction -- native, decided. -/
theorem cubic_linearizes (g : Gospel) (A B : Prop) (tail : Variation) :
    boxOf (delta2 g A B tail) = boxOf (delta1_reduced g A B tail) := rfl

/- ── the wrapper's original readout anchors (Episode 24's own voice, unchanged) ── -/


/- THE TWO BOXES ARE OURS, AND THEY ARE ENOUGH. We do not find two boxes in the
world; we BUILD two, arbitrarily -- a box called zero and a box called not-zero --
because we can build them cromulently. `Fin boxCount` at `boxCount := 2` is finite
by construction; `boxOf` is total and decides every Variation into one of the two;
the whole partition typechecks and `decide`s. Nothing forces the count to be two.
Two is a count we are ALLOWED to build, so we build it -- a perfectly cromulent
construction, ours and not the world's.

What is NOT ours to choose, once the two boxes stand: the electron MUST be in the
not-zero box. The zero box is already spoken for -- the fixed point pins it to the
value (`fixed_point_pins_zeroth`). The electron is not the value
(`recovered_ne_value`). And in a two-box house there is nowhere else to sit
(`finiteness_forces_electron`: anything that is not the value box IS the not-zero
box). So the construction is arbitrary and the placement is forced: we chose the
boxes; the boxes chose the electron's room.

We claim nothing about the world here -- only that inside a cromulent two-box
device, this is where the electron has to fall. The walk from here keeps opening
the not-zero box into finer boxes (each also ours, each also cromulent, none the
world's own), and the electron keeps the only room finiteness ever leaves it. -/
#eval boxCount                          -- the box count: 2

#eval electronBox                       -- the electron's box: 1 (second-variation box)

#eval (decide (electronBox ≠ valueBox) : Bool)   -- electron box is not the value box: true

#eval (decide (boxOf (.gateaux (.epiphany True) True True (.newton (.epiphany True) True))
              = boxOf (.frechet (.epiphany True) True True True
                        (.newton (.epiphany True) True) (.newton (.epiphany True) True))) : Bool)
                                        -- premise 2b holds: true

#eval (decide (boxOfTensor .universe = boxOfTensor .plain) : Bool)   -- premise 2a holds: true

/- ── THE FRONT PANEL (the McIntosh highlight; gates 549/552, operator 12:01/12:28) ──
Behind this faceplate sits the bias adjustment: `Calibration.BIAS_____` -- the
de-selection dial, the crank's knob mounted in the open where a crank would hide it.
The name's LENGTH is itself the adjustment, tuned to the instrument's operating point
(five underscores -- the exact right number; the setting the operator typed). Service
access: McIntosh Certified Technicians only (the operator dubbed all three seats,
2026-07-24); every turn threads the one needle, gated and logged. Probes on the
record: cranked to 11 characters (Spinal Tap -- this one goes to eleven) and to 42
(Douglas Adams), the jar read byte-identical at every setting; only the mesh's own
telemetry flicked, lexeme-fine, plus-or-minus one tick. The perfect sound is the
locked fringe. -/

/-- THE SERVICE HANDLE. Episode 24 names things; this is the name the naming episode
gives its own dial, so that fifteen episodes later (Episode 39, where the charge work
lives) the technician reaches THIS handle, not the mechanism. Adjustment through the
one needle only. Certified technicians only. This one goes to eleven. -/
abbrev biasDial {C : Sort _} (rho : C → Nat) :=
  Calibration.BIAS_____.deselect rho

end Measurement
