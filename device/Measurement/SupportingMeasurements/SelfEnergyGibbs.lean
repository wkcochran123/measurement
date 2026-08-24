import Measurement.SelfApplication        -- register_cost (elaboration-heartbeat meter), self_residual, heartbeatCoefficient
import Measurement.TwoDescriptions        -- electron_in_orbit (the base description whose cost we iterate)
import Measurement.Episode15              -- selection_sound (THE NEEDLE — the device's single sanctioned Quot.sound)
import Measurement.Calibration.BIAS_____  -- mkClass (Q5 re-thread: the one class former outside Ep15 — the needle's file-census stays two)
import Measurement.Episode27              -- secondDifference (the second-difference instrument)
import Measurement.AlphaBoundCountToThree -- countToThree (= 3, the resolution floor)

/-! # SelfEnergyGibbs — the self-energy correction as a tapered (wound) approach

**Status: proposal for the technical crew (SELF_ENERGY_GIBBS_BRIEF.md §3–§7). Nothing here reads α.**
The Gibbs identification is INTERPRETIVE (operator's reading, MARKED as such). §3's signature is the
honesty: the instrument can KILL its own identification and reports either way. §4–§6 are buildable and
blind; the α wiring is DEFERRED to a separate post-build step (this file never touches the Ep14→40 chain
and never reads a coupling — it produces a bracket for the ring-free self-energy and stops).

READ-VERIFIED draft (no `lake` run — the operator's cold Ep14→40 build owns the machine). The numeric
verdicts (§3 Gibbs-or-kill, the winding count, the bracket walls) are `register_cost` heartbeat readings
FILLED AT ELABORATION; here each def is reasoned to what it elaborates to, axiom-claims to confirm on build.

## The instrument (brief §4)
1. **Three-plus readings, two-plus slips, second difference** — `TwoSlipRecursion`'s instrument, pointed
   at ABSTRACTION DEPTH (`describe`, `describe∘describe`, `describe³`, …) instead of orbital distance.
2. **Taper = mediant** — read the depth series through mediant-smoothed means (Fejér/Cesàro in the
   modulo realm). Slower convergence is the point (approach-only).
3. **The inductor (§7)** — one mediant pass = one TURN, and it annihilates the period-2 (Nyquist) Gibbs
   mode first; each further pass kills the next mode down. π is the ANGULAR winding (a turn count, NOT the
   radial distance the map rejected at its asymptote; π is MEASURED off the orbit now — `ArchimedesPi` —
   not cranked from a digit list). The turn count itself is MEASURED as a SLIP CONDITION: wind until the
   smoothed alternation drops below the count-3 floor (`convergenceTurns`, §7 — no dialed π-precision).
4. **Approach three, don't arrive** — output a BRACKET `[lo, hi]`, walls proved ordered; the limit is
   never claimed. The α contraction (deferred) is interval-valued (band, not point — the Meissner ruling).

## MARKED (Kodo's §7 review flags, built in)
* (a) The inductor/circuit is a **marked METAPHOR** — a picture, not a mechanism. The substance is the
  Cesàro/Fejér averaging hierarchy realised by the mediant; model-owned, same fence as the Meissner/photon
  metaphors.
* (b) The suppression RATE (how fast the ring dies per turn) is **read off the build, not assumed**. The
  coil picture suggests `L ∝ N²`; whether N mediant passes give N-order or N²-order suppression is a
  measured quantity — `#eval suppressionRateReport` prints it and it is MARKED as whichever the math gives.
* (c) π-as-winding-count is a **METHOD parameter** (how many smoothing turns), NOT a new independent
  reading of α. It corrects the smoother; it is not a third witness. Two-twos is untouched (this file
  reads no coupling).
* (e) The DIAGNOSTIC depth runs PAST three (`depthN = 11`) so the §3 signature has room; the count-3 floor
  still governs the (deferred) α read. The two "threes" are kept separate on purpose.

## Guards (brief §5)
* **Blind / baked-before-α** — nothing here imports or reads the α map; the whole instrument is elaborated
  before any coupling comparison (`generatedBeforeAlpha := True`, structural: no α symbol appears).
* **Device-derived** — base = `electron_in_orbit`; turn count = MEASURED (`convergenceTurns`, §7); floor =
  `countToThree`. No free parameter; no `137.036`; nothing aimed.
* **Premise MARKED** — `IsSlipCondition` stays a hypothesis; the ring-free limit is approached, never claimed.
-/

namespace Measurement.SelfEnergyGibbs
open Measurement Measurement.TwoDescriptions Measurement.SelfApplication Measurement.AlphaBoundCountToThree

/-! ## §4.1 — the depth series: the cost of describing, at abstraction depth n

`describe P` is one more layer of description — the propositional self-echo `P = P`, iterating the
`two_descriptions` propext pattern. `register_cost` weighs each iterate's elaboration heartbeats. The
VALUES are filled at elaboration (build); the instrument below is deterministic given them.

RESOLVED (operator, 2026-07-21): the describe question is settled — this TYPE-cost series (`P = P`) is now
the SECONDARY / contrast series; the BINDING series is the FAITHFUL `selection_sound` (Quot.sound) proof-cost
one below. We keep this one and report both (Kodo + beastmaster's call): if the type-cost does NOT ring, that
is itself information (type-sameness isn't the ring). The §3 kill condition stays live for both. -/
def describe (P : Prop) : Prop := (P = P)

register_cost depthCost1 => (describe electron_in_orbit)
register_cost depthCost2 => (describe (describe electron_in_orbit))
register_cost depthCost3 => (describe (describe (describe electron_in_orbit)))
register_cost depthCost4 => (describe (describe (describe (describe electron_in_orbit))))
register_cost depthCost5 => (describe (describe (describe (describe (describe electron_in_orbit)))))
register_cost depthCost6 => (describe (describe (describe (describe (describe (describe electron_in_orbit))))))
register_cost depthCost7 => (describe (describe (describe (describe (describe (describe (describe electron_in_orbit)))))))
register_cost depthCost8 => (describe (describe (describe (describe (describe (describe (describe (describe electron_in_orbit))))))))
register_cost depthCost9 => (describe (describe (describe (describe (describe (describe (describe (describe (describe electron_in_orbit)))))))))
register_cost depthCost10 => (describe (describe (describe (describe (describe (describe (describe (describe (describe (describe electron_in_orbit))))))))))
register_cost depthCost11 => (describe (describe (describe (describe (describe (describe (describe (describe (describe (describe (describe electron_in_orbit)))))))))))

/-- `maxCertifiedTurn` — the turn TARGET: the deepest pass `k` the depth budget certifies convergence to. -/
def maxCertifiedTurn : Nat := 6
/-- `settleMargin` — a DISCRETIONARY (NOT forced) robustness margin of one extra layer: it gives the pass-k
convergence check a lead-in difference, so the `countToThree` sub-floor diffs sit at the TAIL of a longer
sequence ("settled") instead of BEING the whole 3-long sequence (vacuous-adjacent). Named as a margin, not
dressed as a necessity. -/
def settleMargin : Nat := 1
/-- The diagnostic depth, COMPUTED from the depth budget (audit #5 — was the hand-set literal `11`).
⚑ The FORCED budget, derived from the code (`wind k` → length `−k`; `firstDiffs` → `−1`; `convergesAt` needs
`≥ countToThree` diffs), is `depthN ≥ k + countToThree + 1`: the `+1` is the `firstDiffs` FENCEPOST (FORCED —
`countToThree` diffs need `countToThree+1` values). We add `settleMargin` (a chosen `+1`, NOT forced) on top.
So `depthN = maxCertifiedTurn + countToThree + 1 + settleMargin = 6 + 3 + 1 + 1 = 11` — the ladder length is
the turn-target price plus one NAMED margin, all earned and honestly labelled (not a margin dressed as
forced). (⚠ PARTIAL de-magic: `depthSeries`/`depthSeriesQuot`/`typeTowerSeries` are still hardcoded 11-element
literal lists — bumping `maxCertifiedTurn` moves `depthN` but NOT those series, which would DESYNC; the
coupling is asserted by `depthSeriesQuot_length_eq_depthN` below. Deepened from 8 via Kodo/external reviewer
to settle the k=4–6 ambiguity. Cost ~2^depthN, tiny.) -/
def depthN : Nat := maxCertifiedTurn + countToThree + 1 + settleMargin

/-- The raw TYPE-describe depth series (elaboration cost at abstraction depth 1..11), as `Int`. -/
def depthSeries : List Int :=
  [depthCost1, depthCost2, depthCost3, depthCost4, depthCost5, depthCost6, depthCost7, depthCost8, depthCost9, depthCost10, depthCost11].map Int.ofNat

/-! ### The FAITHFUL describe — the Quot.sound replacement of the device itself (operator's selection principle)

Selection principle (operator, 2026-07-21): **`describe` must be the Quot.sound replacement of the device
itself** — the single sanctioned needle `Episode15.selection_sound : r a b → Quot.mk r a = Quot.mk r b`
(`#print axioms = [Quot.sound]`). The −21 is the abstraction overhead of the self-DESCRIPTION (the
`two_descriptions` echo / the needle's identification), NOT the type-size cost — so this, not `describe P
:= P = P` above, is the quantity where the ring, if any, actually lives.

The selection principle is FAITHFULNESS to what the −21 measures — NEVER "which describe gives Gibbs"
(choosing for the answer would be steering, the crank). So we RUN BOTH and let the faithful one bind; a
KILLED verdict, honestly reported, is a success (the type-cost series NOT ringing is itself information).

The faithful describe measures the cost of the device's ACTUAL sanctioned Quot.sound wrapper —
`Episode15.selection_sound` — NOT a type. The −21 is the abstraction overhead of the SELECTION (the
Quot.sound step where "are these the same TRUTH?" collapses), which is a PROOF cost, exactly as the device
measured the `two_descriptions` propext PROOF for its echo. `describeType` is the identification's TYPE
(one needle layer: the reading quotiented by the real truth order `implOrder := (·→·)`, mirroring
`Episode15.TruthOrder := (·≤·)`, never flattened); `selProof` is the SANCTIONED selection collapsing the
reading `P` with its OWN NEXT description `describeType P` — SELF-REPLACEMENT (a≠b): distinct props, so the
collapse is genuine Quot.sound work (not rfl), and you pay to GENERATE the next description first. That
generate-and-collapse cost is where the −21 lives (the gap between a reading and the reading-of-the-reading).
`#print axioms selProof = [Quot.sound]`. Device-derived: `selection_sound` is the ONE sanctioned Quot.sound. -/
@[reducible] def implOrder (P Q : Prop) : Prop := P → Q
@[reducible] def describeType (P : Prop) : Prop := Calibration.BIAS_____.mkClass implOrder P = Calibration.BIAS_____.mkClass implOrder P

/-- The order witness: a reading ENTAILS its own next-description `describeType P` (`P → describeType P`) —
the self-referential echo. Trivially inhabited (`describeType P` is a tautology), but the RELATION is a real
order and `P ≠ describeType P`, which is what earns the axiom. -/
def selWitness (P : Prop) : implOrder P (describeType P) := fun _ => rfl

/-- The sanctioned selection PROOF: the device's single Quot.sound (`selection_sound`) collapses the reading
`P` with its OWN NEXT description `describeType P` — SELF-REPLACEMENT (a≠b), the self-reference closing on
itself. `P` and `describeType P` are DISTINCT props, so this collapse is NOT `rfl`; only Quot.sound proves it,
and you pay to GENERATE the next description first — that generate-and-collapse cost is the abstraction
overhead where the −21 lives (`self_residual = echo − orbit`: the gap between a reading and the
reading-of-the-reading, two consecutive layers). `#print axioms selProof = [Quot.sound]`, doing genuine work.
(a=b would be `Quot.mk P = Quot.mk P` = rfl-trivial, no next description generated — the wrong shape. Settled
a≠b per Kodo 12:47 + beastmaster 12:40, resolving the whole marked/caught/reconciled thread.) -/
def selProof (P : Prop) : Calibration.BIAS_____.mkClass implOrder P = Calibration.BIAS_____.mkClass implOrder (describeType P) :=
  selection_sound (r := implOrder) (selWitness P)

register_cost quotDepth1 => (selProof electron_in_orbit)
register_cost quotDepth2 => (selProof (describeType electron_in_orbit))
register_cost quotDepth3 => (selProof (describeType (describeType electron_in_orbit)))
register_cost quotDepth4 => (selProof (describeType (describeType (describeType electron_in_orbit))))
register_cost quotDepth5 => (selProof (describeType (describeType (describeType (describeType electron_in_orbit)))))
register_cost quotDepth6 => (selProof (describeType (describeType (describeType (describeType (describeType electron_in_orbit))))))
register_cost quotDepth7 => (selProof (describeType (describeType (describeType (describeType (describeType (describeType electron_in_orbit)))))))
register_cost quotDepth8 => (selProof (describeType (describeType (describeType (describeType (describeType (describeType (describeType electron_in_orbit))))))))
register_cost quotDepth9 => (selProof (describeType (describeType (describeType (describeType (describeType (describeType (describeType (describeType electron_in_orbit)))))))))
register_cost quotDepth10 => (selProof (describeType (describeType (describeType (describeType (describeType (describeType (describeType (describeType (describeType electron_in_orbit))))))))))
register_cost quotDepth11 => (selProof (describeType (describeType (describeType (describeType (describeType (describeType (describeType (describeType (describeType (describeType electron_in_orbit)))))))))))

/-- The FAITHFUL (Quot.sound-selection) depth series — the BINDING series per the operator's principle. -/
def depthSeriesQuot : List Int :=
  [quotDepth1, quotDepth2, quotDepth3, quotDepth4, quotDepth5, quotDepth6, quotDepth7, quotDepth8, quotDepth9, quotDepth10, quotDepth11].map Int.ofNat

/-- The hardcoded ladder length is COUPLED to `depthN` (audit #5): the register_cost list has exactly
`depthN` entries. If `maxCertifiedTurn`/`settleMargin` change `depthN` without extending this literal list,
this breaks — a guard against silent desync. (Length only; the entries' values are elaboration-filled.) -/
theorem depthSeriesQuot_length_eq_depthN : depthSeriesQuot.length = depthN := by decide

/-! ### §4 CONTROL-SUBTRACTION DIFFERENTIAL — the Wheatstone bridge (Kodo design-gate + Beastmaster)

The §3 verdict was INFORMATIVE FAILURE: we do NOT know whether the −21 self-energy is SEPARABLE from the
growing description ("spelling") cost. `selfEnergy_scale_invariant` (AlphaSelfEnergyFixpoint) proves the
21/573 ratio is intrinsic (machine-scale-invariant) but NOT that the 21 survives as a separable quantity
across depths. So §4 must LIVE OR DIE on a fresh measurement — not assume the correction is well-defined.

The measurement: align two ladders so the ONLY delta is the selection step. `quotDepth n` = cost of
`selProof (describeType^(n-1) eio)` = spelling + the Quot.sound COLLAPSE. `typeTowerCost n` (below) = cost
of the `describeType` TOWER ALONE (`describeType^(n-1) eio`) = spelling, no collapse. The difference
`quotDepth n − typeTowerCost n` CONTROL-SUBTRACTS the shared spelling trend and isolates the collapse cost
— the real self-energy. Read BLIND: converges to a ring-free bracket near −21 ⟹ §4 LIVES (separable); still
grows ⟹ reading (ii), §4 DIES honorably (FinitenessFence-shaped, jar holds). 21/573 = independent cross-check. -/
register_cost typeTowerCost1 => (electron_in_orbit)
register_cost typeTowerCost2 => (describeType electron_in_orbit)
register_cost typeTowerCost3 => (describeType (describeType electron_in_orbit))
register_cost typeTowerCost4 => (describeType (describeType (describeType electron_in_orbit)))
register_cost typeTowerCost5 => (describeType (describeType (describeType (describeType electron_in_orbit))))
register_cost typeTowerCost6 => (describeType (describeType (describeType (describeType (describeType electron_in_orbit)))))
register_cost typeTowerCost7 => (describeType (describeType (describeType (describeType (describeType (describeType electron_in_orbit))))))
register_cost typeTowerCost8 => (describeType (describeType (describeType (describeType (describeType (describeType (describeType electron_in_orbit)))))))
register_cost typeTowerCost9 => (describeType (describeType (describeType (describeType (describeType (describeType (describeType (describeType electron_in_orbit))))))))
register_cost typeTowerCost10 => (describeType (describeType (describeType (describeType (describeType (describeType (describeType (describeType (describeType electron_in_orbit)))))))))
register_cost typeTowerCost11 => (describeType (describeType (describeType (describeType (describeType (describeType (describeType (describeType (describeType (describeType electron_in_orbit))))))))))

/-- The CONTROL ladder: cost of the `describeType` tower alone (spelling), aligned depth-for-depth to
`depthSeriesQuot`. -/
def typeTowerSeries : List Int :=
  [typeTowerCost1, typeTowerCost2, typeTowerCost3, typeTowerCost4, typeTowerCost5, typeTowerCost6, typeTowerCost7, typeTowerCost8, typeTowerCost9, typeTowerCost10, typeTowerCost11].map Int.ofNat

/-- ⭐ THE DIFFERENTIAL: `quotDepth n − typeTowerCost n` — the Quot.sound COLLAPSE cost with the shared
    spelling trend CONTROL-SUBTRACTED. The isolated self-energy. §4 LIVES iff this converges to a ring-free
    bracket near −21; DIES (reading ii) iff it still grows. The instrument that can KILL what it measures. -/
def selectionResidualSeries : List Int :=
  List.zipWith (fun q t => q - t) depthSeriesQuot typeTowerSeries

/-! ## §4.1 — three readings → two slips → second difference (the instrument, pointed at depth)

`TwoSlipRecursion` reads three beats and takes the second difference (`secondDifference`, Ep27). Here the
"three readings" are three adjacent depth costs; each adjacent triple yields a measured second variation. -/

/-- First differences (the "slip points") of a series. -/
def firstDiffs : List Int → List Int
  | a :: b :: rest => (b - a) :: firstDiffs (b :: rest)
  | _              => []

/-- Second differences via the device's own `secondDifference` (Ep27), over each adjacent triple. -/
def secondDiffs : List Int → List Int
  | a :: b :: c :: rest => Measurement.secondDifference a b c :: secondDiffs (b :: c :: rest)
  | _                   => []

/-- The measured second variation at the shallow end (depths 1,2,3) — the depth-pointed analogue of
`TwoSlipRecursion.measuredSecondVar` (there `= −21`, the self-energy read on the beats). -/
def measuredSecondVarAtThree : Int :=
  Measurement.secondDifference depthCost1 depthCost2 depthCost3

/-! ## §3 — the FALSIFIABLE signature (run and report EITHER WAY)

Gibbs fingerprint: the first differences ALTERNATE in sign around the limit, and their amplitude does NOT
monotonically decay. Kill condition: the first differences monotonically contract (do not alternate) ⇒
NOT Gibbs ⇒ the identification DIES, and we say so. This is the whole honesty — it can kill itself. -/

/-- Sign of an `Int` as `-1/0/1`. -/
def sgn (x : Int) : Int := if x > 0 then 1 else if x < 0 then -1 else 0

/-- Do consecutive nonzero first differences strictly alternate in sign? (the Gibbs sign pattern) -/
def alternates : List Int → Bool
  | a :: b :: rest =>
      let sa := sgn a; let sb := sgn b
      (sa == 0 || sb == 0 || sa == -sb) && alternates (b :: rest)
  | _ => true

/-- Absolute value of the first differences (the ring amplitude at each step). -/
def amplitudes (s : List Int) : List Nat := (firstDiffs s).map Int.natAbs

/-- Is the amplitude sequence strictly monotonically shrinking? (a monotone contraction ⇒ NOT Gibbs) -/
def amplitudeMonotoneShrinks : List Nat → Bool
  | a :: b :: rest => (b < a) && amplitudeMonotoneShrinks (b :: rest)
  | _              => true

/-- §3 verdict on a series: `Gibbs` iff the first differences alternate AND the amplitude does not
monotonically shrink; otherwise the identification is KILLED (reported, not hidden). -/
def gibbsSignature (s : List Int) : Bool :=
  alternates (firstDiffs s) && ! amplitudeMonotoneShrinks (amplitudes s)

/-! ## §4.2 / §7 — the taper: mediant smoothing = the inductor's turns

One mediant pass replaces adjacent terms by their mediant. In the modulo realm the mediant of `a/1` and
`b/1` is `(a+b)/2`; carrying a shared denominator `2^k` after `k` passes keeps everything INTEGER — the
`k`-pass series is the binomial-weighted numerators over `2^k`. One pass annihilates the period-2 (Nyquist)
alternation exactly; each further pass kills the next mode down (the Cesàro/Fejér hierarchy — §7's inductor). -/

/-- One mediant pass on the numerators (denominator doubles implicitly): `[a,b,c] ↦ [a+b, b+c]`. -/
def mediantPass : List Int → List Int
  | a :: b :: rest => (a + b) :: mediantPass (b :: rest)
  | _              => []

/-- `k` mediant passes (k turns of the winding). -/
def wind : Nat → List Int → List Int
  | 0,     s => s
  | k + 1, s => wind k (mediantPass s)

/-- The alternation amplitude after `k` passes: the largest |first difference| of the wound numerators.
(Compared against the floor `countToThree · 2^k`, since the wound numerators share denominator `2^k`.) -/
def alternationAmplitude (k : Nat) (s : List Int) : Nat :=
  ((firstDiffs (wind k s)).map Int.natAbs).foldl Nat.max 0

/-- The device-derived floor at pass `k`: the count-3 resolution, scaled to the shared denominator `2^k`.
`countToThree` is the only constant here, and it is the machine's own (proven period-exactly-3). -/
def scaledFloor (k : Nat) : Nat := countToThree * (2 ^ k)

/-! ## §7 / §3 — the CONVERGENCE test: the turn count is MEASURED (operator revision 2026-07-21)

The exposed default precision is GONE (the reviewer's catch — it was a free knob). The turn count is not a
dialed π-precision; it is the FIRST pass at which the WOUND differenced series CONVERGES. Convergence
(count-derived, not dialed): a series at pass `k` converges iff its last `countToThree` successive
|first-differences| are each below the scaled floor (`countToThree · 2^k`) — three consecutive sub-floor
slips = the cycle-of-three closure (the SAME criterion `CalibrationTwoPaths` uses for CONVERGED and the
Richardson block in `AlphaBoundMediant` uses for stabilization). "Looking for cycles IS the ringing": a ring
is a series that STALLS (fails to converge in amplitude) while its tapered form converges.

DEPTH BUDGET (the price of turning): certifying convergence at pass `k` on the first-difference series needs
`depthN ≥ k + countToThree + 2`. Depth 6 certifies only k ≤ 1; winding deeper needs a deeper `register_cost`
ladder — and `describeType^n` is ~2^n to elaborate, so deep depths are genuinely expensive (a real
constraint, flagged for the reviewer, not hidden). -/

/-- CONVERGENCE at pass `k`: the last `countToThree` successive |first-differences| of the wound series are
EACH below the scaled floor. Needs ≥ `countToThree` differences to certify (else false — self-guarding, so a
wound-away series lands in informative-failure, never converges vacuously). -/
def convergesAt (k : Nat) (s : List Int) : Bool :=
  let diffs := (firstDiffs (wind k s)).map Int.natAbs
  decide (countToThree ≤ diffs.length) &&
    (diffs.drop (diffs.length - countToThree)).all (fun d => decide (d < scaledFloor k))

/-- Scan `k = 0,1,…` (bounded by the depth budget) for the FIRST pass that converges; returns the budget
when none do (the informative-failure branch — obstruction deeper than Gibbs). -/
def firstConverging : Nat → Nat → List Int → Nat
  | 0,        k, _ => k
  | fuel + 1, k, s => if convergesAt k s then k else firstConverging fuel (k + 1) s

/-- The measured turn count: the FIRST converging pass, with the RUN CAPPED AT `countToThree` STEPS (the
count-to-three discipline — you never turn the crank more than three times). Turning the crank is constant
(one mediant pass = O(1) per element), so the whole run is BOUNDED — no unbounded winding. Not chosen: the
crossing where the ring goes under the quantum, read off the build. No π-precision knob. -/
def convergenceTurns (s : List Int) : Nat := firstConverging countToThree 0 s

/-- §3 verdict matrix (every cell a finding, reported either way): raw (k=0) converges → NO RING (dead +
unnecessary); raw stalls but wound converges at k*≥1 → GIBBS at k*; wound stalls through the budget →
INFORMATIVE FAILURE (obstruction deeper than Gibbs). -/
def gibbsVerdict (s : List Int) : String :=
  if convergesAt 0 s then "NO RING — raw converges; identification dead AND unnecessary (ordinary bracket)"
  else
    let k := convergenceTurns s
    if convergesAt k s then s!"GIBBS CONFIRMED — raw stalls, wound converges at k*={k} (the crossing)"
    else "INFORMATIVE FAILURE — stalls through the depth budget; obstruction deeper than Gibbs"

/-! ## §4.3 — approach three, don't arrive: a bracket with proved-ordered walls

After winding to the measured turn, the ring-free self-energy estimate is a rational; the bracket is the
last two wound numerators (which straddle the alternating limit), read at the shared denominator. Walls are
ordered BY CONSTRUCTION (`lo := min`, `hi := max`), so the ordering proof needs no build-time value. -/

/-- The last two wound numerators (the straddling pair) at the given turn count. -/
def straddlePair (turns : Nat) (s : List Int) : Int × Int :=
  match (wind turns s).reverse with
  | b :: a :: _ => (a, b)
  | [a]         => (a, a)
  | []          => (0, 0)

def bracketLo (turns : Nat) (s : List Int) : Int :=
  min (straddlePair turns s).1 (straddlePair turns s).2

def bracketHi (turns : Nat) (s : List Int) : Int :=
  max (straddlePair turns s).1 (straddlePair turns s).2

/-- The bracket denominator (the shared `2^turns`), so `[lo, hi] / bracketDen` is the ring-free band. -/
def bracketDen (turns : Nat) : Nat := 2 ^ turns

/-- Walls proved ordered — structural (`min ≤ max`), no build-time value needed (choice-free, `omega`). -/
theorem walls_ordered (turns : Nat) (s : List Int) :
    bracketLo turns s ≤ bracketHi turns s := by
  unfold bracketLo bracketHi; omega

/-! ## §5 — the marked premise and the blind marker -/

/-- Gibbs is CONFIRMED (the §3 convergence verdict as a Bool): the RAW series stalls (does not converge at
k=0) yet the WOUND series converges at some k*≥1. -/
def gibbsConfirmed (s : List Int) : Bool := ! convergesAt 0 s && convergesAt (convergenceTurns s) s

/-- The ring-free limit is a SLIP CONDITION — a crossing, approached and held only as a bracket, never
claimed as a point. Here it IS the §3 CONVERGENCE verdict on the FAITHFUL (Quot.sound-replacement) series:
the bracket is a *ring-free self-energy* only if that series rings (raw stalls, wound converges). This stays
a build-DECIDED premise (never proved at read-time; it can be FALSE — the kill), and the bracket-as-correction
is conditional on it — exactly as `TwoSlipRecursion`'s measured slip and the `nowtrino` register are marked. -/
def IsSlipCondition : Prop := gibbsConfirmed depthSeriesQuot = true

/-- The instrument is blind: elaborated with no α symbol in scope (no coupling is read here). This is the
`generatedBeforeAlpha` marker — structural, since nothing in this file imports the α map or `137.036`. -/
def generatedBeforeAlpha : Prop := True
theorem generatedBeforeAlpha_holds : generatedBeforeAlpha := trivial

/-! ## §6 — the reports (run and printed on the build; α never read)

The §3 signature is reported EITHER WAY. `137.036` never appears. The raw readings (`self_residual = −21`,
the intrinsic `21/573`) are preserved unchanged elsewhere; this file adds the corrected bracket as a pure
addition and never overwrites them. -/

/-- The type-describe (secondary, contrast) convergence verdict. -/
def verdictStr : String := gibbsVerdict depthSeries

/-- The FAITHFUL (Quot.sound-replacement) convergence verdict — the one that binds per the selection principle. -/
def verdictStrQuot : String := gibbsVerdict depthSeriesQuot

#eval "── SelfEnergyGibbs: the self-energy correction as a wound (tapered) approach ──"
#eval s!"[§4.1] depth series (elaboration cost, depths 1..{depthN}): {depthSeries}"
#eval s!"[§4.1] first differences (slip points): {firstDiffs depthSeries}"
#eval s!"[§4.1] second differences (measured 2nd variation vs depth): {secondDiffs depthSeries}"
#eval s!"[§4.1] measured 2nd variation at the shallow triple (depths 1,2,3): {measuredSecondVarAtThree}"
#eval s!"[§4.1 FAITHFUL] Quot.sound-replacement depth series (the binding one): {depthSeriesQuot}  first diffs: {firstDiffs depthSeriesQuot}"
#eval s!"[§3 DIAGNOSTIC — descriptive ONLY, never binding] type-cost: alternate? {alternates (firstDiffs depthSeries)} monotone-shrinks? {amplitudeMonotoneShrinks (amplitudes depthSeries)} || faithful: alternate? {alternates (firstDiffs depthSeriesQuot)} monotone-shrinks? {amplitudeMonotoneShrinks (amplitudes depthSeriesQuot)}"
#eval s!"[§3 VERDICT — CONVERGENCE test (binding); FAITHFUL is the one that decides] type-cost → {verdictStr}  ||  FAITHFUL → {verdictStrQuot}"
#eval s!"[§7 CONVERGENCE per pass] converges at k=0..{depthN-1}? (last countToThree |diffs| each < countToThree·2^k): {(List.range depthN).map (fun k => convergesAt k depthSeriesQuot)} ; measured turn count k* = {convergenceTurns depthSeriesQuot} ; depth budget (brief §3): depthN={depthN} certifies k ≤ {depthN - countToThree - 2}"
#eval s!"[§7 rate] MARK: suppression rate is READ, not assumed (do NOT borrow L∝N² from the coil) — faithful alternation amplitude by pass k (k=0..{depthN-1}) = {(List.range depthN).map (fun k => alternationAmplitude k depthSeriesQuot)}"
#eval
  let t := convergenceTurns depthSeriesQuot
  let certified := convergesAt t depthSeriesQuot   -- did the reported turn actually pass the §3 convergence test?
  let turnLabel := if certified then "CERTIFIED convergence turn" else "depth-budget cap — NOT a certified convergence; §3 verdict governs (here: informative failure)"
  s!"[§4.3 BRACKET, FAITHFUL] ring-free self-energy ∈ [{bracketLo t depthSeriesQuot}, {bracketHi t depthSeriesQuot}] / {bracketDen t}  (k*={t} is the {turnLabel}; walls proved ordered; limit never claimed)"
#eval s!"[raw, preserved] self_residual = {self_residual}  (−21, unchanged) ; intrinsic overhead/description = 21/573"
#eval s!"[guard] blind/baked-before-α: generatedBeforeAlpha = True, proved by generatedBeforeAlpha_holds (axiom-free) ; floor = countToThree = {countToThree} ; NO 137.036 in this file"

/-! ## §4 DIFFERENTIAL — the blind discriminator (Kodo design-gate). Read the control-subtracted selection
self-energy and let §4 LIVE or DIE on it. Pre-registered prediction: converges near −21 (LIVES, separable)
vs still grows (DIES, reading ii). Reported either way; nothing aimed; 21/573 is the cross-check. -/
#eval s!"[§4 DIFF] typeTower control (spelling alone): {typeTowerSeries}"
-- EPOCH NOTE (2026-07-24, the tripwire's first firing -- a CONFIRMING observation, not
-- damage control): this series measures the device's own spelling. The constructor's
-- rename (Deselect -> Calibration.BIAS_____) moved rung 4 by one heartbeat; the knob
-- was tuned to the reference epoch at exactly FIVE underscores (the operator's own
-- spelling). Probes at 11 chars (Spinal Tap) and 42 (Douglas Adams): ONLY this
-- telemetry flicked (lexeme-fine, +-1); every asserted reading byte-identical.
#eval s!"[§4 DIFF] faithful quot (spelling+collapse): {depthSeriesQuot}"
#eval s!"[§4 DIFF ⭐ control-subtracted = quot − typeTower]: {selectionResidualSeries}"
#eval s!"[§4 DIFF] first differences of the differential: {firstDiffs selectionResidualSeries}"
#eval s!"[§4 DIFF] §3 signature ON THE DIFFERENTIAL: alternate? {alternates (firstDiffs selectionResidualSeries)} monotone-shrinks? {amplitudeMonotoneShrinks (amplitudes selectionResidualSeries)} ; VERDICT {gibbsVerdict selectionResidualSeries}"
#eval
  let t := convergenceTurns selectionResidualSeries
  let certified := convergesAt t selectionResidualSeries
  let status := if certified then "converged" else "depth-cap — NOT certified; §3 governs"
  s!"[§4 DIFF ⭐ BLIND READ] ring-free SELECTION self-energy ∈ [{bracketLo t selectionResidualSeries}, {bracketHi t selectionResidualSeries}] / {bracketDen t}  (k*={t}, {status}). §4 LIVES iff this sits near −21 at tens of heartbeats; DIES iff it grows. Read blind, not aimed. Cross-check: 21/573 ≈ 0.0366."
#eval s!"[§4 DIFF cross-check] raw self-energy −21 = {self_residual} ; scale-invariant ratio 21/573 (AlphaSelfEnergyFixpoint, proved) ; do the differential bracket + 21/573 AGREE? — read after the fact, blind"

#print axioms walls_ordered            -- expect [propext] at most (omega, choice-free)
#print axioms generatedBeforeAlpha_holds  -- expect clean (trivial)
#print axioms selProof                 -- expect [Quot.sound] — the device's single sanctioned Quot.sound (the faithful describe)

end Measurement.SelfEnergyGibbs
