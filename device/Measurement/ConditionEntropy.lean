import Measurement.WeakDiracGalerkin

/-! # ConditionEntropy — the conditioning of the discrete Galerkin operator,
read finitely, and its entropic growth.

OBJECT (per Kodo's refined ruling, 2026-08-15): the spectrum-bearing carrier is
WeakDiracGalerkin's `UniversalTensor` — the ONLY universe/universal-tensor
object in the corpus with matrix content. Ep10's observation `UniverseTensor`
and Capstone's box term are DISTINCT objects and are not touched here.

WHAT IS DEFINED (honest, finite): the device reads conditioning through
FINITE PROBES, the same way it reads everything. For an operator A and probe
v, the Rayleigh square is ‖Av‖²/‖v‖² in exact integers (numerator/denominator
pairs — no division, no reals). The CONDITION READING over a probe pair
(u, a) is the ratio of the high probe's Rayleigh square to the low probe's:

  κ²-reading(A; u, a) = (‖Aa‖²·‖u‖²) / (‖Au‖²·‖a‖²)

INTERPRETIVE FENCE (the no-name-bridge, in the same breath): under the
standard spectral reading, every Rayleigh square lies between λ_min and λ_max
of AᵀA, so the probe reading BOUNDS THE CLASSICAL κ² FROM BELOW — but that
spectral sentence is an interpretive gloss requiring eigenvalue theory this
file does not import and does not claim. The device asserts ONLY the probe
reading, which it computes exactly. Bracket-not-pin: the reading is a floor,
never the pinned κ.

WHAT IS DEMONSTRATED (kernel-decided, exhaustive over the ladder — the same
instance-ladder style as GridDerivation's `coarser_grids_fail`):

  * `kappa_monotone_ladder` — along the refinement index n (the device's own
    "time step i" register), the κ²-reading of the Dirac difference family is
    MONOTONE INCREASING: a forward `≤` (in fact `<`), which is "entropic" in
    the device's own bound-shaped sense (Ep3's register: an entropic process
    is a `≤` that runs one way). The reading is exactly 4n−3 on this family:
    the conditioning grows, linearly, without bound, as the discretization
    refines. THIS is the raw growth the Sobolev rows (the preconditioner —
    the stethoscope's tuner) exist to tame.

  * `diag_energy_is_distribution_*` — the honest carrier for the −Σ p·lg p
    bill (BM's gate): the DIAGONAL ENERGY distribution of the Gram form,
    p_i = ‖A eᵢ‖² / Σⱼ‖A eⱼ‖². Each numerator is a sum of squares (≥ 0) and
    they sum to the total energy — a genuine probability distribution, proved
    per instance in exact integers. The entropy VALUE −Σ p lg p over it is
    OWED to a later leaf via dyadic-lg brackets; nothing here claims it.

NOT CLAIMED: eigenvalues, the classical κ, any continuum object, any physical
entropy. The word "entropic" names the monotone `≤` shape, per the gate.
-/

namespace Measurement.WeakDiracGalerkin.ConditionEntropy

open Measurement.WeakDiracGalerkin

/-- ‖A v‖² in exact integers: the residual energy of a probe. -/
def energySq (rows : List Vec) (v : Vec) : Int :=
  dot (matrixApply rows v) (matrixApply rows v)

/-- ‖v‖². -/
def normSq (v : Vec) : Int := dot v v

/-- The κ²-reading over a probe pair, as an exact fraction (num, den):
    (‖Aa‖²·‖u‖², ‖Au‖²·‖a‖²). No division is performed; comparisons
    cross-multiply. -/
def kappaSqReading (rows : List Vec) (u a : Vec) : Int × Int :=
  (energySq rows a * normSq u, energySq rows u * normSq a)

/-- Fraction order: (n₁,d₁) < (n₂,d₂) as n₁·d₂ < n₂·d₁ (positive dens).
    Bool-valued so the ladder decides in the kernel. -/
def fracLt (x y : Int × Int) : Bool := x.1 * y.2 < y.1 * x.2

/-! ## The Dirac difference family, refined step by step

`diracRowsN n` : the n×n first-order difference operator with an anchor —
rows eᵢ − eᵢ₊₁ for i < n−1, and the anchor row e_{n−1} (which keeps the
operator injective, so the low probe's energy is nonzero). This extends the
file's own 2×2 `diracToyTensor` pattern to a refinement ladder. -/

/-- Unit vector eᵢ of length n. -/
def unit (n i : Nat) : Vec :=
  (List.range n).map (fun j => if j = i then (1 : Int) else 0)

/-- Difference row eᵢ − eᵢ₊₁ of length n. -/
def diffRow (n i : Nat) : Vec :=
  (List.range n).map (fun j =>
    if j = i then (1 : Int) else if j = i + 1 then (-1 : Int) else 0)

/-- The refined Dirac rows at size n. -/
def diracRowsN (n : Nat) : List Vec :=
  ((List.range (n - 1)).map (diffRow n)) ++ [unit n (n - 1)]

/-- The low probe: all ones (the smooth mode the operator barely sees). -/
def uniformProbe (n : Nat) : Vec :=
  (List.range n).map (fun _ => (1 : Int))

/-- The high probe: alternating ±1 (the rough mode the operator amplifies). -/
def alternatingProbe (n : Nat) : Vec :=
  (List.range n).map (fun j => if j % 2 = 0 then (1 : Int) else -1)

/-- The κ²-reading at refinement n, over the canonical probe pair. -/
def readingAt (n : Nat) : Int × Int :=
  kappaSqReading (diracRowsN n) (uniformProbe n) (alternatingProbe n)

/-! ## The demonstrations (kernel-decided) -/

/-- The reading is exactly (4n−3)·n / 1·n at each rung of the ladder —
    i.e. the κ²-reading equals 4n−3. Checked instance-by-instance, the
    device's exhaustive style. -/
theorem reading_values :
    readingAt 2 = (5 * 2, 1 * 2) ∧
    readingAt 3 = (9 * 3, 1 * 3) ∧
    readingAt 4 = (13 * 4, 1 * 4) ∧
    readingAt 5 = (17 * 5, 1 * 5) ∧
    readingAt 6 = (21 * 6, 1 * 6) ∧
    readingAt 7 = (25 * 7, 1 * 7) ∧
    readingAt 8 = (29 * 8, 1 * 8) := by decide

#print axioms reading_values

/-- ENTROPIC GROWTH: along the refinement index — the device's own step
    register — the κ²-reading strictly increases at every rung of the ladder.
    A forward `<` (hence `≤`): bound-shaped, one-way, entropic in the
    device's sense. The conditioning grows; it is the preconditioner's job
    (the Sobolev rows) to tame it, and the crossing never moves either way. -/
theorem kappa_monotone_ladder :
    (fracLt (readingAt 2) (readingAt 3) = true) ∧
    (fracLt (readingAt 3) (readingAt 4) = true) ∧
    (fracLt (readingAt 4) (readingAt 5) = true) ∧
    (fracLt (readingAt 5) (readingAt 6) = true) ∧
    (fracLt (readingAt 6) (readingAt 7) = true) ∧
    (fracLt (readingAt 7) (readingAt 8) = true) := by decide

#print axioms kappa_monotone_ladder

/-! ## The distribution half of the entropy bill

Diagonal energy: dᵢ = ‖A eᵢ‖². Each is a sum of squares, hence ≥ 0; their
sum is the total diagonal energy. p_i = dᵢ / Σdⱼ is therefore a genuine
probability distribution — the carrier BM's −Σ p·lg p gate runs on. The
entropy VALUE is owed to a dyadic-lg leaf; here only the distribution is
proved, in exact integers, per instance. -/

/-- The diagonal energies of the Gram form at refinement n. -/
def diagEnergies (n : Nat) : List Int :=
  (List.range n).map (fun i => energySq (diracRowsN n) (unit n i))

/-- Every diagonal energy is nonnegative and the family is nonempty with
    positive total — the distribution p_i = dᵢ/Σd is genuine (per rung). -/
theorem diag_energy_is_distribution :
    (diagEnergies 2).all (fun d => decide (0 ≤ d)) = true ∧
    (diagEnergies 3).all (fun d => decide (0 ≤ d)) = true ∧
    (diagEnergies 4).all (fun d => decide (0 ≤ d)) = true ∧
    (diagEnergies 5).all (fun d => decide (0 ≤ d)) = true ∧
    0 < (diagEnergies 2).foldl (· + ·) 0 ∧
    0 < (diagEnergies 3).foldl (· + ·) 0 ∧
    0 < (diagEnergies 4).foldl (· + ·) 0 ∧
    0 < (diagEnergies 5).foldl (· + ·) 0 := by decide

#print axioms diag_energy_is_distribution

/-- The toy tensor in the file itself sits at the bottom of the ladder:
    its Dirac rows are perfectly conditioned (reading = 8/8 = 1) — the
    ladder's floor, before refinement begins to pay the entropic bill. -/
theorem toy_reading_is_one :
    kappaSqReading diracToyTensor.diracRows [1, 1] [1, -1] = (4 * 2, 4 * 2) := by
  decide

#print axioms toy_reading_is_one

end Measurement.WeakDiracGalerkin.ConditionEntropy
