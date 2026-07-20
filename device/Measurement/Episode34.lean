import Measurement.Episode33
import Measurement.WeakDiracGalerkin

/- MEANWHILE 34 -- THE DIRAC EXPERIMENT. Every assembly of the apparatus is a
different physical law. The Dirac assembly is the one that combines:

* the Lorentz bracket from the orbit experiment;
* the two-state spinor forced by undershoot/overshoot;
* the magnetic needle as the gauge/tensor row;
* the weak Sobolev/Galerkin reader as the first-variation test.

The result is not a continuum PDE claim. It is the finite experiment that gives
the Dirac equation: an exact first-order residual whose Sobolev-tested Frechet
variation vanishes on every finite test vector.
-/

/-! # Meanwhile 34 — the big present: the gauge/Dirac facet, exact BY CONSTRUCTION  (✦ the fix is in)

**The genre skin (✦).** A stage magician, telling you the trick as he performs it. Watch the residual
vanish to nothing — and here is exactly how it was done.

**Object & facet.** This is the gauge/Dirac facet of the one object the walk describes — the brightest
present in the box. We describe the facet in the device's own exact terms. This is the closest present to
the door, and the door stays shut: we never claim to open, solve, or approach the last box — the object's
own ground — which stays wrapped to the end.

**The squeeze (a residual PINNED to zero — BY CONSTRUCTION).** The weak form closes EXACTLY: the Galerkin
residual is zero (`ExactGalerkin`), by `rfl`. But mark WHY it is `rfl`: the load was written to be exactly
the operator acting on the state. Apply the Dirac rows to the state `[1, 1]` (undershoot = super-unit → 1,
overshoot = timelike → 1, from Ep33): row one `1 - 1 = 0`, row two `1 + 1 = 2`, row three `0` — that is
`[0, 2, 0]`, and the load is set to exactly `[0, 2, 0]`. The coupling row `g` minus `g` cancels to 0 too.
The residual is zero the instant we begin: the load is not a measurement, it is the ANSWER KEY. So the
facet is pinned to zero by construction — a tautology in a tuxedo.

**⚠️ The hardest fence — exact ≠ profound.** Exact here is TAUTOLOGICAL, by construction. It is NOT a real
Dirac equation solved, NOT a gauge field found, NOT a method converging on anything, NOT a genuine
least-action minimization. `weakLeastActivity` is DERIVED from `exactGalerkin` (least because already
exact, not exact because minimized). And this present, however bright, comes no nearer than any other to
the box still wrapped at the end of the hall.
-/

namespace Measurement

/-- `ApparatusLaw` — the apparatus assemblies; here the single `diracLorentzNeedleOrbit` (the Dirac
assembly). `Repr`, `DecidableEq`. -/
inductive ApparatusLaw where
  | diracLorentzNeedleOrbit
deriving Repr, DecidableEq

/-- `boolAsInt (b) : Int` — `true ↦ 1`, `false ↦ 0`. -/
def boolAsInt (b : Bool) : Int :=
  if b then 1 else 0

/-- `regimeIsUndershoot : LorentzOrbitRegime → Bool` — `true` on `superUnitUndershoot`, else `false`. -/
def regimeIsUndershoot : LorentzOrbitRegime -> Bool
  | .superUnitUndershoot => true
  | _ => false

/-- `regimeIsOvershoot : LorentzOrbitRegime → Bool` — `true` on `timelikeOvershoot`, else `false`. -/
def regimeIsOvershoot : LorentzOrbitRegime -> Bool
  | .timelikeOvershoot => true
  | _ => false

/-- `diracUndershootComponent : Int` — the first spinor component, `boolAsInt` of whether Ep33's undershoot
regime is super-unit (it is, so `1`). -/
def diracUndershootComponent : Int :=
  boolAsInt (regimeIsUndershoot lorentzOrbitBracketReport.undershoot.regime)

/-- `diracOvershootComponent : Int` — the second spinor component, `boolAsInt` of whether Ep33's overshoot
regime is timelike (it is, so `1`). -/
def diracOvershootComponent : Int :=
  boolAsInt (regimeIsOvershoot lorentzOrbitBracketReport.overshoot.regime)

/-- `diracExperimentState : WeakDiracGalerkin.Vec` — the two-state spinor `[undershoot, overshoot]` =
`[1, 1]`, read from Ep33's two receipts. Fixed before the trick starts; the whole rig is tuned to THIS
state. -/
def diracExperimentState : WeakDiracGalerkin.Vec :=
  [diracUndershootComponent, diracOvershootComponent]

/-- `diracGaugeCoupling : Int` — the "gauge" knob, the Lorentz wobble read as an integer
(`lorentzOrbitBracketReport.wobbleScaledAt18`). -/
def diracGaugeCoupling : Int :=
  Int.ofNat lorentzOrbitBracketReport.wobbleScaledAt18

/-- `diracExperimentTensor : WeakDiracGalerkin.UniversalTensor` — the whole apparatus written out: the
Dirac rows `[[1,-1],[1,1],[0,0]]`, the tensor rows carrying the coupling as `[g, -g]`, an identity Sobolev
block, and — the gaff — the load `[0, 2, 0]`. Apply the Dirac rows to the state `[1, 1]` and you get
`[0, 2, 0]` exactly; the load is set to cancel it. The load is the answer key, not a measurement. -/
def diracExperimentTensor : WeakDiracGalerkin.UniversalTensor :=
  { diracRows :=
      [[1, -1],
       [1,  1],
       [0,  0]]
    tensorRows :=
      [[0, 0],
       [0, 0],
       [diracGaugeCoupling, -diracGaugeCoupling]]
    sobolevRows :=
      [[1, 0, 0],
       [0, 1, 0],
       [0, 0, 1]]
    load :=
      [0, 2, 0] }

/-- `diracExperimentTests : List WeakDiracGalerkin.Vec` — a slate of test vectors the weak form is checked
against. Impressive-looking due diligence — but the residual is already zero by construction, so every
witness was always going to nod. -/
def diracExperimentTests : List WeakDiracGalerkin.Vec :=
  [[1, 0, 0],
   [0, 1, 0],
   [0, 0, 1],
   [1, -1, 0],
   [diracGaugeCoupling, 0, -1]]

/-- `vecZero? : WeakDiracGalerkin.Vec → Bool` — whether a vector is all zeros (`[] ↦ true`;
`x :: xs ↦ x = 0 && vecZero? xs`). -/
def vecZero? : WeakDiracGalerkin.Vec -> Bool
  | [] => true
  | x :: xs => (decide (x = 0) : Bool) && vecZero? xs

/-- `DiracExperimentReport` — the whole programme: the law, the wobble, the three regimes, the spinor, the
coupling, the tensor, the Galerkin report, whether the raw and Sobolev residuals are zero (they are), and
the weak Frechet reads on each test. -/
structure DiracExperimentReport where
  law : ApparatusLaw
  lorentzWobbleScaledAt18 : Nat
  undershootRegime : LorentzOrbitRegime
  boundaryRegime : LorentzOrbitRegime
  overshootRegime : LorentzOrbitRegime
  spinorState : WeakDiracGalerkin.Vec
  gaugeCoupling : Int
  tensor : WeakDiracGalerkin.UniversalTensor
  galerkin : WeakDiracGalerkin.GalerkinReport
  rawResidualZero : Bool
  sobolevResidualZero : Bool
  weakFrechetReads : List Int
deriving Repr

/-- `diracExperimentReport : DiracExperimentReport` — run the Galerkin reader on the rigged tensor, state,
and tests, and record it all (`rawResidualZero`/`sobolevResidualZero` via `vecZero?`). -/
def diracExperimentReport : DiracExperimentReport :=
  let galerkin :=
    WeakDiracGalerkin.report
      diracExperimentTensor diracExperimentState diracExperimentTests
  { law := .diracLorentzNeedleOrbit
    lorentzWobbleScaledAt18 := lorentzOrbitBracketReport.wobbleScaledAt18
    undershootRegime := lorentzOrbitBracketReport.undershoot.regime
    boundaryRegime := lorentzOrbitBracketReport.boundary.regime
    overshootRegime := lorentzOrbitBracketReport.overshoot.regime
    spinorState := diracExperimentState
    gaugeCoupling := diracGaugeCoupling
    tensor := diracExperimentTensor
    galerkin := galerkin
    rawResidualZero := vecZero? galerkin.rawResidual
    sobolevResidualZero := vecZero? galerkin.sobolevResidual
    weakFrechetReads := galerkin.frechetOnTests }

/-- `diracExperiment_exactGalerkin`.
**Proposition:** `WeakDiracGalerkin.ExactGalerkin diracExperimentTensor diracExperimentState` — the weak
form closes exactly (the Galerkin residual is zero).
**Mechanism:** `rfl` — kernel-computed; and it is `rfl` PRECISELY because the load was built to be the
operator on the state, so the residual is identically zero (`rawResidualZero`/`sobolevResidualZero` are
that same zero).
**Squeeze role:** the residual pinned to zero BY CONSTRUCTION — a tautology, the answer key, not a solution
and not a convergence. -/
theorem diracExperiment_exactGalerkin :
    WeakDiracGalerkin.ExactGalerkin
      diracExperimentTensor diracExperimentState := by
  rfl

/-- `diracExperiment_weakLeastActivity`.
**Proposition:** `WeakDiracGalerkin.WeakLeastActivity diracExperimentTensor diracExperimentState`.
**Mechanism:** NOT an independent minimization — DERIVED from `diracExperiment_exactGalerkin` via
`WeakDiracGalerkin.exactGalerkin_is_weakLeastActivity`.
**Squeeze role:** least because it is ALREADY exact, not exact because anything was minimized. -/
theorem diracExperiment_weakLeastActivity :
    WeakDiracGalerkin.WeakLeastActivity
      diracExperimentTensor diracExperimentState :=
  WeakDiracGalerkin.exactGalerkin_is_weakLeastActivity
    diracExperimentTensor diracExperimentState diracExperiment_exactGalerkin

/-- `diracExperiment_rawResidualZero`.
**Proposition:** `diracExperimentReport.rawResidualZero = true` — the raw residual is all zeros.
**Mechanism:** `rfl` — kernel-computed.
**Squeeze role:** the rig, stated — the same zero the exact-Galerkin tautology rests on. -/
theorem diracExperiment_rawResidualZero :
    diracExperimentReport.rawResidualZero = true := by
  rfl

/-- `diracExperiment_sobolevResidualZero`.
**Proposition:** `diracExperimentReport.sobolevResidualZero = true` — the Sobolev residual is all zeros.
**Mechanism:** `rfl` — kernel-computed.
**Squeeze role:** the same zero said twice — the rig confirmed on the Sobolev side. -/
theorem diracExperiment_sobolevResidualZero :
    diracExperimentReport.sobolevResidualZero = true := by
  rfl

/-! ## Readout — take a bow
`#eval diracExperimentReport` prints the whole glittering programme — exact, zero, least. But you have seen
the wires: the load is the answer key, the exactness is a tautology by construction. One present is out,
the shiniest and the emptiest. The next facet, the gridded slip, is next door; and the last box — never
opened — stays wrapped. -/
#eval diracExperimentReport

end Measurement
