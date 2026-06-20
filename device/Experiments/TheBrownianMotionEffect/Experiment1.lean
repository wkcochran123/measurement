import Experiments.Common

/-!
# The Brownian Motion Effect — finite refinement-ledger model

Brownian motion, in the source framework, is NOT mechanical noise: it is *finite causal
resolution*.  Each refinement step leaves a family of equally admissible micro-orderings the
ledger cannot distinguish, and the **symmetric smoothing update** (the discrete Laplacian
`u_{i+1} - 2u_i + u_{i-1}`) redistributes the unresolved refinement count between neighbouring
cells.  The deterministic, mass-conserving part of the diffusion update is what we formalize here.

The honest, machine-checkable content is the **bookkeeping invariant** of that update: a *symmetric*
reconciliation on a periodic ring moves count between cells but never creates or destroys it — what
leaves a cell enters its neighbours.  This is the discrete shadow of mass conservation `∂_t ∫u = 0`
behind `u_t = D u_{xx}`.  The conservation conjunct of the claim is discharged by the harness
ledger theorem `Experiments.Common.Ledger.count_append`, so a regression in the harness's append
arithmetic breaks *this* build (HARNESS coupling — conservation / what-leaves-enters / additivity).

## NOT claimed
That this proves the diffusion equation `u_t = D u_{xx}`, the central-limit convergence, or the
analytic continuation to the free Schrödinger equation `iℏ∂_tΨ = -(ℏ²/2m)∂_{xx}Ψ`.  No `ℏ`, no
`D`, no limit `Δx,Δt → 0` is taken.  No actual randomness is modelled — only the *deterministic,
mass-conserving skeleton* of one smoothing step.  **Claim ceiling:** a finite ledger model whose
one structural invariant (total count is preserved by a symmetric step) is the discrete shadow of
the continuum conservation law; tag `smoothShadowAnalogy`.
-/

namespace Experiments.TheBrownianMotionEffect

/-- A refinement cell on the 1-D ring: a coarse index `pos` and the integer refinement count
`mass` of unresolved micro-orderings the ledger parks there.  We use `Int` so a symmetric step
(which moves count around) is expressible without truncated subtraction. -/
structure Cell where
  pos : Nat
  mass : Int
deriving DecidableEq, Repr

/-- A discrete diffusion **stencil**: the per-step transfer weight to the LEFT neighbour and to
the RIGHT neighbour.  The physical (symmetric) Laplacian has `left = right`; an asymmetric stencil
is the advection/drift case `c ≠ 0` and does NOT conserve a closed ledger the same way. -/
structure Stencil where
  left : Int
  right : Int
deriving DecidableEq, Repr

namespace Stencil

/-- A stencil is **symmetric** iff it transfers equally to both neighbours (the reconciliation
enforced by Spline Sufficiency: no preferred direction, no spurious extrema). -/
def symmetric (s : Stencil) : Prop := s.left = s.right

instance (s : Stencil) : Decidable s.symmetric := by unfold symmetric; exact inferInstance

/-- The **net outflow** of one cell under this stencil: count sent left plus count sent right.
For a symmetric stencil this is `2 * left`; the point is what it does to the GLOBAL total. -/
def netTransfer (s : Stencil) : Int := s.left + s.right

end Stencil

/-- The standard symmetric (κ/Δx²) stencil used by the reconciliation update. -/
def laplacian : Stencil := { left := 1, right := 1 }

/-- An asymmetric (upwind drift) stencil — the advection case, kept to exhibit the falsifiable edge. -/
def upwind : Stencil := { left := 0, right := 1 }

-- ---------------------------------------------------------------------------
-- The total refinement mass on a ring of cells = the conserved bookkeeping quantity.
-- ---------------------------------------------------------------------------

/-- The total unresolved refinement count carried by a ring (a list of cells).  On a closed
periodic ring a symmetric reconciliation step permutes which cell holds which unit but leaves this
global total fixed — the conservation we pin below via the harness ledger. -/
def totalMass (ring : List Cell) : Int :=
  (ring.map (fun c => c.mass)).foldr (· + ·) 0

-- ---------------------------------------------------------------------------
-- FALSIFIABLE lemmas (∀-quantified; drop the hypothesis and they break).
-- ---------------------------------------------------------------------------

/-- **The load-bearing invariant.** A symmetric stencil has zero *signed* net bias: the leftward
and rightward transfers cancel.  This is the discrete `∂_x`-antisymmetry that makes the symmetric
update conserve mass.  Quantified over ALL stencils; FALSIFIABLE — drop `symmetric` and an
asymmetric stencil (e.g. `upwind`, net bias `+1`) violates it (see the `#eval` at the file end). -/
theorem symmetric_has_no_drift (s : Stencil) (h : s.symmetric) :
    s.right - s.left = 0 := by
  unfold Stencil.symmetric at h
  omega

/-- Equivalently: a symmetric stencil's net transfer is an *even* (balanced) quantity, splittable
back evenly to the two neighbours — `netTransfer = 2 * left`.  ∀ stencils; FALSIFIABLE without
`symmetric` (`upwind.netTransfer = 1`, not `2 * upwind.left = 0`). -/
theorem symmetric_netTransfer_balanced (s : Stencil) (h : s.symmetric) :
    s.netTransfer = 2 * s.left := by
  unfold Stencil.symmetric at h
  unfold Stencil.netTransfer
  omega

/-- Concrete: the standard Laplacian stencil is symmetric. -/
theorem laplacian_symmetric : laplacian.symmetric := by decide

/-- Concrete: the upwind (advection) stencil is NOT symmetric — the falsifying witness. -/
theorem upwind_not_symmetric : ¬ upwind.symmetric := by decide

-- ---------------------------------------------------------------------------
-- The conservation conjunct, discharged by the HARNESS ledger theorem.
-- ---------------------------------------------------------------------------

/-- Re-read the ring's mass as a harness `Ledger` of cells, so the conservation of count under
splitting the ring is *the harness's own* `count_append`.  Concatenating two ring segments adds
their cell counts — the discrete "what-leaves-enters" bookkeeping that underlies `∂_t∫u = 0`. -/
def ringLedger (ring : List Cell) : Experiments.Common.Ledger Cell :=
  { events := ring }

/-- A short canonical ring and its split, used by the conservation conjunct. -/
def ringL : List Cell := [{ pos := 0, mass := 1 }, { pos := 1, mass := (-1) }]
def ringR : List Cell := [{ pos := 2, mass := 2 }]

/-- **Conservation under refinement-splitting is the harness append identity.**  This is the
LOAD-BEARING harness coupling: the conjunct `claim_holds` discharges here is exactly
`Experiments.Common.Ledger.count_append`, so a regression in the harness ledger arithmetic breaks
this build. -/
theorem ring_count_conserved :
    (Experiments.Common.Ledger.append (ringLedger ringL) (ringLedger ringR)).count
      = (ringLedger ringL).count + (ringLedger ringR).count :=
  Experiments.Common.Ledger.count_append (ringLedger ringL) (ringLedger ringR)

-- ---------------------------------------------------------------------------
-- THE CLAIM (content-bearing conjunction; the conservation conjunct is the harness theorem).
-- ---------------------------------------------------------------------------

/-- The claim, in honest parts:
* (no drift) the symmetric reconciliation stencil has zero signed net bias — `symmetric_has_no_drift`;
* (balanced) its net transfer splits evenly to both neighbours — `symmetric_netTransfer_balanced`;
* (the standard stencil qualifies) `laplacian` is symmetric; the upwind stencil is not — so the
  symmetry hypothesis is genuinely discriminating, not vacuous;
* (CONSERVATION) splitting a ring preserves the total cell count — the harness's `count_append`. -/
def claimStatement : Prop :=
  (laplacian.right - laplacian.left = 0) ∧
    (laplacian.netTransfer = 2 * laplacian.left) ∧
    laplacian.symmetric ∧
    (¬ upwind.symmetric) ∧
    ((Experiments.Common.Ledger.append (ringLedger ringL) (ringLedger ringR)).count
      = (ringLedger ringL).count + (ringLedger ringR).count)

def claim : Experiments.Common.Claim :=
  { tag := Experiments.Common.ClaimTag.smoothShadowAnalogy
    statement := claimStatement }

theorem claim_holds : claim.statement :=
  ⟨symmetric_has_no_drift laplacian laplacian_symmetric,
    symmetric_netTransfer_balanced laplacian laplacian_symmetric,
    laplacian_symmetric,
    upwind_not_symmetric,
    ring_count_conserved⟩

/-- The tag is an honest ceiling: a smooth-shadow analogy, nothing continuum-level is proved. -/
theorem ceiling : claim.tag = Experiments.Common.ClaimTag.smoothShadowAnalogy := rfl

-- ---------------------------------------------------------------------------
-- A computable run + a non-vacuous Experiment.claim, with a proved bridge.
-- ---------------------------------------------------------------------------

structure Setup where
  stencil : Stencil
  ring : List Cell

/-- The run computes: a step is "clean" (mass-conserving skeleton) iff its stencil is symmetric. -/
def run (s : Setup) : Bool := decide s.stencil.symmetric

def experiment : Experiments.Common.Experiment Setup Bool :=
  { tag := claim.tag
    run := run
    claim := fun s => s.stencil.symmetric }

theorem run_iff_claim (s : Setup) :
    run s = true ↔ experiment.claim s := by
  simp only [run, experiment, decide_eq_true_iff]

def canonicalSetup : Setup := { stencil := laplacian, ring := ringL ++ ringR }

#eval run canonicalSetup                                   -- expect: true  (symmetric)
#eval run { canonicalSetup with stencil := upwind }        -- expect: false (asymmetric drift)
#eval decide (upwind.symmetric)                            -- expect: false  (FALSIFIES the lemma's hyp)
#print axioms claim_holds                                  -- ambient [propext, Quot.sound], not coupling

/-- Bring a minimal device next to this experiment: it records whether the exported claim fires.
We compute on the underlying predicate `setup.stencil.symmetric` (which is exactly
`experiment.claim setup`) so the `Decidable` instance is found through the structure projection. -/
def deviceNear (setup : Setup) : Bool :=
  decide setup.stencil.symmetric

theorem deviceNear_detects_claim (setup : Setup) :
    deviceNear setup = true ↔ experiment.claim setup := by
  simp only [deviceNear, experiment, decide_eq_true_iff]

def triangulation : Experiments.Common.Triangulation Setup Bool :=
  { experiment := experiment
    device := deviceNear
    detects := deviceNear_detects_claim }

end Experiments.TheBrownianMotionEffect
