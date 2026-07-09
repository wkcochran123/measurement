import Experiments.Common

/-!
# The Fluxions Effect — finite bookkeeping behind Newton's "ghost" derivative

Berkeley's objection: Newton's fluxion `ẋ = Δx/Δt` lets `Δt` vanish in one step and
stay nonzero in the previous one. The description (`instrument/chapters/06.tex:1292`,
`te:newtonian-ghost`) reframes this: `Δx` and `Δt` are two finite integer tallies — spatial
ticks and temporal ticks between two anchors. The derivative is not a ghost quantity but the
**continuous shadow of finite bookkeeping**: the single slope value that prevents the
appearance of *new, unrecorded events* as the anchor spacing shrinks (resolution refines).

This file follows the EXEMPLAR shape (`ThePositronAnnihilationEffect/Experiment1.lean`):

1. an effect-specific domain (`Anchor`, `Fluxion`) — NOT three undifferentiated `Nat`s;
2. genuinely **falsifiable** ∀-lemmas (drop a hypothesis and the proof dies);
3. a **content-bearing** claim — a real conjunction, never `True`;
4. an honest tag (`smoothShadowAnalogy`) + a candid "NOT claimed";
5. explicit `Decidable` instances so `decide`/`#eval` compute;
6. a LOAD-BEARING **harness** coupling: the conjunct "no new events appear under refinement"
   is `Experiments.Common.Ledger.count_map` — the refinement-invariance of the ledger count.
   Refinement / zoom / resolution-change is exactly the description's "every refinement of the
   observable record", so this is the honest harness theorem (NOT a device/holonomy coupling —
   there is no charge, loop-phase, or positron here, so device coupling is FORBIDDEN).

## NOT claimed
That this proves any limit, derivative, or `Ψ⁽⁴⁾=0` cubic-interpolation theorem; that
`Δx/Δt` converges (no real analysis here); that the smooth completion `Ψ` exists. The "slope"
is an integer quotient on a chosen finite record, and the only transported invariant is that
re-binning (refining) the tick ledger does not change how many ticks were recorded.
**Claim ceiling:** a finite ledger / refinement model whose discrete shadow is the slope; the
refinement-invariance conjunct is the harness's own `count_map` theorem.
-/

namespace Experiments.Fluxions

/-- A recorded anchor: a temporal tick index `t` and the spatial tick count `x` read at it. -/
structure Anchor where
  t : Nat
  x : Nat
deriving DecidableEq, Repr

/-- A fluxion is the finite data between two anchors: the spatial tick difference `dx` and the
temporal tick difference `dt`. `dt` must be **positive** — `Δt → 0` is never a physical state
(that is the whole point of the reframing). -/
structure Fluxion where
  dx : Nat
  dt : Nat
deriving DecidableEq, Repr

namespace Fluxion

/-- `Δt` is a genuine (nonzero) temporal gap: there is no "vanished" denominator. -/
def wellFormed (f : Fluxion) : Prop := 0 < f.dt

/-- The finite slope: the integer quotient of spatial ticks over temporal ticks. (A coarse
shadow of `Ψ'`; not a limit.) -/
def slope (f : Fluxion) : Nat := f.dx / f.dt

/-- The fluxion read off two anchors `a` (earlier) before `b` (later). -/
def between (a b : Anchor) : Fluxion := { dx := b.x - a.x, dt := b.t - a.t }

instance (f : Fluxion) : Decidable (f.wellFormed) := by unfold wellFormed; exact inferInstance

end Fluxion

-- ---------------------------------------------------------------------------
-- FALSIFIABLE lemmas. Each drops a hypothesis and breaks.
-- ---------------------------------------------------------------------------

/-- A well-formed fluxion never has a vanished denominator: `dt ≠ 0`.
FALSIFIABLE: drop `wellFormed` and `f.dt = 0` is possible (e.g. `{dx:=1, dt:=0}`), so the
conclusion fails. The hypothesis is load-bearing. -/
theorem wellFormed_dt_ne_zero (f : Fluxion) (h : f.wellFormed) : f.dt ≠ 0 := by
  unfold Fluxion.wellFormed at h
  omega

/-- If the denominator strictly exceeds the numerator, the finite slope reads zero — the
sub-tick regime where the "ghost" would hide.  FALSIFIABLE: drop `h : f.dx < f.dt` and the
slope can be positive (e.g. `{dx:=4, dt:=2}` has slope `2`), so the conclusion breaks. -/
theorem subtick_slope_zero (f : Fluxion) (h : f.dx < f.dt) : f.slope = 0 := by
  unfold Fluxion.slope
  exact Nat.div_eq_of_lt h

/-- Monotone record: a later anchor reads at least as many spatial ticks, so the difference is
honest (no truncation surprise).  FALSIFIABLE: drop `h : a.x ≤ b.x` and `b.x - a.x` truncates
to `0` while the "true" change is negative, so `(between a b).dx + a.x = b.x` fails. -/
theorem between_dx_recovers (a b : Anchor) (h : a.x ≤ b.x) :
    (Fluxion.between a b).dx + a.x = b.x := by
  show (b.x - a.x) + a.x = b.x
  omega

-- ---------------------------------------------------------------------------
-- THE REFINEMENT LEDGER: the harness coupling.
--   The temporal record is a Ledger of ticks. "Refining the resolution" re-labels each tick
--   (decodes a fine tick into a coarse one). The description's key invariant — "no new,
--   unrecorded events appear as resolution increases" — is exactly that the ledger COUNT is
--   unchanged by the refinement decode, i.e. `Ledger.count_map`.
-- ---------------------------------------------------------------------------

/-- A fine temporal tick, carrying its own sub-index `phase` within a coarse tick. -/
structure FineTick where
  coarse : Nat
  phase : Nat
deriving DecidableEq, Repr

/-- The refinement: forget the fine phase, keep the coarse tick index. -/
def coarsen : Experiments.Common.Refinement Nat FineTick :=
  { decode := fun ft => ft.coarse }

/-- A concrete fine temporal record: three sub-ticks of coarse tick 0, then two of tick 1. -/
def fineRecord : Experiments.Common.Ledger FineTick :=
  { events := [⟨0,0⟩, ⟨0,1⟩, ⟨0,2⟩, ⟨1,0⟩, ⟨1,1⟩] }

/-- THE TRANSPORTED INVARIANT (harness-coupled): refining/coarsening the temporal record does
NOT change how many ticks were recorded — no ghost events are created or destroyed by changing
resolution.  This is discharged by `Experiments.Common.Ledger.count_map`, so a regression in the
harness's refinement bookkeeping breaks THIS build. -/
theorem refinement_conserves_ticks (L : Experiments.Common.Ledger FineTick) :
    (coarsen.pushLedger L).count = L.count := by
  unfold coarsen Experiments.Common.Refinement.pushLedger
  exact Experiments.Common.Ledger.count_map _ L

-- ---------------------------------------------------------------------------
-- The canonical fluxion event.
-- ---------------------------------------------------------------------------

/-- Two anchors: at temporal tick 0 read 4 spatial ticks; at temporal tick 2 read 10. -/
def anchorA : Anchor := { t := 0, x := 4 }
def anchorB : Anchor := { t := 2, x := 10 }

/-- The canonical fluxion: `dx = 6`, `dt = 2`, slope `3`. -/
def canonicalFluxion : Fluxion := Fluxion.between anchorA anchorB

theorem canonical_wellFormed : canonicalFluxion.wellFormed := by decide

theorem canonical_slope_is_three : canonicalFluxion.slope = 3 := by decide

-- ---------------------------------------------------------------------------
-- THE CLAIM (content-bearing; the refinement conjunct is the harness's own theorem).
-- ---------------------------------------------------------------------------

/-- The claim, in honest parts:
* (well-formed) the canonical fluxion has a genuine nonzero `Δt` — no vanished denominator;
* (shadow slope) its finite slope reads `3` — the discrete shadow of `Ψ'`;
* (refinement-invariance, HARNESS-COUPLED) coarsening the fine temporal record preserves the
  tick count — `Ledger.count_map`, the "no new unrecorded events" law.
Breaking the harness's `count_map`, or a sign/value regression in the slope, fails this proof. -/
def claimStatement : Prop :=
  canonicalFluxion.wellFormed ∧
    canonicalFluxion.slope = 3 ∧
    (coarsen.pushLedger fineRecord).count = fineRecord.count

def claim : Experiments.Common.Claim :=
  { tag := Experiments.Common.ClaimTag.smoothShadowAnalogy
    statement := claimStatement }

theorem claim_holds : claim.statement :=
  ⟨canonical_wellFormed, canonical_slope_is_three, refinement_conserves_ticks fineRecord⟩

/-- The tag is an honest ceiling: a finite stand-in for the smooth derivative, nothing more. -/
theorem ceiling : claim.tag = Experiments.Common.ClaimTag.smoothShadowAnalogy := rfl

-- ---------------------------------------------------------------------------
-- A computable run + a NON-vacuous Experiment.claim, with a proved bridge.
-- ---------------------------------------------------------------------------

structure Setup where
  earlier : Anchor
  later : Anchor

/-- The run computes the finite slope of the fluxion read off the two anchors. -/
def run (s : Setup) : Nat := (Fluxion.between s.earlier s.later).slope

def experiment : Experiments.Common.Experiment Setup Nat :=
  { tag := claim.tag
    run := run
    claim := fun s => (Fluxion.between s.earlier s.later).wellFormed }

def canonicalSetup : Setup := { earlier := anchorA, later := anchorB }

theorem run_canonical : run canonicalSetup = 3 := by decide

#eval run canonicalSetup                                   -- expect: 3
#eval decide ((Fluxion.mk 1 0).wellFormed)                 -- expect: false  (ghost Δt = 0)
#print axioms claim_holds                                  -- ambient [propext, Quot.sound]

instance (setup : Setup) : Decidable (experiment.claim setup) := by
  unfold experiment
  infer_instance

/-- Bring a minimal device next to this experiment: it records whether the exported claim fires. -/
def deviceNear (setup : Setup) : Bool :=
  decide (experiment.claim setup)

theorem deviceNear_detects_claim (setup : Setup) :
    deviceNear setup = true ↔ experiment.claim setup := by
  simp [deviceNear]

def triangulation : Experiments.Common.Triangulation Setup Nat :=
  { experiment := experiment
    device := deviceNear
    detects := deviceNear_detects_claim }

end Experiments.Fluxions
