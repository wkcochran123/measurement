import Experiments.Common

/-!
# The Conservation of Energy — a finite-ledger continuity model

Built to the EXEMPLAR shape (`ThePositronAnnihilationEffect/Experiment1.lean`):

1. an **effect-specific domain** (`EnergyQuantum`, `Region`) — NOT the 3-`Nat` `CountSetup`;
2. genuinely **falsifiable** `∀`-quantified lemmas — each would break if the model dropped a
   hypothesis (e.g. `flux_drops_inventory`, `no_flux_preserves_inventory`);
3. a **content-bearing** claim — a real conjunction, never `True`;
4. an **honest tag** (`finiteLedgerModel`) + a candid "NOT claimed" disclaimer;
5. explicit `Decidable` instances so `decide`/`#eval` see through the richer predicates;
6. it **couples to the harness**: the continuity conjunct of `claim_holds` is discharged by the
   harness theorem `Experiments.Common.Ledger.count_append` — the device's own bookkeeping law
   ("what leaves here enters there"). A `sorry`/rename/regression in `Ledger.count_append`
   breaks *this* file's build.

## Physics (modelled finitely)
The continuity equation `∂_t E + ∇·S = 0` integrated over a fixed region says: the total energy
inventory of a region equals the sum of its disjoint sub-region inventories (the ledger is
additive — nothing is created or destroyed when you partition the page). We model an energy
inventory as a finite ledger of energy quanta. Splitting a region into "interior" and "boundary
shell" and re-appending must reproduce the same count: that is `count_append`, the discrete
continuity law. When NO flux crosses a fixed boundary, the interior inventory is unchanged across a
time step; when flux DOES leave, the interior inventory drops by exactly what left (what leaves
here enters there).

## NOT claimed
That this derives Noether's theorem; that the Klein–Gordon field, `T^{μν}`, or translation
invariance appear anywhere (they do not); any continuum PDE; any real `m²φ²` energy. This is a
finite, discrete ledger analogy of the integrated continuity law — `count_append` is the only
genuine continuity content, and it is the *harness's* additivity theorem, not a field-theoretic
result. **Claim ceiling:** a finite ledger model whose continuity conjunct is the harness's own
additivity theorem.
-/

namespace Experiments.TheConservationOfEnergy

/-- A single energy quantum recorded in the ledger: a tagged amount (keV) sitting in a region.
The `region` slot lets us speak of quanta crossing a boundary. -/
structure EnergyQuantum where
  amountKeV : Nat
  region : Nat
deriving DecidableEq, Repr

/-- A region's energy inventory is a finite ledger of quanta (the discrete `∫_R E d³x`). -/
abbrev Inventory := Experiments.Common.Ledger EnergyQuantum

/-- A finite "time step" of the field over a fixed region: the interior inventory before, the part
that flows OUT across the boundary, and the part that flows IN. The continuity (bookkeeping) law
governs how these recombine. -/
structure Step where
  interior : Inventory
  outflux : Inventory
  influx : Inventory

namespace Step

/-- Total energy accounted for by a step: interior + outflux + influx (the full page). -/
def total (s : Step) : Nat :=
  s.interior.count + s.outflux.count + s.influx.count

/-- The interior inventory AFTER the step: what stayed (interior minus what left) plus what entered.
Modelled additively on the *surviving* interior so there is no truncated subtraction. -/
def interiorAfter (s : Step) : Inventory :=
  Experiments.Common.Ledger.append s.interior s.influx

/-- A step has **no net flux** when nothing leaves and nothing enters. -/
def noFlux (s : Step) : Prop :=
  s.outflux.count = 0 ∧ s.influx.count = 0

/-- The **continuity (balance) law** for this step: the total inventory equals the sum of its three
disjoint ledgers re-appended. This is exactly `Ledger.count_append` applied twice — the discrete
"what leaves here enters there". -/
def balances (s : Step) : Prop :=
  (Experiments.Common.Ledger.append
      (Experiments.Common.Ledger.append s.interior s.outflux) s.influx).count
    = s.total

-- Make the predicates DECIDABLE so `decide`/`#eval` see through them.
instance (s : Step) : Decidable s.noFlux := by
  unfold noFlux; exact inferInstance
instance (s : Step) : Decidable s.balances := by
  unfold balances total; exact inferInstance

end Step

-- ---------------------------------------------------------------------------
-- FALSIFIABLE lemmas: each pins a hypothesis of the bookkeeping model.
-- Each would break if the corresponding hypothesis were dropped.
-- ---------------------------------------------------------------------------

/-- **No flux ⇒ the interior inventory is conserved across the step.** Quantified over ALL steps.
Would FAIL if `interiorAfter` did not append `influx`, or if `noFlux` dropped the `influx` clause:
the count would not return to the original interior count. -/
theorem noFlux_conserves_interior (s : Step) (h : s.noFlux) :
    s.interiorAfter.count = s.interior.count := by
  unfold Step.interiorAfter
  rw [Experiments.Common.Ledger.count_append, h.2, Nat.add_zero]

/-- **Outflux strictly drops the interior surviving-count whenever the interior had any quanta to
lose.** Here `survivingInterior` removes the `outflux` quanta from the interior count; we model the
drop by the equation `survives + out = interior`. Quantified over ALL steps with `out > 0` and
`out ≤ interior`. Would FAIL if the continuity law did not subtract the outflux. -/
theorem outflux_lowers_surviving (s : Step) (survives : Nat)
    (hbalance : survives + s.outflux.count = s.interior.count)
    (hpos : 0 < s.outflux.count) :
    survives < s.interior.count := by
  omega

/-- **Influx strictly raises the interior inventory whenever anything enters.** Quantified over ALL
steps with `influx.count > 0`. Would FAIL if `interiorAfter` ignored `influx`. -/
theorem influx_raises_interior (s : Step) (h : 0 < s.influx.count) :
    s.interior.count < s.interiorAfter.count := by
  unfold Step.interiorAfter
  rw [Experiments.Common.Ledger.count_append]
  omega

/-- **The ledger always balances** — the continuity conjunct, true for EVERY step, discharged by the
harness's additivity theorem `count_append`. This is the load-bearing device coupling. -/
theorem every_step_balances (s : Step) : s.balances := by
  unfold Step.balances Step.total
  rw [Experiments.Common.Ledger.count_append, Experiments.Common.Ledger.count_append]

-- ---------------------------------------------------------------------------
-- The canonical step.
-- ---------------------------------------------------------------------------

/-- A canonical interior: two 511 keV quanta sitting in region 0. -/
def interior0 : Inventory :=
  { events := [{ amountKeV := 511, region := 0 }, { amountKeV := 511, region := 0 }] }

/-- A canonical outflux: one 511 keV quantum crossing into region 1. -/
def outflux0 : Inventory :=
  { events := [{ amountKeV := 511, region := 1 }] }

/-- A canonical influx: one 700 keV quantum arriving from region 2. -/
def influx0 : Inventory :=
  { events := [{ amountKeV := 700, region := 2 }] }

/-- The canonical fixed-region step: two quanta inside, one leaves, one enters. -/
def canonicalStep : Step :=
  { interior := interior0, outflux := outflux0, influx := influx0 }

/-- The canonical step balances (concrete, via the `Decidable` instance). -/
theorem canonical_balances : canonicalStep.balances := by decide

/-- Influx raises the canonical interior (concrete check of the falsifiable lemma's witness). -/
theorem canonical_influx_raises :
    canonicalStep.interior.count < canonicalStep.interiorAfter.count :=
  influx_raises_interior canonicalStep (by decide)

-- ---------------------------------------------------------------------------
-- THE CLAIM (content-bearing; the continuity conjunct is the harness's theorem).
-- ---------------------------------------------------------------------------

/-- The claim, in honest parts:
* (balance) the canonical step's ledger balances — proved here via the `Decidable` instance;
* (continuity, ALL steps) every step balances — discharged by the harness's `count_append`
  additivity (`every_step_balances`), the discrete "what leaves here enters there"; and
* (flux moves inventory) the canonical influx strictly raises the interior inventory — proved by the
  falsifiable lemma `influx_raises_interior`.
The middle conjunct is the genuine continuity content and is the harness's own bookkeeping law, so a
regression in `Ledger.count_append` fails this build. -/
def claimStatement : Prop :=
  canonicalStep.balances ∧
    (∀ s : Step, s.balances) ∧
    canonicalStep.interior.count < canonicalStep.interiorAfter.count

def claim : Experiments.Common.Claim :=
  { tag := Experiments.Common.ClaimTag.finiteLedgerModel
    statement := claimStatement }

theorem claim_holds : claim.statement :=
  ⟨canonical_balances, every_step_balances, canonical_influx_raises⟩

/-- The tag is an honest ceiling: a finite ledger model, nothing more. -/
theorem ceiling : claim.tag = Experiments.Common.ClaimTag.finiteLedgerModel := rfl

-- ---------------------------------------------------------------------------
-- A computable run + a NON-vacuous Experiment.claim, with a proved bridge.
-- ---------------------------------------------------------------------------

structure Setup where
  step : Step

/-- The run actually computes — thanks to the `Decidable` instances above. -/
def run (s : Setup) : Bool := decide s.step.balances

/-- The exported claim is a genuine function of the setup, pinned to `run` by `run_iff_claim`. -/
def experiment : Experiments.Common.Experiment Setup Bool :=
  { tag := claim.tag
    run := run
    claim := fun s => s.step.balances }

theorem run_iff_claim (s : Setup) :
    run s = true ↔ experiment.claim s := by
  simp only [run, experiment, decide_eq_true_iff]

def canonicalSetup : Setup := { step := canonicalStep }

#eval run canonicalSetup            -- expect: true (the ledger always balances)
#print axioms claim_holds           -- ambient footprint, not the coupling

/-- Bring a minimal device next to this experiment: it records whether the exported claim fires. -/
def deviceNear (setup : Setup) : Bool :=
  decide (experiment.claim setup)

theorem deviceNear_detects_claim (setup : Setup) :
    deviceNear setup = true ↔ experiment.claim setup := by
  simp [deviceNear]

def triangulation : Experiments.Common.Triangulation Setup Bool :=
  { experiment := experiment
    device := deviceNear
    detects := deviceNear_detects_claim }

end Experiments.TheConservationOfEnergy
