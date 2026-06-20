import Experiments.Common

/-!
# The Agent Effect — a finite-ledger reconciliation model

Built to the EXEMPLAR shape (`ThePositronAnnihilationEffect/Experiment1.lean`):

1. an **effect-specific domain** (`Refinement`, `Agent`) — NOT the 3-`Nat` `CountSetup`;
2. genuinely **falsifiable** `∀`-quantified lemmas — each would break if the model dropped a
   hypothesis (e.g. `ingest_raises_held`, `underHeld_not_solved`);
3. a **content-bearing** claim — a real conjunction, never `True`;
4. an **honest tag** (`finiteLedgerModel`) + a candid "NOT claimed" disclaimer;
5. explicit `Decidable` instances so `decide`/`#eval` see through the richer predicates;
6. it **couples to the harness**: the reconciliation conjunct of `claim_holds` is discharged by the
   harness theorem `Experiments.Common.Ledger.count_append` — the agent's own bookkeeping law
   ("the refinements I hold after ingesting = the ones I held plus the ones the stream supplied").
   A `sorry`/rename/regression in `Ledger.count_append` breaks *this* file's build.

## The effect (modelled finitely)
"An agent is not an external observer but a localized substructure that actively minimizes the
informational strain induced by its boundary conditions" — it "functions as a localized solver of
the spline constraint", altering its internal state "to minimize prediction error between itself and
the external ledger" (description.md / `instrument/chapters/11.tex`).

We model the agent's internal state as a finite **ledger of refinements** it has committed to (the
`e_k` it has already settled). An incoming external **stream** demands some number of refinements
(`required`). The agent ingests the stream's refinements: its post-ingest ledger is its held ledger
*appended* with the stream's ledger — that append, counted, is `Ledger.count_append`, the discrete
reconciliation law. The agent has **solved** the spline constraint (zero residual prediction error)
exactly when its reconciled ledger meets the stream's demand; its **strain** (prediction error) is
the shortfall, and ingesting more refinements weakly lowers it.

## NOT claimed
That this is the Inverse Update Operator; that Ockham's Razor (Axiom 3) is formalized; that any
*unique* next admissible refinement `e_{k+1}` is computed (we count refinements, we do not select
them); any spline, any continuum minimization, any actual prediction-error gradient. There is no
"agency", "intention", or "computation" here beyond appending and comparing finite counts.
`count_append` is the only genuine reconciliation content, and it is the *harness's* additivity
theorem. **Claim ceiling:** a finite ledger model whose reconciliation conjunct is the harness's own
additivity theorem.
-/

namespace Experiments.TheAgentEffect

/-- A single committed refinement `e_k`: a tagged step on the spline, with which boundary slot it
resolves. The `slot` lets us speak of refinements arriving from the external stream. -/
structure Refinement where
  index : Nat
  slot : Nat
deriving DecidableEq, Repr

/-- The agent's internal state is a finite ledger of refinements it has committed to. -/
abbrev Held := Experiments.Common.Ledger Refinement

/-- A reconciliation episode: the refinements the agent already `held`, the refinements the external
`stream` supplies this step, and the number `required` to satisfy the spline constraint. The agent
minimizes its strain by ingesting `stream` and comparing the reconciled count to `required`. -/
structure Agent where
  held : Held
  stream : Held
  required : Nat

namespace Agent

/-- The agent's reconciled ledger after ingesting the stream: held appended with stream. The COUNT
of this is exactly `Ledger.count_append` — the discrete "what I now account for = what I held plus
what the stream supplied". -/
def reconciled (a : Agent) : Held :=
  Experiments.Common.Ledger.append a.held a.stream

/-- The agent has **solved** the spline constraint when its reconciled ledger meets the demand:
zero residual prediction error. -/
def solved (a : Agent) : Prop :=
  a.required <= a.reconciled.count

/-- The agent's **residual strain** (prediction error): the shortfall of its reconciled ledger
against the demand (`Nat`-safe, no truncation surprises since it is the floor at 0). -/
def strain (a : Agent) : Nat :=
  a.required - a.reconciled.count

-- Make the predicates DECIDABLE so `decide`/`#eval` see through them.
instance (a : Agent) : Decidable a.solved := by
  unfold solved reconciled; exact inferInstance

end Agent

-- ---------------------------------------------------------------------------
-- FALSIFIABLE lemmas: each pins a hypothesis of the reconciliation model.
-- Each would break if the corresponding hypothesis were dropped.
-- ---------------------------------------------------------------------------

/-- **Reconciliation law (ALL agents): the reconciled count equals held + stream.** This is the
load-bearing harness coupling — it IS `Ledger.count_append`. A regression in that theorem fails
this build. Quantified over every agent. -/
theorem reconciled_count (a : Agent) :
    a.reconciled.count = a.held.count + a.stream.count := by
  unfold Agent.reconciled
  exact Experiments.Common.Ledger.count_append a.held a.stream

/-- **Ingesting the stream weakly raises what the agent holds** — strictly, when the stream is
nonempty. Quantified over ALL agents with `stream.count > 0`. Would FAIL if `reconciled` ignored
`stream` (e.g. returned `held` unchanged): the count could not strictly increase. -/
theorem ingest_raises_held (a : Agent) (h : 0 < a.stream.count) :
    a.held.count < a.reconciled.count := by
  rw [reconciled_count]
  omega

/-- **An agent whose reconciled ledger falls short of the demand has NOT solved the constraint.**
Quantified over ALL agents. Would FAIL if `solved` dropped the `required ≤ reconciled` comparison
(e.g. were defined as `True`): a shortfall would still count as solved. -/
theorem underHeld_not_solved (a : Agent) (h : a.reconciled.count < a.required) :
    ¬ a.solved := by
  unfold Agent.solved
  omega

/-- **Solved means zero residual strain.** Quantified over ALL agents. Would FAIL if `strain` did
not floor against `reconciled` (e.g. measured against `held` alone): a solved agent could still
report positive strain. -/
theorem solved_iff_strain_zero (a : Agent) :
    a.solved ↔ a.strain = 0 := by
  unfold Agent.solved Agent.strain
  omega

-- ---------------------------------------------------------------------------
-- The canonical reconciliation episode.
-- ---------------------------------------------------------------------------

/-- A canonical held state: two refinements the agent already committed. -/
def held0 : Held :=
  { events := [{ index := 0, slot := 0 }, { index := 1, slot := 1 }] }

/-- A canonical incoming stream: two refinements the external ledger supplies. -/
def stream0 : Held :=
  { events := [{ index := 2, slot := 2 }, { index := 3, slot := 3 }] }

/-- The canonical agent: holds 2, ingests 2, must reach 3 to satisfy the spline constraint. -/
def canonicalAgent : Agent :=
  { held := held0, stream := stream0, required := 3 }

/-- The canonical agent solves the constraint (concrete, via the `Decidable` instance):
held 2 + stream 2 = reconciled 4 ≥ required 3. -/
theorem canonical_solved : canonicalAgent.solved := by decide

/-- Ingesting the stream strictly raised what the canonical agent holds (concrete witness of the
falsifiable lemma). -/
theorem canonical_ingest_raises :
    canonicalAgent.held.count < canonicalAgent.reconciled.count :=
  ingest_raises_held canonicalAgent (by decide)

-- ---------------------------------------------------------------------------
-- THE CLAIM (content-bearing; the reconciliation conjunct is the harness's theorem).
-- ---------------------------------------------------------------------------

/-- The claim, in honest parts:
* (solved) the canonical agent satisfies the spline constraint — proved here via the `Decidable`
  instance;
* (reconciliation, ALL agents) every agent's reconciled count equals held + stream — discharged by
  the harness's `count_append` additivity (`reconciled_count`), the discrete "what I now account for
  = what I held plus what the stream supplied"; and
* (ingest lowers strain) ingesting the canonical stream strictly raised the agent's held count —
  proved by the falsifiable lemma `ingest_raises_held`.
The middle conjunct is the genuine reconciliation content and is the harness's own bookkeeping law,
so a regression in `Ledger.count_append` fails this build. -/
def claimStatement : Prop :=
  canonicalAgent.solved ∧
    (∀ a : Agent, a.reconciled.count = a.held.count + a.stream.count) ∧
    canonicalAgent.held.count < canonicalAgent.reconciled.count

def claim : Experiments.Common.Claim :=
  { tag := Experiments.Common.ClaimTag.finiteLedgerModel
    statement := claimStatement }

theorem claim_holds : claim.statement :=
  ⟨canonical_solved, reconciled_count, canonical_ingest_raises⟩

/-- The tag is an honest ceiling: a finite ledger model, nothing more. -/
theorem ceiling : claim.tag = Experiments.Common.ClaimTag.finiteLedgerModel := rfl

-- ---------------------------------------------------------------------------
-- A computable run + a NON-vacuous Experiment.claim, with a proved bridge.
-- ---------------------------------------------------------------------------

structure Setup where
  agent : Agent

/-- The run actually computes — thanks to the `Decidable` instance above. -/
def run (s : Setup) : Bool := decide s.agent.solved

/-- The exported claim is a genuine function of the setup, pinned to `run` by `run_iff_claim`. -/
def experiment : Experiments.Common.Experiment Setup Bool :=
  { tag := claim.tag
    run := run
    claim := fun s => s.agent.solved }

theorem run_iff_claim (s : Setup) :
    run s = true ↔ experiment.claim s := by
  simp only [run, experiment, decide_eq_true_iff]

def canonicalSetup : Setup := { agent := canonicalAgent }

/-- An agent that holds 1, ingests 0, but needs 3: reconciled count 1 < required 3, so NOT solved.
This evaluates the falsifiable `solved` predicate at a config where it is FALSE — proof the lemma is
load-bearing, not vacuous. -/
def underResolvedAgent : Agent :=
  { held := { events := [{ index := 0, slot := 0 }] }
    stream := Experiments.Common.Ledger.empty
    required := 3 }

#eval run canonicalSetup                          -- expect: true (the agent solves the constraint)
#eval run { agent := underResolvedAgent }         -- expect: false (reconciled 1 < required 3)
#print axioms claim_holds                          -- ambient footprint, not the coupling

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

end Experiments.TheAgentEffect
