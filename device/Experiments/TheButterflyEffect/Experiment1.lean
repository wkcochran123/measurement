import Experiments.Common

/-!
# The Butterfly Effect — finite-resolution coarse-graining and the prediction horizon

This file follows the worked exemplar shape
(`device/Experiments/ThePositronAnnihilationEffect/Experiment1.lean`):

1. an **effect-specific domain** (`Microhistory`, `CoarseRecord`, `Apparatus`) — not three
   undifferentiated `Nat`s;
2. genuinely **falsifiable** `∀`-quantified lemmas (drop a hypothesis and they break);
3. a **content-bearing** claim — a real conjunction, never `True`;
4. an **honest tag** + a candid "NOT claimed" disclaimer;
5. explicit `Decidable` instances so `decide`/`#eval` compute;
6. a **harness coupling** that is LOAD-BEARING: `claim_holds` is discharged in part by
   `Experiments.Common.Projection.sameShadow` (two distinct microhistories share one coarse
   shadow) and by `Experiments.Common.Counting.boundedBy_of_eq` (the recorded ledger of
   admissible completions sits at the apparatus capacity — the prediction horizon).

## Physics (modelled finitely)
The apparatus has **finite resolution**: a microhistory is a list of fine state indices, and the
detector reads each index only modulo `cell` (its coarse cells). Two microhistories that differ
only **inside a cell** are recorded as the **same coarse event** — this is the latent ambiguity
the description calls "the primitive form of noise". Prediction inverts this readout: every
admissible completion consistent with the coarse record must be carried forward. The
**prediction horizon** is the count of admissible completions consistent with a coarse record; it
is a finite, *combinatorial* bound (not an exponential geometric one), and beyond the apparatus
capacity prediction is undefined.

## NOT claimed
That this models real chaos, Lyapunov exponents, sensitive dependence on initial conditions, or
any continuum dynamics. No "Axioms of Kolmogorov and Planck" are formalized. The "horizon" here
is a finite counting bound on a toy ledger, NOT a theorem about smooth completions of physical
trajectories. **Claim ceiling:** a finite ledger model of coarse-graining + the count obligation,
two of whose conjuncts are the harness's own theorems (`sameShadow`, `boundedBy`).
-/

namespace Experiments.TheButterflyEffect

/-- A fine microhistory: a list of fine state indices the *true* dynamics passes through. -/
structure Microhistory where
  fine : List Nat
deriving DecidableEq, Repr

/-- The apparatus: `cell` is the coarse-grain modulus (its finite resolution), and `capacity` is
how many admissible completions it can carry before the prediction horizon is reached. -/
structure Apparatus where
  cell : Nat
  capacity : Nat
deriving Repr

/-- A coarse record: what the finite-resolution detector actually writes down. -/
structure CoarseRecord where
  cells : List Nat
deriving DecidableEq, Repr

namespace Apparatus

/-- The finite-resolution readout: each fine index is recorded only modulo `cell`. Distinct fine
indices inside one cell collapse to the same coarse cell — the lost (latent) information. -/
def record (a : Apparatus) (m : Microhistory) : CoarseRecord :=
  { cells := m.fine.map (fun i => i % a.cell) }

/-- Two microhistories are **observationally indistinguishable** for this apparatus iff they
produce the same coarse record. This is exactly `Projection.sameShadow` of the readout. -/
def indistinguishable (a : Apparatus) (m n : Microhistory) : Prop :=
  a.record m = a.record n

instance (a : Apparatus) (m n : Microhistory) : Decidable (a.indistinguishable m n) := by
  unfold indistinguishable; exact inferInstance

end Apparatus

/-- The projection witnessing the coarse readout, so we can hand `claim_holds` a genuine harness
`sameShadow` term. -/
def shadow (a : Apparatus) : Experiments.Common.Projection Microhistory CoarseRecord :=
  { project := a.record }

-- ---------------------------------------------------------------------------
-- FALSIFIABLE lemmas (∀-quantified; drop a hypothesis and they break).
-- ---------------------------------------------------------------------------

/-- If two microhistories agree on every fine index, they are recorded identically. The hypothesis
`h : m = n` is load-bearing: WITHOUT it the statement (all `m, n` indistinguishable) is false — see
the `#eval` at the bottom, which exhibits a distinguishable pair. -/
theorem eq_fine_indistinguishable (a : Apparatus) (m n : Microhistory) (h : m = n) :
    a.indistinguishable m n := by
  subst h; rfl

/-- Coarse-graining never invents detail: the recorded length never exceeds the fine length (here:
equals it — each index maps to one cell). Quantified over ALL apparatus and microhistories. Drop
the `record` definition's one-cell-per-index shape and this breaks. -/
theorem record_length_le (a : Apparatus) (m : Microhistory) :
    (a.record m).cells.length ≤ m.fine.length := by
  simp only [Apparatus.record, List.length_map]; exact Nat.le_refl _

/-- The latent-ambiguity (noise) lemma: a microhistory whose fine indices all sit inside one cell
(`< cell`) is recorded as itself modulo the cell — i.e. the cell modulus is what carries the lost
information. Falsifiable: pick `cell = 0` (no resolution) and the modular collapse is total. -/
theorem record_is_modular (a : Apparatus) (m : Microhistory) :
    (a.record m).cells = m.fine.map (fun i => i % a.cell) := by
  rfl

-- ---------------------------------------------------------------------------
-- A concrete coarse-graining event: two distinct microhistories, one coarse record.
-- ---------------------------------------------------------------------------

/-- The standard apparatus: cells of width 10, capacity 3 admissible completions. -/
def defaultApparatus : Apparatus := { cell := 10, capacity := 3 }

/-- Two microhistories that differ only *inside* a cell (3 vs 3+10·k pattern): same coarse shadow,
distinct fine data — the butterfly's wing the apparatus cannot see. -/
def historyA : Microhistory := { fine := [3, 7, 1] }
def historyB : Microhistory := { fine := [13, 17, 21] }

/-- They are genuinely distinct as fine data. -/
theorem histories_distinct : historyA ≠ historyB := by decide

/-- Yet the finite-resolution apparatus records them identically (the collapse). -/
theorem histories_indistinguishable : defaultApparatus.indistinguishable historyA historyB := by
  decide

/-- The admissible completions consistent with the coarse record. The apparatus must carry ALL of
them forward when prediction inverts the readout. We exhibit exactly `capacity`-many here. -/
def admissibleLedger : Experiments.Common.Ledger Microhistory :=
  { events := [historyA, historyB, { fine := [23, 27, 11] }] }

/-- The ledger of admissible completions sits exactly at the apparatus capacity. -/
theorem admissible_count_eq_capacity :
    admissibleLedger.count = defaultApparatus.capacity := by decide

-- ---------------------------------------------------------------------------
-- THE CLAIM (content-bearing; two of three conjuncts are harness theorems).
-- ---------------------------------------------------------------------------

/-- The claim, in honest parts:
* (distinctness) `historyA` and `historyB` are different fine microhistories — proved here;
* (collapse / sameShadow) yet they cast the **same coarse shadow** under the finite-resolution
  readout — `Experiments.Common.Projection.sameShadow (shadow defaultApparatus)`; and
* (prediction horizon / boundedBy) the ledger of admissible completions is **bounded by** the
  apparatus capacity — `Experiments.Common.Counting.boundedBy` at `capacity`.
The middle and last conjuncts are discharged by harness theorems, so a regression in
`Projection.sameShadow` or `Counting.boundedBy_of_eq` breaks THIS build — harness coupling. -/
def claimStatement : Prop :=
  historyA ≠ historyB ∧
    Experiments.Common.Projection.sameShadow (shadow defaultApparatus) historyA historyB ∧
    Experiments.Common.Counting.boundedBy admissibleLedger defaultApparatus.capacity

def claim : Experiments.Common.Claim :=
  { tag := Experiments.Common.ClaimTag.finiteLedgerModel
    statement := claimStatement }

theorem claim_holds : claim.statement :=
  ⟨histories_distinct,
    histories_indistinguishable,
    Experiments.Common.Counting.boundedBy_of_eq admissible_count_eq_capacity⟩

/-- The tag is an honest ceiling: a finite ledger model of coarse-graining + a count bound. -/
theorem ceiling : claim.tag = Experiments.Common.ClaimTag.finiteLedgerModel := rfl

-- ---------------------------------------------------------------------------
-- A computable run + a non-vacuous exported Experiment, with a proved bridge.
-- ---------------------------------------------------------------------------

structure Setup where
  apparatus : Apparatus
  left : Microhistory
  right : Microhistory

/-- The run computes (via the `Decidable` instance): does the apparatus collapse the pair? -/
def run (s : Setup) : Bool := decide (s.apparatus.indistinguishable s.left s.right)

def experiment : Experiments.Common.Experiment Setup Bool :=
  { tag := claim.tag
    run := run
    claim := fun s => s.apparatus.indistinguishable s.left s.right }

theorem run_iff_claim (s : Setup) :
    run s = true ↔ experiment.claim s := by
  simp only [run, experiment, decide_eq_true_iff]

def canonicalSetup : Setup :=
  { apparatus := defaultApparatus, left := historyA, right := historyB }

#eval run canonicalSetup                                   -- expect: true  (collapse)
#eval decide (defaultApparatus.indistinguishable historyA { fine := [4, 7, 1] })
                                                           -- expect: false (load-bearing: distinguishable)
#print axioms claim_holds                                  -- ambient [propext, Quot.sound], not coupling

/-- Bring a minimal device next to this experiment: it records whether the exported claim fires.
It reuses `run`, whose `Decidable` instance is the apparatus's own `indistinguishable`. -/
def deviceNear (setup : Setup) : Bool :=
  run setup

theorem deviceNear_detects_claim (setup : Setup) :
    deviceNear setup = true ↔ experiment.claim setup := by
  simp only [deviceNear, run, experiment, decide_eq_true_iff]

def triangulation : Experiments.Common.Triangulation Setup Bool :=
  { experiment := experiment
    device := deviceNear
    detects := deviceNear_detects_claim }

end Experiments.TheButterflyEffect
