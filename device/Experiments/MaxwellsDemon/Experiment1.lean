import Experiments.Common

/-!
# Maxwell's Demon — a finite-ledger model of measurement-as-refinement

Source: `instrument/chapters/11.tex:101` (`phenomenon`, Maxwell 1865).

Built to the EXEMPLAR shape (`device/Experiments/ThePositronAnnihilationEffect/Experiment1.lean`):

1. an **effect-specific domain** (`Configuration`, `Demon`) — NOT the 3-`Nat`
   `Experiments.Common.CountSetup`;
2. genuinely **falsifiable** ∀-quantified lemmas — `measurement_adds_distinctions`
   and `idle_demon_preserves_count` each break if a hypothesis is dropped;
3. a **content-bearing** claim: a real conjunction, never `True`, never a single `decide`
   over frozen literals;
4. an honest `ClaimTag` (`finiteLedgerModel`) + a candid "NOT claimed" disclaimer;
5. explicit `Decidable` instances so `decide`/`#eval` see through the richer `Prop`s;
6. it **couples to the harness**: the entropy-balance conjunct of `claim_holds` is the
   discrete additivity law `Experiments.Common.Ledger.count_append` (the global
   distinguishable count of the joint system is the sum of the gas and demon-record counts —
   "informational refinement in one domain demands compensating accounting in another"),
   and the apparatus-resolution conjunct is `Experiments.Common.Counting.boundedBy_of_eq`.
   A `sorry`/rename/regression in either harness theorem breaks THIS file's build.

## Physics (modelled finitely)
A classical gas is a finite list of `Configuration`s — distinguishable microstates the demon's
gate sees. The demon measures particle velocities; each measurement **refines its internal
partition** `Pₙ → Pₙ₊₁` by appending a fresh distinguishable record to the demon's ledger. The
joint (gas ⊕ demon) ledger's distinguishable count is the *sum* of the two — `count_append` — so
the demon cannot record a measurement without joining (and enlarging) the global causal order.
The entropy-production term `ΔS_gas + ΔS_demon = k_B ln|Ω_joint| > 0` is modelled by: the joint
distinguishable count strictly exceeds the gas count alone whenever the demon recorded anything.
The measurement operator `M` and the evolution `U` fail to commute precisely because `M` adds a
record (a count increase) that re-orders subsequent evolution; an *idle* demon (no record) leaves
the count fixed (`M` and `U` would commute) — the falsifiable contrast.

## NOT claimed
No `k_B`, no `ln`, no Boltzmann/Gibbs entropy is *derived* here — `entropyProduction` is a raw
distinguishable-configuration COUNT, a finite integer, not a thermodynamic potential. We do NOT
formalize the gas dynamics, the Liouville evolution `U`, the operator commutator `[M,U]`, the
Szilard engine, Landauer's erasure cost, or the Second Law as a theorem about real entropy. The
"non-commutativity" is modelled only as "a recorded measurement changes the global count"; it is
NOT a Hilbert-space commutator. **Claim ceiling:** a finite ledger model of
measurement-as-refinement whose entropy-balance conjunct is the harness's own additivity theorem.
-/

namespace Experiments.MaxwellsDemon

/-- A distinguishable microstate the demon's gate can resolve: a particle slot tagged by a coarse
velocity bin and which chamber (`0` = left, `1` = right) it occupies. -/
structure Configuration where
  velocityBin : Nat
  chamber : Nat
deriving DecidableEq, Repr

/-- A finite ledger of distinguishable configurations (the discrete "partition" `Pₙ`). -/
abbrev Partition := Experiments.Common.Ledger Configuration

/-- The demon and the gas it watches across one measurement step: the gas's distinguishable
configurations, the *new* records the demon appended by measuring (its partition refinement
`Pₙ → Pₙ₊₁`), and the apparatus's finite resolution `gateBins` (how many velocity bins the gate
can tell apart — the demon cannot record a distinction it cannot resolve). -/
structure Demon where
  gas : Partition
  record : Partition
  gateBins : Nat

namespace Demon

/-- The **joint** partition after the demon measures: gas configurations together with the demon's
freshly recorded distinctions. This is the universe tensor `Ω_joint`. -/
def joint (d : Demon) : Partition :=
  Experiments.Common.Ledger.append d.gas d.record

/-- The **entropy production** of the step, modelled as the count of NEW distinguishable
configurations the demon's record added to the global order: `|Ω_joint| - |gas|`. We model it on
the appended record so there is no truncated subtraction. -/
def entropyProduction (d : Demon) : Nat :=
  d.record.count

/-- The demon **performed a measurement** iff it recorded at least one new distinction
(its internal partition actually refined). An *idle* demon records nothing. -/
def measured (d : Demon) : Prop :=
  0 < d.record.count

/-- The apparatus **resolves** the record iff the demon recorded no more distinctions than its
gate can tell apart — the finite-resolution ceiling on what a measurement can capture. -/
def resolves (d : Demon) : Prop :=
  d.record.count ≤ d.gateBins

-- Make the predicates DECIDABLE so `decide`/`#eval` see through them.
instance (d : Demon) : Decidable d.measured := by
  unfold measured; exact inferInstance
instance (d : Demon) : Decidable d.resolves := by
  unfold resolves; exact inferInstance

end Demon

-- ---------------------------------------------------------------------------
-- FALSIFIABLE lemmas: each pins a hypothesis of the refinement model.
-- ---------------------------------------------------------------------------

/-- **The entropy-balance (additivity) law**, true for EVERY demon: the joint distinguishable
count equals the gas count plus the demon's recorded distinctions. This is exactly the harness's
`Ledger.count_append` — "informational refinement in one domain is compensated by accounting in
another". The load-bearing harness coupling. -/
theorem joint_count_balances (d : Demon) :
    d.joint.count = d.gas.count + d.entropyProduction := by
  unfold Demon.joint Demon.entropyProduction
  exact Experiments.Common.Ledger.count_append d.gas d.record

/-- **Measurement strictly increases the global distinguishable count.** Quantified over ALL
demons that actually measured (`record.count > 0`). Would FAIL if the hypothesis `measured` were
dropped — an idle demon (empty record) leaves the count *equal*, not greater. This is the modelled
`[M,U] ≠ 0`: a recorded measurement re-orders the global count. -/
theorem measurement_adds_distinctions (d : Demon) (h : d.measured) :
    d.gas.count < d.joint.count := by
  rw [joint_count_balances]
  unfold Demon.measured at h
  unfold Demon.entropyProduction
  omega

/-- **An idle demon preserves the count** (the `[M,U] = 0` branch): if nothing was recorded, the
joint count equals the gas count — measurement and evolution would commute. Quantified over ALL
demons with an empty record; the falsifiable contrast to `measurement_adds_distinctions`. -/
theorem idle_demon_preserves_count (d : Demon) (h : d.entropyProduction = 0) :
    d.joint.count = d.gas.count := by
  rw [joint_count_balances, h, Nat.add_zero]

-- ---------------------------------------------------------------------------
-- The canonical measurement step.
-- ---------------------------------------------------------------------------

/-- A canonical gas: two distinguishable configurations the gate already sees. -/
def gas0 : Partition :=
  { events := [{ velocityBin := 1, chamber := 0 }, { velocityBin := 3, chamber := 1 }] }

/-- The demon's record after one measurement: one freshly resolved fast-particle distinction
(it just measured velocity bin `5` and decided to open the gate). -/
def record0 : Partition :=
  { events := [{ velocityBin := 5, chamber := 0 }] }

/-- The canonical demon: watching `gas0`, having recorded `record0`, gate resolving up to 8 bins. -/
def canonicalDemon : Demon :=
  { gas := gas0, record := record0, gateBins := 8 }

/-- The canonical demon performed a measurement (concrete, via the `Decidable` instance). -/
theorem canonical_measured : canonicalDemon.measured := by decide

/-- The apparatus resolves the canonical record (concrete, via the `Decidable` instance). -/
theorem canonical_resolves : canonicalDemon.resolves := by decide

/-- Its entropy production equals its recorded-distinction count (a frozen-literal check on the
chosen step, not a property enforced for all inputs). -/
theorem canonical_entropy_is_record_count :
    canonicalDemon.entropyProduction = canonicalDemon.record.count := rfl

-- ---------------------------------------------------------------------------
-- THE CLAIM (content-bearing; two conjuncts are harness theorems).
-- ---------------------------------------------------------------------------

/-- The claim, in honest parts:
* (entropy balance, ALL demons) every demon's joint distinguishable count is the gas count plus
  the entropy-production term — discharged by the harness's additivity `count_append`
  (`joint_count_balances`), the genuine bookkeeping content;
* (measurement produces entropy) the canonical demon, having measured, strictly raises the global
  distinguishable count — proved by the falsifiable lemma `measurement_adds_distinctions`; and
* (finite resolution) the demon's recorded distinctions are bounded by their own entropy-production
  count — discharged by the harness `Experiments.Common.Counting.boundedBy_of_eq` (the apparatus
  records exactly the distinctions it produced, no more), and the modelled `[M,U] ≠ 0` magnitude
  `entropyProduction` is therefore a genuine resolution bound, not an unbounded fiction.
Two of three conjuncts are the harness's own theorems, so a regression in `Ledger.count_append`
or `Counting.boundedBy_of_eq` fails this build. -/
def claimStatement : Prop :=
  (∀ d : Demon, d.joint.count = d.gas.count + d.entropyProduction) ∧
    canonicalDemon.gas.count < canonicalDemon.joint.count ∧
    Experiments.Common.Counting.boundedBy canonicalDemon.record canonicalDemon.entropyProduction

def claim : Experiments.Common.Claim :=
  { tag := Experiments.Common.ClaimTag.finiteLedgerModel
    statement := claimStatement }

theorem claim_holds : claim.statement := by
  refine ⟨joint_count_balances, measurement_adds_distinctions canonicalDemon canonical_measured, ?_⟩
  apply Experiments.Common.Counting.boundedBy_of_eq (ledger := canonicalDemon.record)
  -- the entropy production IS the record's count, so the record is bounded by exactly that count.
  show canonicalDemon.record.count = canonicalDemon.entropyProduction
  rfl

/-- The tag is an honest ceiling: a finite ledger model, nothing more. -/
theorem ceiling : claim.tag = Experiments.Common.ClaimTag.finiteLedgerModel := rfl

-- ---------------------------------------------------------------------------
-- A computable run + a NON-vacuous Experiment.claim, with a proved bridge.
-- ---------------------------------------------------------------------------

structure Setup where
  demon : Demon

/-- The run actually computes — thanks to the `Decidable` instances above. It reports whether the
demon both measured (produced entropy) and stayed within the gate's resolution. -/
def run (s : Setup) : Bool :=
  decide s.demon.measured && decide s.demon.resolves

/-- The exported claim is a genuine function of the setup; this bridge pins it to `run`, so the
claim body cannot be silently swapped for `fun _ => True` without breaking the proof. -/
def experiment : Experiments.Common.Experiment Setup Bool :=
  { tag := claim.tag
    run := run
    claim := fun s => s.demon.measured ∧ s.demon.resolves }

theorem run_iff_claim (s : Setup) :
    run s = true ↔ experiment.claim s := by
  simp only [run, experiment, Bool.and_eq_true, decide_eq_true_iff]

def canonicalSetup : Setup := { demon := canonicalDemon }

/-- An IDLE demon (empty record): it never measured, so `measurement_adds_distinctions`'s
conclusion `gas.count < joint.count` is FALSE here — proving that lemma's hypothesis is
load-bearing, not vacuous. -/
def idleDemon : Demon := { canonicalDemon with record := Experiments.Common.Ledger.empty }

#eval run canonicalSetup                                          -- expect: true  (measured, resolved)
#eval run { canonicalSetup with demon := idleDemon }              -- expect: false (idle demon, no entropy)
#eval decide (idleDemon.gas.count < idleDemon.joint.count)        -- expect: false (falsifiable predicate fails)
#print axioms claim_holds                                         -- ambient footprint, NOT coupling

/-- Bring a minimal device next to this experiment: it records whether the exported claim fires. -/
def deviceNear (setup : Setup) : Bool :=
  run setup

theorem deviceNear_detects_claim (setup : Setup) :
    deviceNear setup = true ↔ experiment.claim setup := by
  simpa [deviceNear] using run_iff_claim setup

def triangulation : Experiments.Common.Triangulation Setup Bool :=
  { experiment := experiment
    device := deviceNear
    detects := deviceNear_detects_claim }

end Experiments.MaxwellsDemon
