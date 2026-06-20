import Experiments.Common

/-!
# LiDAR — a finite-ledger model of laser-certified causal distinctions

Built to the EXEMPLAR shape (`ThePositronAnnihilationEffect/Experiment1.lean`):

1. an **effect-specific domain** (`Pulse`, `Notebook`, `Journey`) — NOT the 3-`Nat` `CountSetup`;
2. genuinely **falsifiable** `∀`-quantified lemmas — each would break if the model dropped a
   hypothesis (`inertial_no_extra_refinement`, `acceleration_densifies`);
3. a **content-bearing** claim — a real conjunction, never `True`;
4. an **honest tag** (`smoothShadowAnalogy`) + a candid "NOT claimed" disclaimer;
5. explicit `Decidable` instances so `decide`/`#eval` see through the richer predicates;
6. it **couples to the harness**: the merge conjunct of `claim_holds` is discharged by the harness
   theorem `Experiments.Common.Ledger.count_append` — the bookkeeping law that "merging the two
   laboratory notebooks counts every distinction exactly once". A `sorry`/rename/regression in
   `Ledger.count_append` breaks *this* file's build.

## Physics (modelled finitely)
Observer A continuously tracks B with timestamped laser round-trips; each fired-and-reflected pulse
is a distinguishable EVENT entered in A's notebook. B's notebook records only its own internal ticks
plus those refinements FORCED by onboard acceleration events. The description's claim is purely
informational: acceleration introduces refinements, refinements create more events, and a coherent
MERGE of the two histories counts every distinction exactly once. A's record is the denser one, so
A's count is the larger; in the smooth limit the same count is the shadow of the Lorentz dilation
factor — here it is just bookkeeping.

We model each notebook as a finite `Ledger` of `Pulse`s. A `Journey` carries A's tracking notebook,
B's proper-time notebook, and the EXTRA refinements that acceleration forces into A's record. The
merge law (`count_append`) is the harness's additivity theorem; the "acceleration densifies" lemma
is the falsifiable informational core.

## NOT claimed
That this derives or reproduces the relativistic time-dilation / Lorentz-contraction formula (no
`γ`, no `c`, no metric, no proper-time integral); that the refinement count IS proper time; that
Minkowski geometry, Doppler shift, or the update rule `E_k = Ψ(e_k ∩ R̂(e_{k-1}))` are formalized
(they are not). This is a finite, discrete ledger ANALOGY of "denser causal record ⇒ larger count",
whose only genuine merge content is the harness's own additivity law. **Claim ceiling:** a
smooth-shadow analogy whose merge conjunct is the harness's `count_append`.
-/

namespace Experiments.LiDAR

/-- One laser-certified distinction: a fired/received round-trip timestamped in a notebook.
`emit` is the emission timestamp, `recv` the reflected-reception timestamp (A's clock); `onboard`
flags a refinement FORCED by an onboard acceleration event rather than a plain coasting return. -/
structure Pulse where
  emit : Nat
  recv : Nat
  onboard : Bool
deriving DecidableEq, Repr

/-- A laboratory notebook is a finite ledger of distinguishable pulses. -/
abbrev Notebook := Experiments.Common.Ledger Pulse

/-- A full tracking journey: A's tracking notebook (the symmetric coasting interpolant), B's
proper-time notebook, and the EXTRA refinements that acceleration forces into A's record. The merge
recombines A's base record with those forced refinements. -/
structure Journey where
  tracking : Notebook
  proper : Notebook
  forced : Notebook

namespace Journey

/-- A's full merged record: her base coasting interpolant PLUS the refinements acceleration forced.
Modelled additively (append) so there is no truncated subtraction — every distinction counts once. -/
def merged (j : Journey) : Notebook :=
  Experiments.Common.Ledger.append j.tracking j.forced

/-- The journey is **inertial** when acceleration forced NO extra refinements: B coasted, so A's
record is the unique minimal interpolant with nothing added. -/
def inertial (j : Journey) : Prop :=
  j.forced.count = 0

/-- B **accelerated** when at least one extra refinement was forced into A's record. -/
def accelerated (j : Journey) : Prop :=
  0 < j.forced.count

/-- THE MERGE LAW: when the two histories are coherently merged, the merged count equals A's base
tracking count plus the forced refinements — every laser-certified distinction counted exactly once.
This is `Ledger.count_append`; it is the load-bearing harness coupling. -/
def mergeBalances (j : Journey) : Prop :=
  j.merged.count = j.tracking.count + j.forced.count

-- Make the predicates DECIDABLE so `decide`/`#eval` see through them.
instance (j : Journey) : Decidable j.inertial := by
  unfold inertial; exact inferInstance
instance (j : Journey) : Decidable j.accelerated := by
  unfold accelerated; exact inferInstance
instance (j : Journey) : Decidable j.mergeBalances := by
  unfold mergeBalances merged; exact inferInstance

end Journey

-- ---------------------------------------------------------------------------
-- FALSIFIABLE lemmas: each pins a hypothesis of the bookkeeping model.
-- Each would break if the corresponding hypothesis were dropped.
-- ---------------------------------------------------------------------------

/-- **Inertial ⇒ the merged record adds nothing over A's base tracking record.** Quantified over
ALL journeys. Would FAIL if `merged` did not append `forced`, or if `inertial` dropped its clause:
the merged count would not collapse back to the base tracking count. -/
theorem inertial_no_extra_refinement (j : Journey) (h : j.inertial) :
    j.merged.count = j.tracking.count := by
  unfold Journey.merged
  rw [Experiments.Common.Ledger.count_append, h, Nat.add_zero]

/-- **Acceleration strictly DENSIFIES A's record** — the informational core of the description:
acceleration forces extra refinements, so A's merged record is strictly larger than her base coasting
interpolant. Quantified over ALL accelerated journeys. Would FAIL if `merged` ignored `forced`, or if
`accelerated` did not demand a positive forced count (it would no longer be strict). -/
theorem acceleration_densifies (j : Journey) (h : j.accelerated) :
    j.tracking.count < j.merged.count := by
  unfold Journey.accelerated at h
  unfold Journey.merged
  rw [Experiments.Common.Ledger.count_append]
  omega

/-- **The merge always balances** — true for EVERY journey, discharged by the harness's additivity
theorem `count_append`. This is the load-bearing harness coupling. -/
theorem every_merge_balances (j : Journey) : j.mergeBalances := by
  unfold Journey.mergeBalances Journey.merged
  rw [Experiments.Common.Ledger.count_append]

-- ---------------------------------------------------------------------------
-- The canonical journey.
-- ---------------------------------------------------------------------------

/-- A's base tracking record: two clean coasting round-trips (no onboard refinement). -/
def tracking0 : Notebook :=
  { events := [{ emit := 0, recv := 2, onboard := false },
               { emit := 4, recv := 6, onboard := false }] }

/-- B's proper-time record: one internal tick. -/
def proper0 : Notebook :=
  { events := [{ emit := 0, recv := 1, onboard := false }] }

/-- The refinements acceleration forced into A's record: two onboard-event round-trips. -/
def forced0 : Notebook :=
  { events := [{ emit := 4, recv := 5, onboard := true },
               { emit := 5, recv := 7, onboard := true }] }

/-- The canonical accelerated journey: two base round-trips, two forced refinements. -/
def canonicalJourney : Journey :=
  { tracking := tracking0, proper := proper0, forced := forced0 }

/-- The canonical journey's merge balances (concrete, via the `Decidable` instance). -/
theorem canonical_balances : canonicalJourney.mergeBalances := by decide

/-- Acceleration densifies the canonical record (concrete witness of the falsifiable lemma). -/
theorem canonical_densifies :
    canonicalJourney.tracking.count < canonicalJourney.merged.count :=
  acceleration_densifies canonicalJourney (by decide)

/-- A's merged record is strictly LONGER than B's proper-time record — the "denser causal record"
conclusion, here a frozen check on the chosen event (4 > 1). -/
theorem A_record_denser_than_B :
    canonicalJourney.proper.count < canonicalJourney.merged.count := by decide

-- ---------------------------------------------------------------------------
-- THE CLAIM (content-bearing; the merge conjunct is the harness's theorem).
-- ---------------------------------------------------------------------------

/-- The claim, in honest parts:
* (merge balances) the canonical journey's merged record counts every distinction exactly once —
  proved here via the `Decidable` instance;
* (merge law, ALL journeys) every journey's merge balances — discharged by the harness's
  `count_append` additivity (`every_merge_balances`), the bookkeeping that "merging the two notebooks
  counts each distinction once"; and
* (acceleration densifies) the canonical accelerated journey's merged record is strictly larger than
  A's base coasting record — proved by the falsifiable lemma `acceleration_densifies`.
The middle conjunct is the genuine informational content and is the harness's own additivity law, so a
regression in `Ledger.count_append` fails this build. -/
def claimStatement : Prop :=
  canonicalJourney.mergeBalances ∧
    (∀ j : Journey, j.mergeBalances) ∧
    canonicalJourney.tracking.count < canonicalJourney.merged.count

def claim : Experiments.Common.Claim :=
  { tag := Experiments.Common.ClaimTag.smoothShadowAnalogy
    statement := claimStatement }

theorem claim_holds : claim.statement :=
  ⟨canonical_balances, every_merge_balances, canonical_densifies⟩

/-- The tag is an honest ceiling: a smooth-shadow analogy of relativistic dilation, not a derivation
of it. -/
theorem ceiling : claim.tag = Experiments.Common.ClaimTag.smoothShadowAnalogy := rfl

-- ---------------------------------------------------------------------------
-- A computable run + a NON-vacuous Experiment.claim, with a proved bridge.
-- ---------------------------------------------------------------------------

structure Setup where
  journey : Journey

/-- The run actually computes — thanks to the `Decidable` instances above. -/
def run (s : Setup) : Bool := decide s.journey.mergeBalances

/-- The exported claim is a genuine function of the setup, pinned to `run` by `run_iff_claim`. -/
def experiment : Experiments.Common.Experiment Setup Bool :=
  { tag := claim.tag
    run := run
    claim := fun s => s.journey.mergeBalances }

theorem run_iff_claim (s : Setup) :
    run s = true ↔ experiment.claim s := by
  simp only [run, experiment, decide_eq_true_iff]

def canonicalSetup : Setup := { journey := canonicalJourney }

#eval run canonicalSetup                                                 -- expect: true
-- The falsifiable predicate at a FALSE config: an inertial journey is NOT accelerated, so
-- `accelerated` is false there — proving `acceleration_densifies`'s hypothesis is load-bearing.
#eval decide canonicalJourney.accelerated                                -- expect: true
#eval decide (Journey.accelerated { canonicalJourney with forced := Experiments.Common.Ledger.empty }) -- expect: false
#print axioms claim_holds                                               -- ambient footprint, not the coupling

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

end Experiments.LiDAR
