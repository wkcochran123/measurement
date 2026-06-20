import Experiments.Common

/-!
# Paradoxes of Time Travel — a finite refinement / distinguishability model

Source: `instrument/chapters/06.tex:455` (`phenomenon`, "Paradoxes of Time Travel").

## Physics / metaphysics (modelled finitely)
The description's thesis: apparent time-travel paradoxes are *pathologies of
over-resolution*.  A single causal event `eⱼ` is "extended" by splitting it into a
continuum `{e_{j,α}}_{α∈[0,1]}` of **observationally indistinguishable** refinements.
That destroys (1) local finiteness (uncountably many duplicates) and (2)
distinguishability (Extensionality can no longer pin a unique contribution), so the
universe tensor `U_{n+1}` becomes overcomplete and predicts contradictory outcomes.
The **Axiom of Event Selection** repairs this by restricting any refinement to a
*finite, single-valued* family and selecting **exactly one** representative `e_{j,k*}`
from each locally admissible family.

We model this with a finite `Refinement`: a `decode : Fine -> Coarse` that collapses each
admissible fine family back onto its coarse representative.  The selection axiom is the
statement that pushing a (finite) refined ledger down through `decode` preserves the event
**count** — no overcounting, no Banach-Tarski duplication.  When, by contrast, the same
coarse event is refined into *several* indistinguishable fine duplicates and all of them are
admitted, the pushed-down ledger overcounts: that is the inadmissible (no-go) configuration,
exhibited concretely below.

## NOT claimed
That time travel is (im)possible; anything about real causal structure, relativity, closed
timelike curves, or Godel's rotating-universe metric.  There is **no continuum** here — `[0,1]`
is replaced by a finite slot set, so the genuinely uncountable obstruction is only *gestured
at*, never formalized.  "Indistinguishable" is modelled as "`decode`s to the same coarse
event", not as any real observational equivalence.  **Claim ceiling:** a finite refinement
model whose count-preservation conjunct is the harness's own `Ledger.count_map`.
-/

namespace Experiments.ParadoxesOfTimeTravel

/-- A coarse causal event in the history `E = {e₁, e₂, …}`: just its index. -/
structure CoarseEvent where
  idx : Nat
deriving DecidableEq, Repr

/-- A fine event = a coarse event `e_j` together with a refinement slot `α` drawn from a
**finite** admissible family.  This is the lawful (countable, finite) refinement the Axiom of
Event Selection permits — the continuum `α ∈ [0,1]` is replaced by a finite slot index. -/
structure FineEvent where
  base : CoarseEvent
  slot : Nat
deriving DecidableEq, Repr

/-- THE SELECTION REFINEMENT: every fine refinement `e_{j,α}` decodes back to its single
coarse representative `e_j`.  This is the `decode` map of the Axiom of Event Selection — it
forgets the slot, collapsing each admissible family onto one outcome. -/
def selection : Experiments.Common.Refinement CoarseEvent FineEvent :=
  { decode := fun e => e.base }

/-- A fine family over a coarse event `e`: the `k` admitted refinement slots `0 … k-1`. -/
def family (e : CoarseEvent) (k : Nat) : List FineEvent :=
  (List.range k).map (fun s => { base := e, slot := s })

/-- A single locally admissible family is **single-valued under `decode`**: every element of
`family e k` decodes to the same coarse event `e`.  This is exactly the indistinguishability
the description warns about — and the reason the selection axiom must pick *one*. -/
def singleValued (e : CoarseEvent) (k : Nat) : Prop :=
  ∀ f ∈ family e k, selection.decode f = e

-- ---------------------------------------------------------------------------
-- FALSIFIABLE lemmas (∀-quantified; each breaks if a hypothesis is dropped).
-- ---------------------------------------------------------------------------

/-- The selection map IS single-valued on every admissible family, for ALL coarse events and
ALL finite family sizes.  (Falsifiable: were `decode` to depend on `slot`, this fails.) -/
theorem family_singleValued (e : CoarseEvent) (k : Nat) : singleValued e k := by
  unfold singleValued family selection
  intro f hf
  simp only [List.mem_map, List.mem_range] at hf
  -- hf : ∃ s, s < k ∧ { base := e, slot := s } = f
  match hf with
  | ⟨_, _, heq⟩ => exact heq ▸ rfl

/-- COUNT PRESERVATION under selection (the harness coupling, stated as a ∀-lemma over all
fine ledgers): pushing a refined ledger down through `decode` preserves the event count.
This is the finite analogue of "no overcomplete history" — no Banach–Tarski overcounting.
Quantified over ALL fine ledgers; load-bearing on `Experiments.Common.Ledger.count_map`. -/
theorem pushLedger_preserves_count (ledger : Experiments.Common.Ledger FineEvent) :
    (selection.pushLedger ledger).count = ledger.count := by
  unfold Experiments.Common.Refinement.pushLedger
  exact Experiments.Common.Ledger.count_map selection.decode ledger

/-- A coarse event refined into `k` slots, pushed back down, recovers exactly `k` records —
one per admitted slot, NOT one per representative.  This is the precise sense in which
admitting *every* member of an indistinguishable family **overcounts**: a single coarse event
contributes `k` ledger entries.  (For `k ≥ 2` this is the inadmissible over-resolution.) -/
def overcounts (e : CoarseEvent) (k : Nat) : Prop :=
  (selection.pushLedger { events := family e k }).count = k

/-- The over-refined family really does overcount, for ALL coarse events and ALL sizes. -/
theorem family_overcounts (e : CoarseEvent) (k : Nat) : overcounts e k := by
  unfold overcounts selection Experiments.Common.Refinement.pushLedger
  show ((Experiments.Common.Ledger.map _ { events := family e k }).count) = k
  unfold Experiments.Common.Ledger.map Experiments.Common.Ledger.count family
  simp only [List.map_map, List.length_map, List.length_range]

-- ---------------------------------------------------------------------------
-- The canonical configuration: the event `e₅` over-refined into 3 admitted slots.
-- ---------------------------------------------------------------------------

/-- A representative coarse event. -/
def eJ : CoarseEvent := { idx := 5 }

/-- The over-refined fine ledger: three indistinguishable copies of `e₅`. -/
def overRefined : Experiments.Common.Ledger FineEvent := { events := family eJ 3 }

/-- The admissible (selected) coarse ledger: a SINGLE representative `e₅`. -/
def selected : Experiments.Common.Ledger CoarseEvent := { events := [eJ] }

/-- The crux: the over-refined fine ledger carries 3 records, but the lawfully selected coarse
ledger carries only 1.  The selection axiom (one representative per family) is exactly what
collapses the overcount `3 ↦ 1`. -/
theorem overcount_vs_selected :
    (selection.pushLedger overRefined).count = 3 ∧ selected.count = 1 := by
  refine ⟨?_, ?_⟩
  · exact family_overcounts eJ 3
  · rfl

-- ---------------------------------------------------------------------------
-- THE CLAIM (content-bearing conjunction; count-preservation = harness theorem).
-- ---------------------------------------------------------------------------

/-- The claim, in honest parts:
* (single-valued families) every admitted refinement of `e₅` decodes to `e₅` — the
  indistinguishability that forces a selection;
* (count preservation = NO overcomplete history) pushing the over-refined ledger down through
  `decode` preserves its count — `Experiments.Common.Ledger.count_map` via `pushLedger`;
* (the overcount is real) the over-refined ledger holds 3 records while the lawfully selected
  ledger holds 1 — the finite shadow of the inadmissible over-resolution. -/
def claimStatement : Prop :=
  singleValued eJ 3 ∧
    (selection.pushLedger overRefined).count = overRefined.count ∧
    ((selection.pushLedger overRefined).count = 3 ∧ selected.count = 1)

def claim : Experiments.Common.Claim :=
  { tag := Experiments.Common.ClaimTag.inadmissibilityNoGo
    statement := claimStatement }

theorem claim_holds : claim.statement :=
  ⟨family_singleValued eJ 3,
    pushLedger_preserves_count overRefined,
    overcount_vs_selected⟩

/-- The tag is an honest ceiling: a no-go on over-resolution, exhibited finitely. -/
theorem ceiling : claim.tag = Experiments.Common.ClaimTag.inadmissibilityNoGo := rfl

-- ---------------------------------------------------------------------------
-- A computable run + a non-vacuous Experiment.claim, with a proved bridge.
-- ---------------------------------------------------------------------------

structure Setup where
  base : CoarseEvent
  slots : Nat

/-- The run computes the count overcount factor for a chosen over-refinement. -/
def run (s : Setup) : Nat :=
  (selection.pushLedger { events := family s.base s.slots }).count

/-- The exported claim is a genuine function of the setup (not `fun _ => True`): the pushed
count equals the number of admitted slots.  `run_iff_claim` pins `run` to it. -/
def experiment : Experiments.Common.Experiment Setup Nat :=
  { tag := claim.tag
    run := run
    claim := fun s => (selection.pushLedger { events := family s.base s.slots }).count = s.slots }

theorem run_iff_claim (s : Setup) :
    run s = s.slots ↔ experiment.claim s := by
  unfold run experiment
  exact ⟨fun h => h, fun h => h⟩

def canonicalSetup : Setup := { base := eJ, slots := 3 }

#eval run canonicalSetup                     -- expect: 3  (over-refined: 3 records)
-- Load-bearing check: `singleValued` is FALSE if we (wrongly) demand a refinement decode to a
-- DIFFERENT event.  Evaluate `singleValued` at a mismatched target to print `false`.
#eval decide (∀ f ∈ family eJ 3, selection.decode f = ({ idx := 99 } : CoarseEvent))
                                             -- expect: false (eJ.idx = 5 ≠ 99)
#print axioms claim_holds                    -- [propext, Quot.sound] = AMBIENT, not coupling

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

end Experiments.ParadoxesOfTimeTravel
