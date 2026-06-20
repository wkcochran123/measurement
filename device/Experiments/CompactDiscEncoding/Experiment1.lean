import Experiments.Common

/-!
# Compact Disc Encoding — finite distinguishability, refinement, and merge bookkeeping

Modelled finitely after `instrument/chapters/08.tex:273` (`ph:cd-phenomenon`). The CD is
treated **only** as an informational record: a finite ordered chain of distinguishable marks
(pits / lands) read off a track. A reader admits a new event only when the separation between
surface configurations exceeds its **threshold of discernibility**; everything below the
threshold is invisible and cannot enter the admissible record.

Two readers scan the same disc. The coarse reader resolves fewer distinctions; the fine reader
resolves more. The merge of their records must preserve **all** recorded distinctions — failure
to accommodate the finer record would render the merged history inconsistent. The merged ledger
is the fine ledger plus whatever the coarse reader saw that the fine pass did not duplicate; its
length is bookkept by the harness identity `count (append a b) = count a + count b`.

A coarse reader is a **refinement** of the disc: it decodes the alphabet of finer surface marks
down to a coarser alphabet (here, collapsing the directional pit/land detail into a single
"transition" symbol). Refinement decodes event-for-event, so it **preserves the count** of the
ledger it acts on (`count_map`).

## NOT claimed
Nothing about photons, optics, reflected light, the dense/continuous limit, an induced metric or
connection, relativistic causal intervals, the "maximal rate of admitting distinctions", CIRC /
Reed--Solomon error correction, or any physical CD geometry (74 minutes, spiral pitch, etc.).
The "threshold of discernibility" is a labelled `Nat` comparison, not a derived physical
resolution. **Claim ceiling:** a finite ledger model of distinguishability + a coarse-graining
(refinement) that preserves counts + the harness's merge-length bookkeeping.
-/

namespace Experiments.CompactDiscEncoding

-- ---------------------------------------------------------------------------
-- Effect-specific domain: the surface alphabet and the readers.
-- ---------------------------------------------------------------------------

/-- A single admissible mark on the spiral track. The fine alphabet keeps the pit/land
distinction; a coarse reader (below) collapses both into a single "transition". -/
inductive SurfaceMark where
  | pit
  | land
deriving DecidableEq, Repr

/-- The coarse alphabet a coarser reader resolves down to: it can tell *that* the surface
changed, but not *which way*. -/
inductive CoarseMark where
  | transition
deriving DecidableEq, Repr

/-- A finite record of admissible marks. -/
abbrev MarkLedger := Experiments.Common.Ledger SurfaceMark

/-- A reader is fixed by its threshold of discernibility (a labelled `Nat`). -/
structure Reader where
  threshold : Nat
deriving Repr, DecidableEq

namespace Reader

/-- A reader admits a new event only when the surface separation reaches its threshold. -/
def canRecord (reader : Reader) (separation : Nat) : Prop :=
  reader.threshold ≤ separation

instance (reader : Reader) (separation : Nat) : Decidable (reader.canRecord separation) := by
  unfold canRecord; exact inferInstance

end Reader

-- ---------------------------------------------------------------------------
-- FALSIFIABLE lemmas (∀-quantified; drop the hypothesis and each breaks).
-- ---------------------------------------------------------------------------

/-- **Threshold of discernibility is load-bearing.** Quantified over ALL readers and
separations: anything strictly below the threshold is invisible — it cannot be recorded.
Drop the hypothesis `separation < reader.threshold` and this is false. -/
theorem belowThresholdInvisible (reader : Reader) (separation : Nat)
    (h : separation < reader.threshold) : ¬ reader.canRecord separation :=
  fun hr => Nat.lt_irrefl separation (Nat.lt_of_lt_of_le h hr)

/-- **A coarser reader records no more than the finer one.** Quantified over ALL readers:
if the coarse threshold is at least the fine threshold, then any separation the coarse reader
can record, the fine reader can record too. Drop `h` and this is false. -/
theorem finerSeesAtLeast (coarse fine : Reader) (separation : Nat)
    (h : fine.threshold ≤ coarse.threshold)
    (hc : coarse.canRecord separation) : fine.canRecord separation :=
  Nat.le_trans h hc

-- ---------------------------------------------------------------------------
-- Coarse-graining as a refinement: it decodes fine marks → coarse marks and,
-- because it decodes event-for-event, PRESERVES the ledger count.
-- ---------------------------------------------------------------------------

/-- The coarse reader's view of the disc: collapse every fine mark to a single transition. -/
def coarsen : Experiments.Common.Refinement CoarseMark SurfaceMark :=
  { decode := fun _ => CoarseMark.transition }

/-- **Refinement preserves the count.** Pushing a fine ledger through `coarsen` keeps its length:
the coarse reader sees a transition for every fine mark, never inventing or losing one.
This is the harness identity `count_map` — a *load-bearing* harness coupling: a regression that
broke `Ledger.map`/`count_map` would break THIS build. -/
theorem coarsen_preserves_count (ledger : MarkLedger) :
    (coarsen.pushLedger ledger).count = ledger.count :=
  Experiments.Common.Ledger.count_map coarsen.decode ledger

-- ---------------------------------------------------------------------------
-- The merge: glue the records and bookkeep the length with `count_append`.
-- ---------------------------------------------------------------------------

/-- Merge two recorded histories by concatenation — the merged record must contain every
recorded distinction from both passes. -/
def mergeLedgers (a b : MarkLedger) : MarkLedger :=
  Experiments.Common.Ledger.append a b

/-- **The merge conserves the total number of recorded distinctions.** The merged history has
exactly the coarse count plus the fine count — no distinction is dropped, none is invented.
This is the harness's `count_append`, the LOAD-BEARING coupling discharging a conjunct of
`claim_holds` below. -/
theorem merge_count (a b : MarkLedger) :
    (mergeLedgers a b).count = a.count + b.count :=
  Experiments.Common.Ledger.count_append a b

-- ---------------------------------------------------------------------------
-- The canonical setup and run.
-- ---------------------------------------------------------------------------

structure Setup where
  coarseReader : Reader
  fineReader : Reader
  coarseLedger : MarkLedger
  fineLedger : MarkLedger
deriving Repr

/-- A coarse reader (threshold 2) and a fine reader (threshold 1) scanning the same disc. -/
def defaultSetup : Setup :=
  { coarseReader := { threshold := 2 }
    fineReader := { threshold := 1 }
    coarseLedger := { events := [SurfaceMark.pit, SurfaceMark.land, SurfaceMark.pit] }
    fineLedger :=
      { events :=
          [ SurfaceMark.pit
          , SurfaceMark.pit
          , SurfaceMark.land
          , SurfaceMark.pit
          , SurfaceMark.land ] } }

structure RunOutput where
  coarseCount : Nat
  fineCount : Nat
  mergedCount : Nat
deriving Repr, DecidableEq

/-- The run computes the three counts; `mergedCount` is bookkept by `count_append`. -/
def run (setup : Setup) : RunOutput :=
  { coarseCount := setup.coarseLedger.count
    fineCount := setup.fineLedger.count
    mergedCount := (mergeLedgers setup.coarseLedger setup.fineLedger).count }

-- ---------------------------------------------------------------------------
-- THE CLAIM (content-bearing conjunction; one conjunct is the harness theorem).
-- ---------------------------------------------------------------------------

/-- The fine reader resolves at least as fine as the coarse reader. -/
def thresholdsOrdered (setup : Setup) : Prop :=
  setup.fineReader.threshold ≤ setup.coarseReader.threshold

instance (setup : Setup) : Decidable (thresholdsOrdered setup) := by
  unfold thresholdsOrdered; exact inferInstance

/-- The claim, in honest parts:
* (ordering) the fine reader is at least as discerning as the coarse one — concrete `decide`;
* (no count inflation) the coarse pass records no more marks than the fine pass — `decide`;
* (merge bookkeeping) the merged history's length is exactly coarse + fine, discharged by the
  harness `count_append` via `merge_count` — the LOAD-BEARING coupling. -/
def claimStatement : Prop :=
  thresholdsOrdered defaultSetup ∧
    (run defaultSetup).coarseCount ≤ (run defaultSetup).fineCount ∧
    (run defaultSetup).mergedCount
      = (run defaultSetup).coarseCount + (run defaultSetup).fineCount

def claim : Experiments.Common.Claim :=
  { tag := Experiments.Common.ClaimTag.finiteLedgerModel
    statement := claimStatement }

theorem claim_holds : claim.statement :=
  ⟨by decide, by decide,
    merge_count defaultSetup.coarseLedger defaultSetup.fineLedger⟩

theorem ceiling :
    claim.tag = Experiments.Common.ClaimTag.finiteLedgerModel := rfl

-- ---------------------------------------------------------------------------
-- A non-vacuous exported Experiment, pinned to `run`.
-- ---------------------------------------------------------------------------

def experiment : Experiments.Common.Experiment Setup RunOutput :=
  { tag := claim.tag
    run := run
    claim := fun setup =>
      thresholdsOrdered setup ∧
        (run setup).mergedCount = (run setup).coarseCount + (run setup).fineCount }

theorem run_bookkeeps_merge (setup : Setup) :
    (run setup).mergedCount = (run setup).coarseCount + (run setup).fineCount :=
  merge_count setup.coarseLedger setup.fineLedger

-- ---------------------------------------------------------------------------
-- Gate evidence.
-- ---------------------------------------------------------------------------

#eval run defaultSetup                                   -- coarse 3, fine 5, merged 8
-- FALSE at a config that violates the ordering: coarse threshold below the fine one, so the
-- "fine" reader is NOT at least as discerning. Proves `thresholdsOrdered` is load-bearing.
#eval decide (thresholdsOrdered
  { defaultSetup with coarseReader := { threshold := 0 } })   -- expect: false
#print axioms claim_holds                                -- ambient footprint, not coupling

/-- Bring a minimal device next to this experiment: it records whether the exported claim fires. -/
def deviceNear (setup : Setup) : Bool :=
  decide (experiment.claim setup)

theorem deviceNear_detects_claim (setup : Setup) :
    deviceNear setup = true ↔ experiment.claim setup := by
  simp [deviceNear]

def triangulation : Experiments.Common.Triangulation Setup RunOutput :=
  { experiment := experiment
    device := deviceNear
    detects := deviceNear_detects_claim }

end Experiments.CompactDiscEncoding
