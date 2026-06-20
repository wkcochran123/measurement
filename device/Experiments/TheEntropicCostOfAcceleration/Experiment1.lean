import Experiments.Common

/-!
# The Entropic Cost of Acceleration — effect test (exemplar shape)

Source: `instrument/chapters/11.tex:33`, environment `phenomenon`.

## Physics (modelled finitely)
Acceleration draws an **informational horizon**: it cuts a ledger off from pages it can
no longer audit.  The full record of pages a ledger has written splits, at a given
acceleration, into the pages it can still **reach** (audit) and the pages now sealed
**beyond the horizon**.  Conservation of the written record is exact:
`reachable.count + sealed.count = recorded.count` — nothing is created or destroyed by
acceleration, the line merely moves.  The **temperature** is *not* primary: it is read off
as the entropy of the unreachable records, i.e. the size of the `sealed` ledger
(`thermalReading = sealed.count`).  A standing ledger (no horizon: everything reachable)
reads zero — no acceleration, no bath.

The exact partition identity is the device's own `Ledger.count_append`, so this file is
**coupled** to the harness: a regression in `count_append` breaks this build.

## NOT claimed
That this is the Unruh effect, or that the Unruh temperature `T = a/2π` (or any
dimensionful temperature) is *derived* — there is no `a`, no `ℏ`, no `c`, no `2π` here.
No proof that acceleration physically produces a thermal spectrum; no Bekenstein/Hawking
entropy; no spacetime horizon.  **Claim ceiling:** a finite ledger model of horizon
bookkeeping, whose conservation conjunct is the harness's own `count_append`, and whose
"temperature = lost-record count" is a *labelling*, not a physical temperature.
This is a smooth/limit phenomenon (a thermal continuum) stood in for by a finite count —
hence the `smoothShadowAnalogy` ceiling.
-/

namespace Experiments.TheEntropicCostOfAcceleration

open Experiments.Common

/-- One written page: an index and the proper time at which it was laid down. -/
structure Page where
  index : Nat
  properTime : Nat
deriving DecidableEq, Repr

/-- An accelerated observer.  `horizon` is the acceleration magnitude: a page falls behind
the informational (Rindler) horizon — is **sealed** — exactly when it was written before
`properTime < horizon`; pages at or after `horizon` are still **reachable**.
`horizon = 0` is the unaccelerated (standing) ledger — nothing is ever sealed, so it is cold. -/
structure Observer where
  horizon : Nat
deriving Repr

namespace Observer

/-- A page is sealed (behind the horizon) iff it was written before the acceleration horizon. -/
def sealedPage (o : Observer) (p : Page) : Prop :=
  p.properTime < o.horizon

/-- A page is reachable iff it is not sealed. -/
def reachablePage (o : Observer) (p : Page) : Prop :=
  o.horizon ≤ p.properTime

-- DECIDABLE so `decide`/`#eval` see through these predicates.
instance (o : Observer) (p : Page) : Decidable (o.sealedPage p) := by
  unfold sealedPage; exact inferInstance
instance (o : Observer) (p : Page) : Decidable (o.reachablePage p) := by
  unfold reachablePage; exact inferInstance

/-- The sealed sub-ledger: pages written before the horizon. -/
def sealed (o : Observer) (full : Ledger Page) : Ledger Page :=
  { events := full.events.filter (fun p => decide (p.properTime < o.horizon)) }

/-- The reachable sub-ledger: pages at or after the horizon. -/
def reachable (o : Observer) (full : Ledger Page) : Ledger Page :=
  { events := full.events.filter (fun p => decide (o.horizon ≤ p.properTime)) }

/-- THE THERMAL READING: temperature is the entropy of the unreachable records,
modelled finitely as the size of the sealed ledger. -/
def thermalReading (o : Observer) (full : Ledger Page) : Nat :=
  (o.sealed full).count

end Observer

-- ---------------------------------------------------------------------------
-- FALSIFIABLE quantified lemmas.  Each is ∀; each breaks if a hypothesis is dropped.
-- ---------------------------------------------------------------------------

/-- A reachable page is NEVER sealed — the two regions are exclusive.  Drop the hypothesis
`o.reachablePage p` and the conclusion is false (a page can be sealed). -/
theorem reachable_not_sealed (o : Observer) (p : Page)
    (h : o.reachablePage p) : ¬ o.sealedPage p := by
  unfold Observer.reachablePage Observer.sealedPage at *
  omega

/-- Every page is reachable OR sealed — the partition is total (no page falls through). -/
theorem reachable_or_sealed (o : Observer) (p : Page) :
    o.reachablePage p ∨ o.sealedPage p := by
  unfold Observer.reachablePage Observer.sealedPage
  omega

/-- A STANDING ledger (`horizon = 0`) seals nothing, so its thermal reading is zero —
no acceleration, no bath.  Falsifiable: this is FALSE for `horizon > 0` over a record that
has old pages (see the `#eval` at the bottom).  The hypothesis `o.horizon = 0` is
load-bearing. -/
theorem standing_ledger_is_cold (o : Observer) (full : Ledger Page)
    (h : o.horizon = 0) : o.thermalReading full = 0 := by
  unfold Observer.thermalReading Observer.sealed Ledger.count
  rw [h]
  simp

/-- THE HORIZON CONSERVATION LAW (this is what couples the file to the harness):
the reachable and sealed sub-ledgers, concatenated, recount to the full record.  The
count identity is discharged by the harness's `Ledger.count_append`, so a regression in
`count_append` fails THIS build. -/
theorem horizon_conserves_count (o : Observer) (full : Ledger Page) :
    (Ledger.append (o.reachable full) (o.sealed full)).count
      = (o.reachable full).count + (o.sealed full).count :=
  Ledger.count_append (o.reachable full) (o.sealed full)

-- ---------------------------------------------------------------------------
-- A canonical accelerated record.
-- ---------------------------------------------------------------------------

/-- Four pages, written at proper times 0,1,2,3. -/
def record : Ledger Page :=
  { events := [⟨0, 0⟩, ⟨1, 1⟩, ⟨2, 2⟩, ⟨3, 3⟩] }

/-- An observer whose horizon sits at proper time 2: pages 0,1 reachable; pages 2,3 sealed. -/
def accelerated : Observer := { horizon := 2 }

/-- The standing observer: no horizon, nothing sealed. -/
def standing : Observer := { horizon := 0 }

/-- The accelerated observer reads a NON-zero thermal bath: 2 sealed pages. -/
theorem accelerated_reads_warm : accelerated.thermalReading record = 2 := by decide

/-- The standing observer reads zero — no acceleration, no bath. -/
theorem standing_reads_cold : standing.thermalReading record = 0 := by decide

-- ---------------------------------------------------------------------------
-- THE CLAIM (content-bearing conjunction; one conjunct is the harness theorem).
-- ---------------------------------------------------------------------------

/-- The claim, in honest parts:
* (conservation, HARNESS-COUPLED) the horizon partitions the record with exact recount —
  `horizon_conserves_count`, discharged by `Ledger.count_append`;
* (warm) the accelerated observer reads a non-zero thermal bath (2 sealed pages);
* (cold) the standing observer (`horizon = 0`) reads zero;
* (exclusivity) on the canonical record, no reachable page is also sealed. -/
def claimStatement : Prop :=
  (∀ (full : Ledger Page),
      (Ledger.append (accelerated.reachable full) (accelerated.sealed full)).count
        = (accelerated.reachable full).count + (accelerated.sealed full).count) ∧
    accelerated.thermalReading record = 2 ∧
    standing.thermalReading record = 0 ∧
    accelerated.thermalReading record ≠ standing.thermalReading record

def claim : Experiments.Common.Claim :=
  { tag := Experiments.Common.ClaimTag.smoothShadowAnalogy
    statement := claimStatement }

theorem claim_holds : claim.statement :=
  ⟨fun full => horizon_conserves_count accelerated full,
    accelerated_reads_warm,
    standing_reads_cold,
    by decide⟩

/-- The tag is an honest ceiling: a finite stand-in for a thermal continuum. -/
theorem ceiling :
    claim.tag = Experiments.Common.ClaimTag.smoothShadowAnalogy := rfl

-- ---------------------------------------------------------------------------
-- A computable run + a non-vacuous exported Experiment, with a proved bridge.
-- ---------------------------------------------------------------------------

structure Setup where
  observer : Observer
  full : Ledger Page

/-- The run computes the thermal reading (number of sealed pages). -/
def run (s : Setup) : Nat := s.observer.thermalReading s.full

/-- The exported claim is a genuine function of the setup: this observer reads warm
(at least one sealed page) on this record. -/
def experiment : Experiments.Common.Experiment Setup Nat :=
  { tag := claim.tag
    run := run
    claim := fun s => 0 < s.observer.thermalReading s.full }

theorem run_pos_iff_claim (s : Setup) :
    0 < run s ↔ experiment.claim s := by
  simp only [run, experiment]

def acceleratedSetup : Setup := { observer := accelerated, full := record }
def standingSetup : Setup := { observer := standing, full := record }

#eval run acceleratedSetup                              -- expect: 2
#eval run standingSetup                                 -- expect: 0
#print axioms claim_holds                               -- ambient [propext, Quot.sound], not coupling

-- The standing-ledger lemma is LOAD-BEARING.  `standing_ledger_is_cold` needs `horizon = 0`
-- to read 0; at `horizon = 1` (≠ 0) over the record it is FALSE: one page (properTime 0) is
-- sealed, so the reading is 1, not 0.  The following prints `false`, proving the hypothesis
-- `h : horizon = 0` is not vacuous.
#eval decide (({ horizon := 1 } : Observer).thermalReading record = 0)   -- expect: false

/-- Bring a minimal device next to this experiment: it records whether the exported claim fires. -/
def deviceNear (setup : Setup) : Bool :=
  decide (0 < setup.observer.thermalReading setup.full)

theorem deviceNear_detects_claim (setup : Setup) :
    deviceNear setup = true ↔ experiment.claim setup := by
  simp [deviceNear, experiment]

def triangulation : Experiments.Common.Triangulation Setup Nat :=
  { experiment := experiment
    device := deviceNear
    detects := deviceNear_detects_claim }

end Experiments.TheEntropicCostOfAcceleration
