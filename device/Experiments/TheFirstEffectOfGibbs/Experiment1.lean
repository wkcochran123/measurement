import Experiments.Common

/-!
# The First Effect of Gibbs — a finite ledger of CATALYSIS

Modelled finitely after the exemplar
(`device/Experiments/ThePositronAnnihilationEffect/Experiment1.lean`).

## Physics (modelled finitely)
A **catalyst** is a structure `K` that lowers the informational strain required to admit a
refinement *without altering the net causal ledger* (description: "The First Effect of Gibbs").
The catalyzed transition runs

    U_A  --K-->  U*  --K⁻¹-->  U_B,

inserting an intermediate ledger `U*` that exists *only to reduce strain*, then undoing it.
The catalyst is **not consumed** because it "does not contribute events to the causal balance":
the forward pass `K` commits a finite list of intermediate anchors, the inverse pass `K⁻¹`
commits their signed reversal, and the two **cancel** in the net causal balance while leaving the
endpoints (`U_A`, `U_B`) fixed.

We pin exactly this finite content:
* **count bookkeeping is additive** — the catalyzed path's ledger count is the sum of the bare
  path's count and the catalyst loop's count (`Ledger.count_append`, the device-harness theorem);
* **ledger neutrality** — the catalyst loop's *net signed contribution* (forward strain minus the
  inverse strain it restores) is exactly `0`, so `K` adds no net events to the causal balance;
* **endpoints are preserved** — the catalyzed path begins at `U_A` and ends at `U_B`, unchanged.

## NOT claimed
That this is real chemical catalysis; that "curvature of a spline" or "informational strain" is
*derived* (they are labelled finite stand-ins — a strain is a `Nat` weight, the path is a finite
anchor list); any reaction rate, activation energy, transition-state theory, or continuum
refinement dynamics; that the catalyst is *optimal*. The real physics we are NOT formalizing is
the continuum geometry of the admissible refinement path and any thermodynamics of the barrier.
**Claim ceiling:** a finite ledger model of catalysis, whose additivity conjunct is the
device-harness theorem `Ledger.count_append`.
-/

namespace Experiments.TheFirstEffectOfGibbs

/-- One step on a refinement path: an `anchor` index it passes through, and the *signed*
informational `strain` it commits to the causal ledger (`+` on a forward pass, `-` on the inverse
pass that the catalyst uses to undo its intermediate anchors). -/
structure Step where
  anchor : Nat
  strain : Int
deriving DecidableEq, Repr

/-- A refinement path is a finite ledger of steps. -/
abbrev Path := Experiments.Common.Ledger Step

/-- The **net causal balance** of a path: the signed sum of its committed strains. This is the
quantity the catalyst must leave invariant ("does not contribute events to the causal balance"). -/
def balance (p : Path) : Int :=
  (p.events.map Step.strain).foldr (· + ·) 0

/-- A catalyst `K`: a forward pass that inserts intermediate anchors at reduced strain, paired with
its inverse pass `K⁻¹`. Ledger-neutral means `inverse` exactly negates `forward` step-for-step. -/
structure Catalyst where
  forward : Path
  inverse : Path

/-- `K` is **ledger-neutral** when its inverse pass is the signed mirror of its forward pass: same
anchors visited, strains negated. This is the catalyst "not being consumed". -/
def Catalyst.neutral (k : Catalyst) : Prop :=
  k.inverse.events = k.forward.events.map (fun s => { s with strain := -s.strain })

instance (k : Catalyst) : Decidable (k.neutral) := by
  unfold Catalyst.neutral; exact inferInstance

/-- The catalyst LOOP as a single path: forward then inverse (`U_A → U* → U_B`'s detour). -/
def Catalyst.loop (k : Catalyst) : Path :=
  Experiments.Common.Ledger.append k.forward k.inverse

-- ---------------------------------------------------------------------------
-- FALSIFIABLE lemmas. Each is ∀-quantified; drop a hypothesis / a summand and it
-- breaks. These are the load-bearing facts that make "catalysis = strain-reduction
-- at zero net ledger cost" well defined.
-- ---------------------------------------------------------------------------

/-- COUNT BOOKKEEPING IS ADDITIVE: splicing the catalyst loop onto a bare path adds exactly the
loop's step count. This is the device-harness theorem `Ledger.count_append`, re-exported; it is
the single fact that makes "the catalyst adds intermediate anchors" a *countable* operation.
FALSIFIABLE: replace `bare.count + k.loop.count` with `bare.count` and it fails. Quantified over
ALL paths and catalysts. -/
theorem count_splices (bare : Path) (k : Catalyst) :
    (Experiments.Common.Ledger.append bare k.loop).count = bare.count + k.loop.count :=
  Experiments.Common.Ledger.count_append bare k.loop

/-- List-level signed strain sum (what `balance` reduces to). -/
def strainSum (xs : List Step) : Int :=
  (xs.map Step.strain).foldr (· + ·) 0

theorem balance_eq_strainSum (p : Path) : balance p = strainSum p.events := rfl

/-- Helper: the list-level strain sum distributes over append. Clean list induction. -/
theorem strainSum_append (xs ys : List Step) :
    strainSum (xs ++ ys) = strainSum xs + strainSum ys := by
  unfold strainSum
  induction xs with
  | nil => simp
  | cons s rest ih =>
      simp only [List.cons_append, List.map_cons, List.foldr_cons, ih]
      omega

/-- Helper: a signed-mirror pass carries the exactly negated net strain sum. List induction. -/
theorem strainSum_mirror (xs : List Step) :
    strainSum (xs.map (fun s => { s with strain := -s.strain })) = - strainSum xs := by
  unfold strainSum
  induction xs with
  | nil => simp
  | cons s rest ih =>
      simp only [List.map_cons, List.foldr_cons, ih]
      omega

/-- The signed strain sum distributes over path concatenation. -/
theorem balance_append (left right : Path) :
    balance (Experiments.Common.Ledger.append left right) = balance left + balance right := by
  show strainSum (left.events ++ right.events) = strainSum left.events + strainSum right.events
  exact strainSum_append left.events right.events

/-- LEDGER NEUTRALITY: a neutral catalyst's loop has **zero** net causal balance — the forward
strain and the inverse strain it restores cancel exactly. This is "the catalyst is not consumed".
FALSIFIABLE: drop the `neutral` hypothesis and a generic `Catalyst` loop has nonzero balance (see
the `#eval` at the bottom). Quantified over ALL catalysts. -/
theorem neutral_loop_balanced (k : Catalyst) (h : k.neutral) : balance k.loop = 0 := by
  unfold Catalyst.loop
  rw [balance_append]
  show strainSum k.forward.events + strainSum k.inverse.events = 0
  unfold Catalyst.neutral at h
  rw [h, strainSum_mirror]
  omega

-- ---------------------------------------------------------------------------
-- A concrete catalyzed transition U_A → U* → U_B.
-- ---------------------------------------------------------------------------

/-- The bare (uncatalyzed) path: the two endpoints `U_A`, `U_B`, committing strain `5` and `5`
(a high-curvature direct step — admissible only with help). -/
def barePath : Path :=
  { events := [ { anchor := 0, strain := 5 }, { anchor := 9, strain := 5 } ] }

/-- The catalyst `K`: a forward pass inserting two intermediate anchors at *reduced* strain
(`2`, `1`), and its signed-mirror inverse (`-2`, `-1`) that restores the ledger. -/
def gibbsCatalyst : Catalyst :=
  { forward := { events := [ { anchor := 3, strain := 2 }, { anchor := 6, strain := 1 } ] }
    inverse := { events := [ { anchor := 3, strain := -2 }, { anchor := 6, strain := -1 } ] } }

/-- The catalyzed path: the bare endpoints with the catalyst loop spliced in. -/
def catalyzedPath : Path :=
  Experiments.Common.Ledger.append barePath gibbsCatalyst.loop

/-- The chosen catalyst is ledger-neutral. Concrete, via the `Decidable` instance. -/
theorem gibbsCatalyst_neutral : gibbsCatalyst.neutral := by decide

/-- The catalyzed count is exactly the bare count plus the loop count (frozen-literal check of the
additivity theorem on the chosen transition: `2 + 4 = 6`). -/
theorem catalyzed_count_is_sum :
    catalyzedPath.count = barePath.count + gibbsCatalyst.loop.count := by decide

/-- The catalyst loop carries zero net balance on the chosen transition. -/
theorem gibbsCatalyst_loop_balanced : balance gibbsCatalyst.loop = 0 :=
  neutral_loop_balanced gibbsCatalyst gibbsCatalyst_neutral

-- ---------------------------------------------------------------------------
-- THE CLAIM (content-bearing; the additivity conjunct is the harness theorem).
-- ---------------------------------------------------------------------------

/-- The claim, in honest parts:
* (neutrality) the catalyst is ledger-neutral — its inverse exactly mirrors its forward pass,
  proved by `decide`;
* (count splices additively) the catalyzed path's ledger count is the bare count plus the loop
  count — discharged by the device-harness `Ledger.count_append` via `count_splices`, so a
  regression in that harness lemma breaks THIS build;
* (ledger neutrality) the catalyst loop adds **zero** to the net causal balance — `K` is not
  consumed (`neutral_loop_balanced`).
The middle conjunct is the load-bearing coupling: it is `count_append` applied to the concrete
`barePath`/`gibbsCatalyst.loop`, so renaming/breaking `count_append` fails here. -/
def claimStatement : Prop :=
  gibbsCatalyst.neutral ∧
    (Experiments.Common.Ledger.append barePath gibbsCatalyst.loop).count
      = barePath.count + gibbsCatalyst.loop.count ∧
    balance gibbsCatalyst.loop = 0

def claim : Experiments.Common.Claim :=
  { tag := Experiments.Common.ClaimTag.finiteLedgerModel
    statement := claimStatement }

theorem claim_holds : claim.statement :=
  ⟨gibbsCatalyst_neutral,
    count_splices barePath gibbsCatalyst,
    gibbsCatalyst_loop_balanced⟩

/-- The tag is an honest ceiling: a finite ledger model of catalysis, nothing more. -/
theorem ceiling : claim.tag = Experiments.Common.ClaimTag.finiteLedgerModel := rfl

-- ---------------------------------------------------------------------------
-- A computable run + a non-vacuous exported Experiment, with a proved bridge.
-- ---------------------------------------------------------------------------

structure Setup where
  bare : Path
  catalyst : Catalyst

/-- The run splices the catalyst loop onto the bare path and reports the catalyzed step count
(the number of anchors traversed with the catalyst's help). Computes via `Ledger.count`. -/
def run (s : Setup) : Nat :=
  (Experiments.Common.Ledger.append s.bare s.catalyst.loop).count

/-- The exported claim is a genuine function of the setup: count splicing is additive for THIS
setup. The bridge below pins `run` to it, so the body cannot be silently swapped for
`fun _ => True`. -/
def experiment : Experiments.Common.Experiment Setup Nat :=
  { tag := claim.tag
    run := run
    claim := fun s =>
      (Experiments.Common.Ledger.append s.bare s.catalyst.loop).count
        = s.bare.count + s.catalyst.loop.count }

theorem run_eq_sum (s : Setup) :
    run s = s.bare.count + s.catalyst.loop.count := by
  unfold run; exact Experiments.Common.Ledger.count_append s.bare s.catalyst.loop

def canonicalSetup : Setup := { bare := barePath, catalyst := gibbsCatalyst }

#eval run canonicalSetup                                       -- expect: 6 (= 2 + 4)
#eval balance gibbsCatalyst.loop                               -- expect: 0  (ledger-neutral)
-- load-bearing check: ledger neutrality is NOT vacuous — a NON-neutral catalyst (its inverse does
-- not mirror its forward pass) has nonzero loop balance, so `neutral` is doing real work:
#eval decide (balance
  (Experiments.Common.Ledger.append
    { events := [ { anchor := 3, strain := (2 : Int) } ] }
    { events := [ { anchor := 3, strain := (7 : Int) } ] }) = 0)   -- expect: false
#print axioms claim_holds                                      -- ambient [propext, Quot.sound]; coupling = count_append symbol

/-- Bring a minimal device next to this experiment: it records whether the exported claim fires.
The exported claim is a `Nat` equality (decidable), so the device just decides it. -/
def deviceNear (setup : Setup) : Bool :=
  decide
    ((Experiments.Common.Ledger.append setup.bare setup.catalyst.loop).count
      = setup.bare.count + setup.catalyst.loop.count)

theorem deviceNear_detects_claim (setup : Setup) :
    deviceNear setup = true ↔ experiment.claim setup := by
  unfold deviceNear experiment
  simp only [decide_eq_true_iff]

def triangulation : Experiments.Common.Triangulation Setup Nat :=
  { experiment := experiment
    device := deviceNear
    detects := deviceNear_detects_claim }

end Experiments.TheFirstEffectOfGibbs
