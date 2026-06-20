import Experiments.Common

/-!
# The Limitation of Indexing — rebuilt to the EXEMPLAR shape

Source: `instrument/chapters/11.tex:52`, phenomenon `ph:library-catalog` (Russell 1903).

## Physics (modelled finitely)
A library shelves events `{eᵢ}` as books. Each measurement attaches a finer **tag**
(subject, author, edition); by the Axiom of Event Selection no tag may be removed without
merging incompatible categories, so the count `N` of distinguishable configurations is
**monotone**: `ΔS ≥ 0` for `S = ln N`. That is the entropy-as-bookkeeping reading.

The **CAVEAT EMPTOR** of the description is the load-bearing subtlety, and it is what this
file actually pins: *re-indexing the catalog by a pure renaming (a `decode` that only relabels)
generates no novelty* — the re-indexed shelf is a structurally identical copy with the **same
count**. Distinguishability can only grow through a **genuine refinement** (a split), never
through a relabel. So the model carries two falsifiable facts in tension:
  * a relabel preserves the count (`Ledger.count_map`) — no enrichment; and
  * a genuine split strictly increases it (a real refinement adds a distinction).

## NOT claimed
That `S = ln N` is derived (the log is a label — we work with the bare count `N`); any
thermodynamic `ΔS ≥ 0` from energy dissipation (we get monotonicity from *order preservation*,
the description's own point); that real library cataloging is bijective; any continuum entropy.
**Claim ceiling:** a finite ledger/count model of the indexing obstruction — a relabel is bounded
by the original count, a split is not.
-/

namespace Experiments.TheLimitationOfIndexing

/-- A book on a shelf: an event id, plus the finite tag attached so far. A finer tag is a longer
list of category labels. -/
structure Book where
  eventId : Nat
  tags : List Nat
deriving DecidableEq, Repr

/-- The catalog: the finite ledger of currently-shelved books. We reuse the harness `Ledger`. -/
abbrev Catalog := Experiments.Common.Ledger Book

/-- The number of distinguishable configurations `N` = the catalog count. -/
def distinguishable (c : Catalog) : Nat := c.count

/-- A **relabel**: rename every book's event id by a pure function. This is the CAVEAT EMPTOR
operation — "continue the construction indefinitely" by re-indexing. It is `Ledger.map` of a
relabelling `decode`, so it never changes how many books there are. -/
def relabel (f : Nat -> Nat) (c : Catalog) : Catalog :=
  c.map (fun b => { b with eventId := f b.eventId })

/-- A **genuine refinement**: shelve one new book carrying a strictly finer tag (a real new
distinction). Unlike a relabel, this adds an entry. -/
def refineWith (newBook : Book) (c : Catalog) : Catalog :=
  { events := newBook :: c.events }

-- ---------------------------------------------------------------------------
-- FALSIFIABLE lemmas. Each is ∀-quantified and breaks if a hypothesis/structure is dropped.
-- ---------------------------------------------------------------------------

/-- CAVEAT EMPTOR, formalized: **a relabel produces no novelty** — the re-indexed catalog has
EXACTLY the same number of distinguishable configurations. Quantified over ALL relabellings and
ALL catalogs. (Falsifiable: it fails the moment `relabel` is replaced by an operation that adds
or drops a book — e.g. `refineWith`.) -/
theorem relabel_preserves_distinguishable (f : Nat -> Nat) (c : Catalog) :
    distinguishable (relabel f c) = distinguishable c := by
  unfold distinguishable relabel
  exact Experiments.Common.Ledger.count_map _ c

/-- Order preservation / monotonicity: a relabel never lets the count EXCEED the original. This is
the `ΔS ≥ 0`-flavoured bound, but as a `≤` ceiling: re-indexing is bounded by what you started
with. (Falsifiable: `refineWith b c` is NOT bounded by `c.count`.) -/
theorem relabel_boundedBy_original (f : Nat -> Nat) (c : Catalog) :
    Experiments.Common.Counting.boundedBy (relabel f c) (distinguishable c) :=
  Experiments.Common.Counting.boundedBy_of_eq (relabel_preserves_distinguishable f c)

/-- A genuine refinement STRICTLY increases the count — distinguishability really grows only when
a new distinction is shelved, not when the catalog is merely re-indexed. Quantified over all books
and catalogs. (Falsifiable: drop the `:: ` cons and it is `c.count = c.count`, not `<`.) -/
theorem refine_increases_distinguishable (b : Book) (c : Catalog) :
    distinguishable c < distinguishable (refineWith b c) := by
  unfold distinguishable refineWith Experiments.Common.Ledger.count
  simp only [List.length_cons]
  omega

-- ---------------------------------------------------------------------------
-- A concrete catalog and its two fates (relabel vs. refine).
-- ---------------------------------------------------------------------------

def book0 : Book := { eventId := 0, tags := [7] }
def book1 : Book := { eventId := 1, tags := [7, 3] }

/-- A two-book catalog. -/
def sampleCatalog : Catalog := { events := [book0, book1] }

/-- The relabel `eventId ↦ eventId + 100`: a pure re-indexing. -/
def shift : Nat -> Nat := fun n => n + 100

/-- A genuinely new, finer-tagged book to shelve. -/
def newBook : Book := { eventId := 2, tags := [7, 3, 5] }

/-- Concrete witness that relabel keeps `N = 2`. -/
theorem sample_relabel_count :
    distinguishable (relabel shift sampleCatalog) = 2 := by
  unfold distinguishable relabel sampleCatalog
  decide

/-- Concrete witness that a genuine refinement grows `N` to `3`. -/
theorem sample_refine_count :
    distinguishable (refineWith newBook sampleCatalog) = 3 := by
  unfold distinguishable refineWith sampleCatalog Experiments.Common.Ledger.count
  decide

-- ---------------------------------------------------------------------------
-- THE CLAIM (content-bearing conjunction; one conjunct discharged by the harness).
-- ---------------------------------------------------------------------------

/-- The claim, in honest parts:
* (no enrichment) any relabel of the sample catalog preserves `N` — the CAVEAT EMPTOR;
* (bounded — order preservation) that relabelled catalog is `boundedBy` the original count,
  discharged by `Experiments.Common.Counting.boundedBy_of_eq` (the LOAD-BEARING harness coupling:
  break `count_map`/`boundedBy_of_eq` and this build breaks);
* (genuine growth) a real refinement strictly increases `N` — distinguishability is monotone but
  ONLY moves under an actual split. -/
def claimStatement : Prop :=
  (distinguishable (relabel shift sampleCatalog) = distinguishable sampleCatalog) ∧
    Experiments.Common.Counting.boundedBy
      (relabel shift sampleCatalog) (distinguishable sampleCatalog) ∧
    distinguishable sampleCatalog < distinguishable (refineWith newBook sampleCatalog)

def claim : Experiments.Common.Claim :=
  { tag := Experiments.Common.ClaimTag.inadmissibilityNoGo
    statement := claimStatement }

theorem claim_holds : claim.statement :=
  ⟨relabel_preserves_distinguishable shift sampleCatalog,
   relabel_boundedBy_original shift sampleCatalog,
   refine_increases_distinguishable newBook sampleCatalog⟩

/-- The tag is an honest ceiling: a finite no-go on enrichment by re-indexing. -/
theorem ceiling : claim.tag = Experiments.Common.ClaimTag.inadmissibilityNoGo := rfl

-- ---------------------------------------------------------------------------
-- A computable run + a non-vacuous Experiment.claim, with a proved bridge.
-- ---------------------------------------------------------------------------

structure Setup where
  catalog : Catalog
  relabelBy : Nat -> Nat
  refineBy : Book

/-- The run reports whether re-indexing left `N` unchanged (the no-enrichment verdict). -/
def run (s : Setup) : Bool :=
  decide (distinguishable (relabel s.relabelBy s.catalog) = distinguishable s.catalog)

def experiment : Experiments.Common.Experiment Setup Bool :=
  { tag := claim.tag
    run := run
    claim := fun s =>
      distinguishable (relabel s.relabelBy s.catalog) = distinguishable s.catalog }

/-- Make the exported claim DECIDABLE so `deviceNear`/`#eval` compute through it. -/
instance (s : Setup) : Decidable (experiment.claim s) := by
  unfold experiment; exact inferInstance

theorem run_iff_claim (s : Setup) :
    run s = true ↔ experiment.claim s := by
  simp only [run, experiment, decide_eq_true_iff]

def canonicalSetup : Setup :=
  { catalog := sampleCatalog, relabelBy := shift, refineBy := newBook }

#eval run canonicalSetup                          -- expect: true  (relabel preserves N)

/-- Bring a minimal device next to this experiment: it records whether the exported claim fires. -/
def deviceNear (setup : Setup) : Bool :=
  decide (experiment.claim setup)

theorem deviceNear_detects_claim (setup : Setup) :
    deviceNear setup = true ↔ experiment.claim setup := by
  unfold deviceNear; exact decide_eq_true_iff

def triangulation : Experiments.Common.Triangulation Setup Bool :=
  { experiment := experiment
    device := deviceNear
    detects := deviceNear_detects_claim }

-- ---------------------------------------------------------------------------
-- Gate evidence.
-- ---------------------------------------------------------------------------

#print axioms claim_holds
-- The falsifiable predicate evaluated where it is FALSE: a *genuine refinement* does NOT
-- preserve N, so "relabel-style preservation" applied to a refinement step is `false`.
#eval decide
  (distinguishable (refineWith newBook sampleCatalog) = distinguishable sampleCatalog) -- false

end Experiments.TheLimitationOfIndexing
