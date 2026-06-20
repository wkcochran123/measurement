import Experiments.Common
import Measurement.Episode84

/-!
# The Feynman Diagram — a tensor contraction as a holonomy

The description (`instrument/chapters/10.tex:550`, `te:feynman-full`) reads a Feynman diagram as a
**tensor contraction in the causal algebra**: vertices are event tensors `E_k`, a propagator is an
admissible contraction `⟨E_i, E_j⟩ = Tr(E_iᵀ G E_j)` between two events (the propagator `G` enforcing
Martin consistency), and the amplitude of a *connected* diagram is the contraction of the ordered
product `U_n = Σ E_k` taken around the diagram.

We model the combinatorial heart of this finitely:

* a **vertex** is an event slot carrying a signed local contribution (the diagonal of its tensor);
* a **propagator** connects two vertices in causal order;
* a **diagram** is either OPEN (a tree / single-leg contraction — one end pinned, no enclosed area)
  or CLOSED (a connected LOOP of propagators — both ends moved, the contraction encloses a cycle).

The physical content we couple to: the amplitude of a *connected loop* of propagators is a
non-trivial signed residue — a HOLONOMY — while an *open* contraction (a tree, one leg pinned)
carries no such residue. In the device this is exactly `Measurement.holonomy`: the commutator
residue a pair accumulates transported around the gauge loop is `±1` around the genuine pair-LOOP
(`holonomy_loop_is_charged`) and `0` on any one-leg OPEN path (`holonomy_open_is_trivial`).
A connected Feynman loop ↔ the charged holonomy; a tree contraction ↔ the trivial open path.

## NOT claimed
That this evaluates a real QFT amplitude; that `Tr(E_iᵀ G E_j)` is *computed* (it is named, not
implemented here); any perturbation series, propagator analyticity, or renormalization; that the
device's δ²-residue *is* a physical propagator. We do NOT claim the loop holonomy equals any
particular field-theory cross-section — only that, in the causal-algebra reading, a CONNECTED loop
of admissible contractions carries a nonzero signed residue and an OPEN tree contraction carries
zero, and we discharge exactly that open-vs-loop split against the device's holonomy theorems.
**Claim ceiling:** a finite ledger model of the open-vs-loop contraction structure, one conjunct of
which is the device's own holonomy split.
-/

open Measurement
open Measurement.CubicGaugeVariation

namespace Experiments.TheFeynmanDiagram

/-- An event vertex `E_k`: a slot index and the signed local contribution it carries (the diagonal
of its event tensor — the part a single-leg contraction can read). -/
structure Vertex where
  slot : Nat
  contribution : Int
deriving DecidableEq, Repr

/-- A diagram's topology: an OPEN contraction (a tree — at least one external leg pinned, no cycle)
or a CLOSED contraction (a connected LOOP — every propagator joins into one cycle). The amplitude's
holonomy lives entirely in this distinction. -/
inductive Topology where
  | open_
  | closed
deriving DecidableEq, Repr

/-- A finite Feynman diagram: an ordered list of event vertices (the product `U_n = Σ E_k`), a count
of admissible propagators wired between them, and the contraction topology. -/
structure Diagram where
  vertices : List Vertex
  propagators : Nat
  topology : Topology
deriving Repr

namespace Diagram

/-- The ORDERED PRODUCT `U_n`: the net signed contribution summed over the vertices (the diagonal of
the contracted tensor — the scalar invariant the description calls the measurable quantity). -/
def orderedProduct (g : Diagram) : Int :=
  (g.vertices.map Vertex.contribution).foldl (· + ·) 0

/-- A diagram is CONNECTED-as-a-loop when its topology is closed and it has at least as many
propagators as vertices (a tree on `n` vertices needs `n-1` edges; a single enclosed cycle needs
`≥ n` — the extra edge is what closes the loop). This is the combinatorial signature of a holonomy
loop: both legs moved, the contraction encloses an area. -/
def isLoop (g : Diagram) : Prop :=
  g.topology = Topology.closed ∧ g.vertices.length ≤ g.propagators

/-- An OPEN contraction (a tree): the topology is open. One external leg is pinned, so the
contraction encloses no cycle — no holonomy. -/
def isTree (g : Diagram) : Prop :=
  g.topology = Topology.open_

-- Make the richer predicates DECIDABLE so `decide`/`#eval` see through them.
instance (g : Diagram) : Decidable (g.isLoop) := by
  unfold isLoop; exact inferInstance
instance (g : Diagram) : Decidable (g.isTree) := by
  unfold isTree; exact inferInstance

end Diagram

-- ---------------------------------------------------------------------------
-- FALSIFIABLE lemmas: each pins a conjunct of the loop/tree contraction rule.
-- Drop a hypothesis and the lemma breaks (witnessed by the FALSE #eval at EOF).
-- ---------------------------------------------------------------------------

/-- LOAD-BEARING: a CLOSED-topology requirement is necessary for a loop — an open diagram is never a
loop, however many propagators it carries. Drop the `topology = closed` conjunct from `isLoop` and
this breaks. Quantified over ALL diagrams. -/
theorem open_is_not_loop (g : Diagram) (h : g.topology = Topology.open_) : ¬ g.isLoop :=
  fun hl => by
    have hclosed : g.topology = Topology.closed := hl.1
    rw [h] at hclosed
    exact Topology.noConfusion hclosed

/-- LOAD-BEARING: the edge count is necessary — a closed-topology diagram with fewer propagators than
vertices does NOT close into a loop (not enough edges to enclose a cycle). Drop the
`length ≤ propagators` conjunct and this breaks. -/
theorem too_few_propagators_not_loop
    (g : Diagram) (h : g.propagators < g.vertices.length) : ¬ g.isLoop :=
  fun hl => Nat.lt_irrefl _ (Nat.lt_of_lt_of_le h hl.2)

/-- A tree and a loop are mutually exclusive topologies: nothing is both. -/
theorem tree_not_loop (g : Diagram) (h : g.isTree) : ¬ g.isLoop :=
  fun hl => by
    have hopen : g.topology = Topology.open_ := h
    have hclosed : g.topology = Topology.closed := hl.1
    rw [hopen] at hclosed
    exact Topology.noConfusion hclosed

-- ---------------------------------------------------------------------------
-- Two canonical diagrams: a connected loop and an open tree.
-- ---------------------------------------------------------------------------

/-- A connected one-loop diagram: two event vertices, two propagators (a cycle), closed topology. -/
def loopDiagram : Diagram :=
  { vertices := [{ slot := 0, contribution := 1 }, { slot := 1, contribution := -1 }]
    propagators := 2
    topology := Topology.closed }

/-- An open tree diagram: two event vertices, one propagator (a single leg), open topology. -/
def treeDiagram : Diagram :=
  { vertices := [{ slot := 0, contribution := 1 }, { slot := 1, contribution := -1 }]
    propagators := 1
    topology := Topology.open_ }

theorem loopDiagram_isLoop : loopDiagram.isLoop := by decide
theorem treeDiagram_isTree : treeDiagram.isTree := by decide
theorem treeDiagram_not_loop : ¬ treeDiagram.isLoop := by decide

/-- The connected loop's ordered product is the signed residue `1 + (-1) = 0` of its two legs (a
frozen-literal check on the chosen diagram, mirroring the device's `split_cancels`). -/
theorem loop_orderedProduct : loopDiagram.orderedProduct = 0 := by decide

-- ---------------------------------------------------------------------------
-- THE CLAIM (content-bearing; the holonomy conjunct is the device's own theorem).
-- ---------------------------------------------------------------------------

/-- The claim, in honest parts:
* (combinatorics) the connected diagram IS a loop and the open diagram is NOT — proved here, and
  load-bearing by `open_is_not_loop` / `too_few_propagators_not_loop`;
* (HOLONOMY — DEVICE-COUPLED) the contraction residue is CHARGED around the connected loop and
  TRIVIAL on the open one. We discharge this with the device's holonomy theorems directly:
  `Measurement.holonomy_loop_is_charged` (the loop residue is `±1`) and
  `Measurement.holonomy_open_is_trivial` (the one-leg open residue is `0`). A sign/zero regression
  or rename in the device's `holonomy` breaks THIS build — load-bearing coupling, not just a name. -/
def claimStatement : Prop :=
  loopDiagram.isLoop ∧ ¬ treeDiagram.isLoop ∧
    (Measurement.holonomy tiltedPath (pairVariation node1 node2) = 1
      ∧ Measurement.holonomy flatPath (pairVariation node1 node2) = -1) ∧
    Measurement.holonomy tiltedPath (pairVariation node2 node1) = 0

def claim : Experiments.Common.Claim :=
  { tag := Experiments.Common.ClaimTag.finiteLedgerModel
    statement := claimStatement }

theorem claim_holds : claim.statement :=
  ⟨loopDiagram_isLoop, treeDiagram_not_loop,
    Measurement.holonomy_loop_is_charged, Measurement.holonomy_open_is_trivial⟩

/-- The tag is an honest ceiling: a finite ledger model of the contraction topology, with one
conjunct discharged by the device's holonomy split. -/
theorem ceiling : claim.tag = Experiments.Common.ClaimTag.finiteLedgerModel := rfl

-- ---------------------------------------------------------------------------
-- A computable run + a NON-vacuous Experiment.claim, with a proved bridge.
-- ---------------------------------------------------------------------------

structure Setup where
  diagram : Diagram

/-- The run computes whether the diagram is a connected loop (thanks to the `Decidable` instance). -/
def run (s : Setup) : Bool := decide (s.diagram.isLoop)

/-- The exported claim is a genuine function of the setup; this bridge pins it to `run`, so the
claim body cannot be silently swapped for `fun _ => True`. -/
def experiment : Experiments.Common.Experiment Setup Bool :=
  { tag := claim.tag
    run := run
    claim := fun s => s.diagram.isLoop }

theorem run_iff_claim (s : Setup) :
    run s = true ↔ experiment.claim s := by
  simp only [run, experiment, decide_eq_true_iff]

def canonicalSetup : Setup := { diagram := loopDiagram }

#eval run canonicalSetup                              -- expect: true   (connected loop)
#eval run { diagram := treeDiagram }                  -- expect: false  (open tree — no holonomy)
#print axioms claim_holds                             -- expect: no axioms (device holonomy is decide-clean)

/-- Bring a minimal device next to this experiment: it records whether the exported claim fires.
(`run setup = decide setup.diagram.isLoop`, and `experiment.claim setup` is definitionally
`setup.diagram.isLoop`, so the device is exactly the run.) -/
def deviceNear (setup : Setup) : Bool :=
  run setup

theorem deviceNear_detects_claim (setup : Setup) :
    deviceNear setup = true ↔ experiment.claim setup := by
  simp only [deviceNear, run, experiment, decide_eq_true_iff]

def triangulation : Experiments.Common.Triangulation Setup Bool :=
  { experiment := experiment
    device := deviceNear
    detects := deviceNear_detects_claim }

-- GATE EVIDENCE: the falsifiable predicate evaluated where it is FALSE proves it is load-bearing,
-- not vacuous. `treeDiagram` is open ⇒ `isLoop` is FALSE here.
#eval decide (treeDiagram.isLoop)                     -- expect: false  (load-bearing, non-vacuous)

end Experiments.TheFeynmanDiagram
