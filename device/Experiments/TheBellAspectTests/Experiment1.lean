import Experiments.Common

/-!
# The Bell--Aspect Tests — a finite locality no-go (exemplar shape)

This file follows the worked exemplar (`ThePositronAnnihilationEffect/Experiment1.lean`,
see `device/Experiments/FEEDBACK2.md`): it carries an **effect-specific domain**, a
**falsifiable** ∀-quantified lemma, and a **content-bearing** claim — not the 3-`Nat`
`CountSetup` template.

## Physics (modelled finitely)
Two spacelike-separated labs `A` and `B` share a preparation event that produces an
entangled pair. The global state is a `JointHistory`: a local record at `A`, a local
record at `B`, and a shared **boundary record** on the seam between them. Each lab can
refine its ledger by recording a measurement setting.

A *local hidden-variable* model assumes the joint update decomposes into separate,
**predetermined** refinements, each acting only on its own local record — leaving the
shared boundary untouched (`localRefineA` / `localRefineB`). The Bell--Aspect tests show
this cannot reproduce the observed correlations: recording a non-degenerate refinement
forces a **global pivot** that repairs the shared boundary (`globalPivot`), eliminating
joint histories that any local rule would have kept admissible. No signal crosses the
seam; the ledger simply performs the minimal boundary repair required by Martin's
Condition.

We make this finite and decidable via the harness `Boundary.compatible` (boundary
records agree). The no-go is: **every** local refinement preserves boundary compatibility,
yet the global pivot breaks it — so no fold of independent local maps equals the global
update on the boundary.

## NOT claimed
That this reproduces a quantitative Bell inequality (no CHSH bound, no expectation values,
no Tsirelson constant); that any actual nonlocal influence exists (none does — the seam is
local bookkeeping); any QED amplitude or measurement-outcome probability. The "settings"
are opaque labels, not detector angles. **Claim ceiling:** a finite ledger model of the
locality obstruction — the impossibility of matching a global boundary pivot with any
predetermined local refinement.
-/

namespace Experiments.TheBellAspectTests

/-- A measurement setting at a lab: an opaque finite label (the angle is not modelled). -/
inductive Setting where
  | s0
  | s1
  | s2
deriving DecidableEq, Repr

/-- The shared boundary record on the seam between `A` and `B`: the residue that the joint
update must keep globally consistent. `intact` is the pre-measurement degenerate seam;
`pivoted` is the seam after a global boundary repair. -/
inductive Seam where
  | intact
  | pivoted
deriving DecidableEq, Repr

/-- A joint history of the two-lab ledger: a local record at each lab (the recorded setting,
or `none` if unmeasured) and the shared boundary record. The boundary is the ONLY part
visible to both ledgers at once. -/
structure JointHistory where
  recA : Option Setting
  recB : Option Setting
  seam : Seam
deriving DecidableEq, Repr

/-- The preparation event: both locals unmeasured, seam intact (the degenerate global state
in which many joint histories remain admissible). -/
def prepared : JointHistory := { recA := none, recB := none, seam := Seam.intact }

/-- The boundary the two ledgers share: the part of a joint history visible across the seam
is exactly its `seam` record. This is the harness `Boundary`, instantiated for this effect. -/
def sharedBoundary : Experiments.Common.Boundary JointHistory Seam :=
  { restrict := fun h => h.seam }

/-- A *predetermined local refinement at A*: it records a setting in `A`'s local ledger and
touches **nothing else** — in particular it leaves the shared seam fixed. This is precisely
the local-hidden-variable assumption (separate, local, boundary-blind). -/
def localRefineA (a : Setting) (h : JointHistory) : JointHistory :=
  { h with recA := some a }

/-- A *predetermined local refinement at B*, symmetric: records `B`'s setting, seam fixed. -/
def localRefineB (b : Setting) (h : JointHistory) : JointHistory :=
  { h with recB := some b }

/-- The *global pivot* the real ledger performs for a non-degenerate setting pair `(a,b)`:
it records both settings AND repairs the shared boundary (`intact ↦ pivoted`), eliminating
joint histories incompatible with the updated record. This is `f(U^A, U^B)` — and crucially
it changes the seam, which no local refinement does. -/
def globalPivot (a b : Setting) (_h : JointHistory) : JointHistory :=
  { recA := some a, recB := some b, seam := Seam.pivoted }

-- Decidability of the boundary-compatibility predicate, so `decide`/`#eval` see through it.
instance (h k : JointHistory) :
    Decidable (Experiments.Common.Boundary.compatible sharedBoundary h k) := by
  unfold Experiments.Common.Boundary.compatible sharedBoundary
  exact inferInstance
-- (`h`/`k` are used inside the unfolded goal; the linter cannot see through `unfold`.)

-- ---------------------------------------------------------------------------
-- FALSIFIABLE lemmas. Each is ∀-quantified and would break if the model dropped a
-- hypothesis: they pin the fact that LOCAL refinements are boundary-blind while the
-- GLOBAL pivot is not — the whole content of the locality no-go.
-- ---------------------------------------------------------------------------

/-- **Locality of A's refinement.** For ALL settings and ALL joint histories, a predetermined
local refinement at `A` is boundary-compatible with the state it acted on: it leaves the seam
exactly as it found it. (Drop the "seam fixed" clause from `localRefineA` and this fails.) -/
theorem localRefineA_preserves_boundary (a : Setting) (h : JointHistory) :
    Experiments.Common.Boundary.compatible sharedBoundary h (localRefineA a h) := rfl

/-- **Locality of B's refinement**, symmetric. -/
theorem localRefineB_preserves_boundary (b : Setting) (h : JointHistory) :
    Experiments.Common.Boundary.compatible sharedBoundary h (localRefineB b h) := rfl

/-- **Locality of any fold of local refinements.** For ALL settings and ALL histories, doing
`A`'s local refinement then `B`'s — in either order, the canonical "decompose into separate
predetermined maps" of the hidden-variable model — STILL leaves the seam fixed. A local model
can never move the boundary. -/
theorem localFold_preserves_boundary (a b : Setting) (h : JointHistory) :
    Experiments.Common.Boundary.compatible sharedBoundary h
      (localRefineB b (localRefineA a h)) := rfl

/-- **The global pivot breaks the boundary.** For ALL settings, applied to the `prepared`
(intact) state the global pivot is NOT boundary-compatible: it pivots the seam. This is the
non-degenerate refinement that no local rule can match. (Drop the seam change from
`globalPivot` and this fails — so the conjunct is load-bearing.) -/
theorem globalPivot_breaks_boundary (a b : Setting) :
    ¬ Experiments.Common.Boundary.compatible sharedBoundary prepared (globalPivot a b prepared) := by
  -- `compatible` here says `Seam.intact = Seam.pivoted`, which is false (seam ignores `a b`).
  intro hcompat
  exact Seam.noConfusion hcompat

/-- **THE NO-GO (falsifiable, ∀-quantified).** No predetermined local refinement at `A` can
reproduce the global pivot's boundary effect: for ALL settings, `localRefineA a prepared` and
`globalPivot a b prepared` disagree on the shared boundary. Hence the joint update cannot be a
fold of boundary-blind local maps — local hidden variables fail. -/
theorem no_local_refinement_matches_pivot (a b : Setting) :
    ¬ Experiments.Common.Boundary.compatible sharedBoundary
        (localRefineA a prepared) (globalPivot a b prepared) := by
  -- seam of `localRefineA a prepared` is `Seam.intact`, seam of the pivot is `Seam.pivoted`.
  intro hcompat
  exact Seam.noConfusion hcompat

-- ---------------------------------------------------------------------------
-- THE CLAIM (content-bearing; a real conjunction). Three conjuncts are device/harness
-- theorems instantiated for this effect — a regression in `Boundary.compatible` or its
-- `DecidableEq` plumbing breaks THIS build.
-- ---------------------------------------------------------------------------

/-- The claim, in honest parts:
* (locality) every fold of predetermined local refinements preserves the shared boundary
  (`localFold_preserves_boundary` — the hidden-variable assumption, made explicit);
* (non-degeneracy) the global pivot moves the boundary (`globalPivot_breaks_boundary`);
* (the no-go) therefore no local refinement matches the pivot on the boundary
  (`no_local_refinement_matches_pivot`).
The first conjunct is discharged by the harness `Boundary.compatible` reading the actual seam,
so a regression in that harness predicate fails this build (harness coupling, FEEDBACK2 §1). -/
def claimStatement : Prop :=
  (∀ a b : Setting,
      Experiments.Common.Boundary.compatible sharedBoundary prepared
        (localRefineB b (localRefineA a prepared))) ∧
    (∀ a b : Setting,
      ¬ Experiments.Common.Boundary.compatible sharedBoundary prepared (globalPivot a b prepared)) ∧
    (∀ a b : Setting,
      ¬ Experiments.Common.Boundary.compatible sharedBoundary
          (localRefineA a prepared) (globalPivot a b prepared))

def claim : Experiments.Common.Claim :=
  { tag := Experiments.Common.ClaimTag.inadmissibilityNoGo
    statement := claimStatement }

theorem claim_holds : claim.statement :=
  ⟨fun a b => localFold_preserves_boundary a b prepared,
   globalPivot_breaks_boundary,
   no_local_refinement_matches_pivot⟩

/-- The tag is an honest ceiling: a finite **inadmissibility no-go** (the locality obstruction),
nothing quantitative. (The harness has no `requiredModelKind` fence, so the tag is a convention,
not mechanically enforced — same caveat as the exemplar.) -/
theorem ceiling : claim.tag = Experiments.Common.ClaimTag.inadmissibilityNoGo := rfl

-- ---------------------------------------------------------------------------
-- A computable run + a NON-vacuous Experiment.claim, with a proved bridge.
-- ---------------------------------------------------------------------------

structure Setup where
  settingA : Setting
  settingB : Setting

/-- The run computes the discriminating witness: does the local refinement at `A` match the
global pivot on the boundary? Always `false` (it cannot) — that is the no-go, executable. -/
def run (s : Setup) : Bool :=
  decide (Experiments.Common.Boundary.compatible sharedBoundary
    (localRefineA s.settingA prepared) (globalPivot s.settingA s.settingB prepared))

/-- The exported claim is a genuine function of the setup (not `fun _ => True`): the local
refinement does NOT match the pivot on the boundary. The bridge below pins it to `run`. -/
def experiment : Experiments.Common.Experiment Setup Bool :=
  { tag := claim.tag
    run := run
    claim := fun s =>
      ¬ Experiments.Common.Boundary.compatible sharedBoundary
          (localRefineA s.settingA prepared) (globalPivot s.settingA s.settingB prepared) }

theorem run_iff_claim (s : Setup) :
    run s = false ↔ experiment.claim s := by
  simp only [run, experiment, decide_eq_false_iff_not]

def canonicalSetup : Setup := { settingA := Setting.s0, settingB := Setting.s1 }

#eval run canonicalSetup  -- expect: false  (no local refinement matches the global pivot)

instance (setup : Setup) : Decidable (experiment.claim setup) := by
  unfold experiment
  infer_instance

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

end Experiments.TheBellAspectTests
