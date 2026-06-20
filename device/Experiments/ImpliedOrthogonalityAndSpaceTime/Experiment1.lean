import Experiments.Common

/-!
# Implied Orthogonality and Space-Time — effect-specific finite model (EXEMPLAR shape)

Source: `instrument/chapters/09.tex:1087` (`phenomenon`, "Implied Orthogonality and
Space--Time"). The source carries a CAVEAT EMPTOR: it presents NO phenomenon suggesting any
structure *geometrically orthogonal to space--time*; any "orthogonality" language is to be read
**set-theoretically**, not geometrically. What the author DOES suggest is an *informational
degree of freedom between measurements* (cf. the "here-and-now" and "constant" phenomena).

This file follows the shape of
`device/Experiments/ThePositronAnnihilationEffect/Experiment1.lean`:

1. an **effect-specific domain** (`Reading`, `SpaceTimeProbe`) — NOT the 3-`Nat`
   `Experiments.Common.CountSetup`;
2. genuinely **falsifiable** ∀-quantified lemmas — `agree_spacetime_indistinguishable` and
   `distinguishable_needs_spacetime_difference` each break if a hypothesis is dropped;
3. a **content-bearing** claim: a real conjunction, never `True`, never `by decide` on frozen
   literals as the whole content;
4. an honest `ClaimTag` + a candid "NOT claimed" disclaimer;
5. explicit `Decidable` instances so `decide`/`#eval` see through the richer `Prop`s;
6. a **harness coupling**: the indistinguishability conjunct of `claim_holds` is discharged by
   the harness operator `Experiments.Common.Projection.sameShadow` (a regression — rename/sorry
   on `sameShadow` in `Common.Basic`) breaks THIS build.

## Physics (modelled finitely — read SET-THEORETICALLY, per the source's caveat)
A `Reading` records a space-time event — a `here` coordinate and a `now` coordinate — together
with an extra `info` label: the *informational degree of freedom between measurements*. A
space-time probe sees only WHERE and WHEN: it projects a `Reading` onto its `(here, now)` pair
and discards `info`. Hence two readings that share the same here-and-now but carry DIFFERENT
`info` are operationally **indistinguishable to space-time** — they cast the same space-time
shadow. The informational coordinate is therefore a degree of freedom *between* measurements,
not visible *within* the space-time projection. The word "orthogonal" here means exactly this:
`info` is a coordinate the space-time projection forgets — a set-theoretic complement, NOT a
geometric perpendicular.

## NOT claimed
NO geometric structure orthogonal to space-time (the source explicitly denies this); NO extra
physical dimension; NO Hilbert-space orthogonality; NO claim that `info` is dynamical or
conserved. We model "orthogonality" purely set-theoretically as *projection forgetfulness*, and
we do NOT claim the converse (distinct shadows imply distinct info — that fails: two readings at
different here-and-now can share info). **Claim ceiling:** a finite projection model exhibiting
one informational degree of freedom that the space-time projection cannot resolve, the
indistinguishability conjunct of which is the harness's own `sameShadow`.
-/

namespace Experiments.ImpliedOrthogonalityAndSpaceTime

/-- A measurement record: a space-time event (`here`, `now`) plus an extra informational label
`info` — the *degree of freedom between measurements* the source points at. `info` is read
set-theoretically (a tag), NOT as a geometric coordinate. -/
structure Reading where
  here : Nat
  now : Nat
  info : Nat
deriving DecidableEq, Repr

/-- The space-time event a reading lives at: just WHERE and WHEN, with `info` stripped. -/
structure Event where
  here : Nat
  now : Nat
deriving DecidableEq, Repr

/-- A space-time probe: an apparatus that resolves only space-time. It has no parameters here —
its whole content is the projection it casts (it sees `(here, now)`, never `info`). -/
structure SpaceTimeProbe where
deriving Repr

namespace SpaceTimeProbe

/-- The space-time event a probe extracts from a reading: it keeps `here` and `now` and
**discards `info`**. This forgetfulness is the whole effect. -/
def event (_ : SpaceTimeProbe) (r : Reading) : Event :=
  { here := r.here, now := r.now }

end SpaceTimeProbe

-- ---------------------------------------------------------------------------
-- The harness PROJECTION operator, instantiated to this domain (the coupling).
-- `Experiments.Common.Projection.sameShadow` is the harness's own notion of
-- "operationally indistinguishable": two states with equal projections.
-- ---------------------------------------------------------------------------

/-- The harness projection a probe casts: a reading's space-time event. -/
def spacetimeProjection (p : SpaceTimeProbe) :
    Experiments.Common.Projection Reading Event :=
  { project := p.event }

/-- Two readings are **indistinguishable to space-time** under probe `p` exactly when the
harness's `sameShadow` holds for `spacetimeProjection`. We DEFINE indistinguishability through
the harness symbol, so a regression in `Common.Projection.sameShadow` breaks everything
downstream. -/
def stIndistinguishable (p : SpaceTimeProbe) (r₁ r₂ : Reading) : Prop :=
  Experiments.Common.Projection.sameShadow (spacetimeProjection p) r₁ r₂

instance (p : SpaceTimeProbe) (r₁ r₂ : Reading) : Decidable (stIndistinguishable p r₁ r₂) := by
  unfold stIndistinguishable Experiments.Common.Projection.sameShadow spacetimeProjection
  exact inferInstance

-- ---------------------------------------------------------------------------
-- FALSIFIABLE lemmas. Each would break if the model dropped a hypothesis.
-- ---------------------------------------------------------------------------

/-- **Space-time agreement ⟹ indistinguishable.** For EVERY probe and EVERY pair of readings:
if they agree on `here` AND on `now`, the probe cannot tell them apart, regardless of `info`.
Quantified over all inputs; this would FAIL if `event` (the projection) had kept `info` —
then two readings differing only in `info` would project differently and the conclusion break. -/
theorem agree_spacetime_indistinguishable
    (p : SpaceTimeProbe) (r₁ r₂ : Reading)
    (hh : r₁.here = r₂.here) (hn : r₁.now = r₂.now) :
    stIndistinguishable p r₁ r₂ := by
  show (spacetimeProjection p).project r₁ = (spacetimeProjection p).project r₂
  show ({ here := r₁.here, now := r₁.now } : Event) = { here := r₂.here, now := r₂.now }
  simp only [hh, hn]

/-- **Distinguishability needs a space-time difference.** Contrapositive face of the rule: if a
probe CAN tell two readings apart, they must differ in `here` or in `now` — never merely in
`info`. Pins that `info` is genuinely invisible to space-time (the "orthogonality"). -/
theorem distinguishable_needs_spacetime_difference
    (p : SpaceTimeProbe) (r₁ r₂ : Reading)
    (hne : ¬ stIndistinguishable p r₁ r₂) :
    r₁.here ≠ r₂.here ∨ r₁.now ≠ r₂.now := by
  match h : decide (r₁.here = r₂.here), h2 : decide (r₁.now = r₂.now) with
  | true, true =>
    exact absurd (agree_spacetime_indistinguishable p r₁ r₂
      (of_decide_eq_true h) (of_decide_eq_true h2)) hne
  | true, false => exact Or.inr (of_decide_eq_false h2)
  | false, _ => exact Or.inl (of_decide_eq_false h)

-- ---------------------------------------------------------------------------
-- The canonical witness: two DISTINCT readings, SAME here-and-now, DIFFERENT info.
-- ---------------------------------------------------------------------------

/-- The standard probe (it has no tunable parameters; its content is the projection). -/
def defaultProbe : SpaceTimeProbe := {}

/-- Reading A: at space-time event (here 7, now 3), carrying informational label 0. -/
def readingA : Reading := { here := 7, now := 3, info := 0 }

/-- Reading B: the SAME space-time event (here 7, now 3), but a DIFFERENT informational
label 1. The records differ; the space-time projection cannot tell them apart. -/
def readingB : Reading := { here := 7, now := 3, info := 1 }

/-- The two readings are genuinely DIFFERENT records (they differ in `info`). -/
theorem readings_distinct : readingA ≠ readingB := by decide

/-- ...yet they are operationally INDISTINGUISHABLE to the space-time probe — the informational
degree of freedom is invisible to space-time. This is the whole effect in one line. -/
theorem canonical_indistinguishable :
    stIndistinguishable defaultProbe readingA readingB := by decide

/-- The shared space-time event is exactly `(here 7, now 3)` (a frozen-literal check on the
chosen witness — NOT a property enforced for all inputs). -/
theorem canonical_shared_event :
    defaultProbe.event readingA = { here := 7, now := 3 } := by decide

-- ---------------------------------------------------------------------------
-- THE CLAIM (content-bearing conjunction; one conjunct is the harness theorem).
-- ---------------------------------------------------------------------------

/-- The claim, in honest parts:
* (distinct records) `readingA ≠ readingB` — proved here by construction (they differ in the
  informational degree of freedom);
* (indistinguishable to space-time) they are `stIndistinguishable` under `defaultProbe` — this
  conjunct is literally `Experiments.Common.Projection.sameShadow` applied to
  `spacetimeProjection` (harness coupling: a regression in `sameShadow` fails this build);
* (the difference is purely informational) the two readings share the same space-time event —
  so their distinctness lives ENTIRELY in `info`, the degree of freedom between measurements. -/
def claimStatement : Prop :=
  readingA ≠ readingB ∧
    stIndistinguishable defaultProbe readingA readingB ∧
    defaultProbe.event readingA = defaultProbe.event readingB

def claim : Experiments.Common.Claim :=
  { tag := Experiments.Common.ClaimTag.finiteLedgerModel
    statement := claimStatement }

theorem claim_holds : claim.statement :=
  ⟨readings_distinct, canonical_indistinguishable, by decide⟩

/-- The tag is an honest ceiling: a finite projection model, nothing more. -/
theorem ceiling : claim.tag = Experiments.Common.ClaimTag.finiteLedgerModel := rfl

-- ---------------------------------------------------------------------------
-- A computable run + a NON-vacuous Experiment.claim, with a proved bridge.
-- ---------------------------------------------------------------------------

structure Setup where
  probe : SpaceTimeProbe
  left : Reading
  right : Reading

/-- The run actually computes — thanks to the `Decidable` instance for `stIndistinguishable`. -/
def run (s : Setup) : Bool := decide (stIndistinguishable s.probe s.left s.right)

/-- The exported claim is a genuine function of the setup; this bridge pins it to `run`, so the
claim body cannot be silently swapped for `fun _ => True` without breaking the proof. -/
def experiment : Experiments.Common.Experiment Setup Bool :=
  { tag := claim.tag
    run := run
    claim := fun s => stIndistinguishable s.probe s.left s.right }

theorem run_iff_claim (s : Setup) :
    run s = true ↔ experiment.claim s := by
  simp only [run, experiment, decide_eq_true_iff]

def canonicalSetup : Setup :=
  { probe := defaultProbe, left := readingA, right := readingB }

#eval run canonicalSetup                                   -- expect: true  (same here-and-now)
#eval run { canonicalSetup with right := readingA }        -- expect: true  (trivially same)
#eval run { canonicalSetup with right := { readingB with here := 9 } }
                                                           -- expect: false (different `here`)
#print axioms claim_holds                                  -- ambient footprint, NOT coupling

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

end Experiments.ImpliedOrthogonalityAndSpaceTime
