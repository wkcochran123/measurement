import Experiments.Common

/-!
# The Message Effect — rebuilt to the EXEMPLAR shape

Source description: `instrument/chapters/09.tex:263` (`device/Experiments/TheMessageEffect/description.md`).

## Physics (modelled finitely)
Two refinement updates are transmitted from lab `A`. The receiver at `B` decodes only through a
SYMMETRIC bilinear form (a Galerkin projection onto a shared test space). A symmetric form responds
solely to the symmetric part of an update; the ANTISYMMETRIC twist (the "informational cross
product" / curl) lies in the KERNEL of the projection and is therefore unrecordable. We model an
update as an ordered pair of integer increments on two basis slots; the readable shadow is the
symmetrized pair `(a+b, a+b)` style witness — concretely, the unordered/symmetric data — and the
antisymmetric residue `a - b` is exactly what the symmetric channel cannot see. THE MESSAGE EFFECT:
two updates that differ only by their antisymmetric twist project to the SAME shadow, so no symmetric
receiver can distinguish them — "a message is not what is sent, but what can be stably projected."

## NOT claimed
That this is a real electromagnetic channel, a real Galerkin finite-element method, or genuine curl
on a manifold; no continuum limit is taken; `curl`/`cross product` here is the finite integer
residue `a - b`, a LABEL for the antisymmetric part, not a derived differential operator. No claim
about attenuation, noise, SNR, or channel capacity in bits. **Claim ceiling:** a finite projection
model in which the lossy (symmetric) readout literally cannot separate two updates that share a
symmetric part — discharged by the harness's `Projection.sameShadow`.
-/

namespace Experiments.TheMessageEffect

/-- A refinement update from lab `A`: two integer increments on a two-element basis. -/
structure Update where
  slot0 : Int
  slot1 : Int
deriving DecidableEq, Repr

/-- The antisymmetric residue (the "informational cross product" / discrete curl): the twist the
symmetric channel cannot carry. -/
def Update.twist (u : Update) : Int := u.slot0 - u.slot1

/-- The symmetric content the receiver CAN read: the total (trace of the symmetrized update). A
symmetric bilinear form sees alignment, i.e. the sum, and is blind to the order of the two slots. -/
def Update.symContent (u : Update) : Int := u.slot0 + u.slot1

/-- The Galerkin receiver at `B`: it decodes an update down to its symmetric shadow only. -/
def receiver : Experiments.Common.Projection Update Int :=
  { project := Update.symContent }

/-- Two updates are INDISTINGUISHABLE to the symmetric receiver iff they share a symmetric shadow. -/
def sameMessage (u v : Update) : Prop :=
  receiver.sameShadow u v

-- Make the predicates DECIDABLE so `decide`/`#eval` compute through them.
instance (u v : Update) : Decidable (sameMessage u v) := by
  unfold sameMessage Experiments.Common.Projection.sameShadow receiver Update.symContent
  exact inferInstance

-- ---------------------------------------------------------------------------
-- FALSIFIABLE lemmas. Each is ∀-quantified and would BREAK if the model were wrong.
-- ---------------------------------------------------------------------------

/-- The flip of an update keeps the SAME symmetric content (the receiver is blind to slot order).
∀ over all updates. -/
def Update.flip (u : Update) : Update := { slot0 := u.slot1, slot1 := u.slot0 }

/-- FALSIFIABLE (Message Effect core): an update and its flip carry the SAME message even though
their twist is NEGATED. Drop the symmetry of `symContent` (e.g. read `slot0` alone) and this breaks.
Quantified over ALL updates. -/
theorem flip_sameMessage (u : Update) : sameMessage u u.flip := by
  unfold sameMessage Experiments.Common.Projection.sameShadow receiver Update.symContent Update.flip
  show u.slot0 + u.slot1 = u.slot1 + u.slot0
  omega

/-- FALSIFIABLE: the twist of the flip is the NEGATION of the original twist — so flipping really
DOES change the antisymmetric residue. This pins that `sameMessage` is NOT trivially everywhere true:
the unrecordable residue genuinely differs. ∀ over all updates. -/
theorem flip_negates_twist (u : Update) : u.flip.twist = - u.twist := by
  unfold Update.flip Update.twist
  omega

/-- FALSIFIABLE: if two updates have DIFFERENT symmetric content, they are NOT the same message.
This is the "load-bearing" direction — the symmetric shadow is exactly the discriminator. ∀-quantified;
drop the hypothesis and it is false. -/
theorem differentContent_notSameMessage (u v : Update)
    (h : u.symContent ≠ v.symContent) : ¬ sameMessage u v := by
  unfold sameMessage Experiments.Common.Projection.sameShadow receiver
  exact h

-- ---------------------------------------------------------------------------
-- The canonical transmission: a pure antisymmetric twist (a "curl-only" update).
-- ---------------------------------------------------------------------------

/-- A purely-symmetric update (the readable part): both slots equal. -/
def pureSymmetric : Update := { slot0 := 3, slot1 := 3 }

/-- A purely-antisymmetric update (the unrecordable twist): the curl-only signal. Its symmetric
content is `0`, so the receiver sees NOTHING — yet its twist is nonzero. -/
def pureTwist : Update := { slot0 := 5, slot1 := -5 }

/-- The curl-only signal is invisible to the receiver: same shadow as the silent (zero) update. -/
def silent : Update := { slot0 := 0, slot1 := 0 }

theorem curl_is_unrecordable : sameMessage pureTwist silent := by decide

theorem curl_is_nonzero : pureTwist.twist = 10 := by decide

-- ---------------------------------------------------------------------------
-- THE CLAIM (content-bearing). The LOAD-BEARING conjunct is the harness coupling:
-- `receiver.sameShadow pureTwist silent` — a `Projection.sameShadow` proposition. A
-- rename/regression of `Projection.sameShadow` in the harness breaks THIS build.
-- ---------------------------------------------------------------------------

/-- The claim, in honest parts:
* (effect) the purely-antisymmetric "curl" signal is UNRECORDABLE — it shares the silent update's
  shadow under the symmetric receiver (`Projection.sameShadow`, the harness coupling); and
* (non-vacuity) that very signal carries a NONZERO twist — so something real was sent that the
  channel could not say; and
* (discrimination) a different symmetric content really is a different message. -/
def claimStatement : Prop :=
  receiver.sameShadow pureTwist silent ∧
    pureTwist.twist ≠ 0 ∧
    ¬ sameMessage pureSymmetric silent

def claim : Experiments.Common.Claim :=
  { tag := Experiments.Common.ClaimTag.smoothShadowAnalogy
    statement := claimStatement }

/-- COUPLING (HARNESS, `Projection.sameShadow`): the first conjunct is literally a
`Experiments.Common.Projection.sameShadow` proposition built from `receiver`. It is discharged here
by `curl_is_unrecordable` (which unfolds to that projection equality), so breaking the harness's
`Projection`/`sameShadow` API breaks this proof term. -/
theorem claim_holds : claim.statement := by
  refine ⟨curl_is_unrecordable, ?_, ?_⟩
  · decide
  · unfold sameMessage Experiments.Common.Projection.sameShadow receiver
    decide

theorem ceiling :
    claim.tag = Experiments.Common.ClaimTag.smoothShadowAnalogy := by
  rfl

-- ---------------------------------------------------------------------------
-- A computable run + a non-vacuous exported Experiment, with a proved bridge.
-- ---------------------------------------------------------------------------

structure Setup where
  sent : Update
  reference : Update

/-- The run computes whether the two updates are the same message (decidable instance above). -/
def run (s : Setup) : Bool := decide (sameMessage s.sent s.reference)

def experiment : Experiments.Common.Experiment Setup Bool :=
  { tag := claim.tag
    run := run
    claim := fun s => sameMessage s.sent s.reference }

theorem run_iff_claim (s : Setup) :
    run s = true ↔ experiment.claim s := by
  simp only [run, experiment, decide_eq_true_iff]

def canonicalSetup : Setup := { sent := pureTwist, reference := silent }

#eval run canonicalSetup                                  -- expect: true  (curl unrecordable)
#eval run { canonicalSetup with reference := pureSymmetric } -- expect: false (different shadow)

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

#print axioms claim_holds
#eval decide (sameMessage pureSymmetric silent)           -- expect: false (load-bearing: lemma is not vacuous)

end Experiments.TheMessageEffect
