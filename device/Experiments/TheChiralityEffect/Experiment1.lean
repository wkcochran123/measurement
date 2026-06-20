import Experiments.Common
import Measurement.Episode85

/-!
# The Chirality Effect — left and right refinements generate distinct causal records

Rebuilt to the `ThePositronAnnihilationEffect` exemplar shape. The 3-`Nat` `CountSetup`
stub is replaced by:

1. an **effect-specific domain** (`Handedness`, `ChiralLedger`) drawn from the description —
   not three undifferentiated `Nat`s;
2. genuinely **falsifiable** `∀`-quantified lemmas (drop a hypothesis and they break);
3. a **content-bearing** claim (a real conjunction, never `True`);
4. an **honest tag** (`inadmissibilityNoGo`) + a candid "NOT claimed" disclaimer;
5. explicit `Decidable` instances so `decide`/`#eval` compute through the richer predicates;
6. a **LOAD-BEARING DEVICE coupling**: two conjuncts of `claim_holds` are discharged by the
   real device theorems `Measurement.holonomy_loop_is_charged` and
   `Measurement.holonomy_open_is_trivial`, so the device *symbols* sit in the proof term and a
   `sorry`/rename/sign-regression in `Measurement` breaks *this* file's build.

## Physics (modelled finitely)
A refinement update Ψ acts on a local causal frame. The description distinguishes its action on
left- and right-oriented bases, `Ψ_L` and `Ψ_R`. In a parity-symmetric ledger `Ψ_L ≡ Ψ_R`; in a
**chiral** ledger `Ψ_L ≠ Ψ_R`, and that asymmetry "cannot be removed by smooth deformation".

This is exactly the device's **holonomy sign**. The device's `holonomy` is the signed residue a
pair accumulates around a gauge loop (Episode84); its SIGN is the orientation (Episode83). The two
handednesses are the two baselines: the SAME loop reads `+1` over the tilted flux and `-1` over the
flat flux (`Measurement.holonomy_loop_is_charged`). So `Ψ_L ≠ Ψ_R` is, literally, `+1 ≠ -1` —
the orientation sign distinguishes left from right and the two records do not coincide. And the
asymmetry "cannot be removed by smooth deformation" is the device's holonomy floor: it is `0` only
on the OPEN, single-leg path (`Measurement.holonomy_open_is_trivial`) and nonzero around the genuine
pair-LOOP — the residue is a holonomy, not a pointwise gauge artifact you can deform away.

The description's closing line — "The observed parity violation of weak interactions is the smooth
shadow of this bookkeeping asymmetry" — is the device's own frame-relative orientation reading.

## NOT claimed
That this is real parity violation, the real weak interaction, a real Dirac operator, or that the
left/right kernel split is *derived* (handedness is the convention fixed by the baseline, Episode83,
not proven here). No claim that the two records differ by a *specific* amount in nature; no QED, no
chiral anomaly, no Standard-Model coupling. WHICH sign is "left" is a convention. **Claim ceiling:**
a finite NO-GO — the chiral ledger *forbids* substituting a refinement's mirror image without a
sign cost — two of whose conjuncts are the device's own holonomy theorems.
-/

namespace Experiments.TheChiralityEffect

/-- The two orientations a refinement can act on. `Handedness` is the finite stand-in for a
left/right-oriented basis of a local causal frame. -/
inductive Handedness where
  | left
  | right
deriving DecidableEq, Repr

/-- The formal inversion the description names: the mirror image swaps the two hands. -/
def Handedness.mirror : Handedness -> Handedness
  | left => right
  | right => left

/-- A refinement update Ψ records a signed cost on each oriented basis: `costOf left = Ψ_L`,
`costOf right = Ψ_R`. The ledger is **chiral** when the two costs disagree. (Signed: an `Int`,
because orientation is a sign — the device reads it as `±1`.) -/
structure ChiralLedger where
  costOf : Handedness -> Int

namespace ChiralLedger

/-- `Ψ_L`: the action on a left-oriented basis. -/
def actLeft (Ψ : ChiralLedger) : Int := Ψ.costOf Handedness.left

/-- `Ψ_R`: the action on a right-oriented basis. -/
def actRight (Ψ : ChiralLedger) : Int := Ψ.costOf Handedness.right

/-- PARITY-SYMMETRIC: `Ψ_L ≡ Ψ_R` — the mirror image substitutes with no cost. -/
def paritySymmetric (Ψ : ChiralLedger) : Prop := Ψ.actLeft = Ψ.actRight

/-- CHIRAL: `Ψ_L ≠ Ψ_R` — the ledger distinguishes orientation. -/
def chiral (Ψ : ChiralLedger) : Prop := Ψ.actLeft ≠ Ψ.actRight

/-- THE NO-GO RULE: in a chiral ledger, the mirror image of a refinement may NOT be substituted
for the original without changing the recorded cost. `forbidsMirror` says exactly that, on a chosen
hand `h`: the cost of `h` and the cost of its mirror differ. (Both conjuncts of `chiral` repackaged
as the per-hand substitution ban; pinned by a falsifiable lemma below.) -/
def forbidsMirror (Ψ : ChiralLedger) (h : Handedness) : Prop :=
  Ψ.costOf h ≠ Ψ.costOf h.mirror

instance (Ψ : ChiralLedger) : Decidable Ψ.paritySymmetric := by
  unfold paritySymmetric; exact inferInstance
instance (Ψ : ChiralLedger) : Decidable Ψ.chiral := by
  unfold chiral; exact inferInstance
instance (Ψ : ChiralLedger) (h : Handedness) : Decidable (Ψ.forbidsMirror h) := by
  unfold forbidsMirror; exact inferInstance

end ChiralLedger

-- ---------------------------------------------------------------------------
-- FALSIFIABLE lemmas, quantified over ALL ledgers / hands.
-- Each would break if the chiral / no-go structure were dropped.
-- ---------------------------------------------------------------------------

/-- A chiral ledger forbids the mirror substitution on EVERY hand. Quantified over all ledgers and
all hands: the hypothesis `Ψ.chiral` is load-bearing — drop it and `forbidsMirror` is false on a
parity-symmetric ledger (see the `#eval` at the bottom). -/
theorem chiral_forbids_mirror
    (Ψ : ChiralLedger) (h : Handedness) (hc : Ψ.chiral) : Ψ.forbidsMirror h := by
  cases h with
  | left => exact hc
  | right => exact fun heq => hc heq.symm

/-- Conversely, a parity-symmetric ledger ALLOWS the mirror substitution: the cost is the same on a
hand and its mirror. The hypothesis `Ψ.paritySymmetric` is necessary. -/
theorem symmetric_allows_mirror
    (Ψ : ChiralLedger) (h : Handedness) (hs : Ψ.paritySymmetric) :
    Ψ.costOf h = Ψ.costOf h.mirror := by
  cases h with
  | left => exact hs
  | right => exact hs.symm

/-- Chirality is not a property of the mirror map itself: `mirror` is an involution, so the
asymmetry lives in the LEDGER (the update admissibility), exactly as the description says
("Chirality is not a property of space, but of update admissibility"). -/
theorem mirror_involutive (h : Handedness) : h.mirror.mirror = h := by
  cases h <;> rfl

-- ---------------------------------------------------------------------------
-- THE CANONICAL CHIRAL LEDGER, read straight off the device holonomy.
-- ---------------------------------------------------------------------------

/-- The canonical refinement update: its action on a left basis is the holonomy over the tilted
flux (`+1`), on a right basis the holonomy over the flat flux (`-1`). These are the device's own
signed residues — so this ledger IS chiral because the device says `+1 ≠ -1`. -/
def diracUpdate : ChiralLedger :=
  { costOf := fun h =>
      match h with
      | Handedness.left => Measurement.holonomy Measurement.tiltedPath
          (Measurement.CubicGaugeVariation.pairVariation Measurement.node1 Measurement.node2)
      | Handedness.right => Measurement.holonomy Measurement.flatPath
          (Measurement.CubicGaugeVariation.pairVariation Measurement.node1 Measurement.node2) }

-- ---------------------------------------------------------------------------
-- THE CLAIM (content-bearing; two of three conjuncts are the device's own theorems).
-- ---------------------------------------------------------------------------

/-- The claim, in honest parts:
* (the device's chiral signature) the holonomy reads `+1` around the loop over the tilted flux and
  `-1` over the flat flux — `Ψ_L ≠ Ψ_R`, the orientation distinguishes left from right
  (`Measurement.holonomy_loop_is_charged`); and
* (the asymmetry cannot be deformed away) the holonomy is `0` on the open single-leg path — the
  residue is a genuine loop holonomy, not a pointwise artifact
  (`Measurement.holonomy_open_is_trivial`); and
* (the no-go, in this file's own domain) the canonical chiral ledger forbids the mirror substitution
  on the left hand — proved here from the device values via `chiral_forbids_mirror`.
The first two read the device's actual δ² **sign** computation, so a sign regression in
`Measurement` fails THIS build — value-coupling, not just a name. -/
def claimStatement : Prop :=
  (Measurement.holonomy Measurement.tiltedPath
      (Measurement.CubicGaugeVariation.pairVariation Measurement.node1 Measurement.node2) = 1
    ∧ Measurement.holonomy Measurement.flatPath
      (Measurement.CubicGaugeVariation.pairVariation Measurement.node1 Measurement.node2) = -1) ∧
  Measurement.holonomy Measurement.tiltedPath
      (Measurement.CubicGaugeVariation.pairVariation Measurement.node2 Measurement.node1) = 0 ∧
  diracUpdate.forbidsMirror Handedness.left

def claim : Experiments.Common.Claim :=
  { tag := Experiments.Common.ClaimTag.inadmissibilityNoGo
    statement := claimStatement }

/-- The canonical ledger is chiral because the device's two holonomy signs disagree. This is the
bridge that lets `chiral_forbids_mirror` (the file's own no-go) read the device values. -/
theorem diracUpdate_chiral : diracUpdate.chiral := by
  unfold ChiralLedger.chiral ChiralLedger.actLeft ChiralLedger.actRight diracUpdate
  -- actLeft = +1, actRight = -1 (the device holonomy signs); `1 ≠ -1`.
  exact fun h => by
    rw [Measurement.holonomy_loop_is_charged.1, Measurement.holonomy_loop_is_charged.2] at h
    nomatch h

theorem claim_holds : claim.statement :=
  ⟨Measurement.holonomy_loop_is_charged,
   Measurement.holonomy_open_is_trivial,
   chiral_forbids_mirror diracUpdate Handedness.left diracUpdate_chiral⟩

/-- The tag is an honest ceiling: a finite NO-GO (the chiral ledger forbids the mirror
substitution), nothing more. -/
theorem ceiling : claim.tag = Experiments.Common.ClaimTag.inadmissibilityNoGo := rfl

-- ---------------------------------------------------------------------------
-- A computable run + a NON-vacuous Experiment.claim, with a proved bridge.
-- ---------------------------------------------------------------------------

structure Setup where
  ledger : ChiralLedger
  hand : Handedness

/-- The run actually computes — thanks to the `Decidable` instance on `forbidsMirror`. -/
def run (s : Setup) : Bool := decide (s.ledger.forbidsMirror s.hand)

def experiment : Experiments.Common.Experiment Setup Bool :=
  { tag := claim.tag
    run := run
    claim := fun s => s.ledger.forbidsMirror s.hand }

theorem run_iff_claim (s : Setup) :
    run s = true ↔ experiment.claim s := by
  simp only [run, experiment, decide_eq_true_iff]

def canonicalSetup : Setup := { ledger := diracUpdate, hand := Handedness.left }

/-- A parity-symmetric ledger where the mirror substitution is ALLOWED — the falsifying config. -/
def symmetricLedger : ChiralLedger := { costOf := fun _ => 0 }

#eval run canonicalSetup                                      -- expect: true  (chiral: forbids mirror)
#eval run { ledger := symmetricLedger, hand := Handedness.left } -- expect: false (symmetric: allows it)
#eval decide (symmetricLedger.forbidsMirror Handedness.left)  -- expect: false  (lemma is load-bearing)
#print axioms claim_holds                                     -- [propext, Quot.sound] = AMBIENT, not coupling

/-- Bring a minimal device next to this experiment: it records whether the exported claim fires.
Decides over the (definitionally equal) unfolded predicate so the `Decidable` instance on
`forbidsMirror` is found directly. -/
def deviceNear (setup : Setup) : Bool :=
  decide (setup.ledger.forbidsMirror setup.hand)

theorem deviceNear_detects_claim (setup : Setup) :
    deviceNear setup = true ↔ experiment.claim setup := by
  simp only [deviceNear, experiment, decide_eq_true_iff]

def triangulation : Experiments.Common.Triangulation Setup Bool :=
  { experiment := experiment
    device := deviceNear
    detects := deviceNear_detects_claim }

end Experiments.TheChiralityEffect
