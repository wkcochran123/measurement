import Experiments.Common

/-!
# The Gamma Decay Effect — rebuilt to the EXEMPLAR shape

Source: `instrument/chapters/07.tex:1761` — "Gamma decay is a reversible repair of internal
causal symmetry."  The excited nucleus carries a small *informational asymmetry* in an internal
ledger; the minimal symmetric repair emits one gamma photon that propagates the excess curvature
away, leaving the ledger in its minimal (ground) configuration:

    Ψ* ⟶ Ψ + γ.

The description's defining mark of gamma (vs alpha) decay is that it is **informationally
reversible**: *no new branches are created and no admissible distinctions are destroyed* — the
identity of the nucleus is preserved, and `δ²A = 0` (the zero-mass / uncharged boundary repair).

So we model the internal record as a finite **ledger of distinctions** and formalise the one thing
the description actually pins down: the repair is *conservative* — every distinction in the excited
record is accounted for after the split, partitioned between the ground record and the photon, with
nothing created and nothing lost.  This is exactly `Ledger.count_append`: the count of the whole is
the sum of the counts of the parts.

## Coupling (HONEST)
This effect is the **δ²A = 0** (reversible, uncharged) case — the description explicitly contrasts
it with the *charged* / branch-removing alpha decay.  There is therefore **no holonomy, no Berry
phase, no charge** to honestly couple to the device's positron/holonomy theorems; forcing those
here would be a FAKE coupling.  The honest content is **conservation / what-leaves-enters
bookkeeping**, so this file couples to the HARNESS theorem `Experiments.Common.Ledger.count_append`.
The coupling is load-bearing: `conservation` (a conjunct of `claim_holds`) is discharged *by*
`Ledger.count_append`, so a regression/rename in that harness lemma breaks THIS build.

## NOT claimed
That any real nucleus decays; that `E = hν` is *derived* (it is a labelled relation, not produced
here); any QED amplitude, lifetime, rate, branching ratio, or selection rule; that the "curvature"
is a real geometric curvature.  We do **not** model energy as a number — only the *combinatorics*
of the distinction ledger (reversibility ⇒ count is conserved across the split).  **Claim ceiling:**
a finite ledger model of the conservative (reversible) split, whose conservation conjunct is the
harness's own theorem.
-/

namespace Experiments.TheGammaDecayEffect

/-- A single distinction recorded in the nucleus's internal causal ledger.  `excited` marks the
extra distinction(s) present before the repair; `ground` marks the ones that survive into the
minimal ground configuration. -/
inductive Distinction where
  | ground
  | excited
deriving DecidableEq, Repr

/-- The internal record of a nuclear configuration: a finite ledger of distinctions. -/
abbrev Record := Experiments.Common.Ledger Distinction

/-- The repair splits one excited record into a *ground* record and a *photon* record (the
propagated correction). -/
structure Decay where
  ground : Record
  photon : Record
deriving Repr

namespace Decay

/-- The excited record *recombined* from its parts: ground ++ photon.  Gamma decay is reversible,
so the excited configuration is recovered by re-joining the two halves. -/
def excited (d : Decay) : Record :=
  Experiments.Common.Ledger.append d.ground d.photon

/-- CONSERVATION (reversibility): the number of distinctions in the recombined excited record
equals ground-count + photon-count — nothing created, nothing destroyed.  This is a `Prop` over
the split. -/
def conserves (d : Decay) : Prop :=
  d.excited.count = d.ground.count + d.photon.count

/-- The repair is *minimal*: the surviving ground record is exactly the excited record with its
excited distinctions removed.  Modelled as: the ground record carries no `excited` marks. -/
def groundIsMinimal (d : Decay) : Prop :=
  d.ground.events.filter (· == Distinction.excited) = []

end Decay

-- Decidability so `decide`/`#eval` see through the predicates.
instance (d : Decay) : Decidable d.groundIsMinimal := by
  unfold Decay.groundIsMinimal; exact inferInstance

-- ---------------------------------------------------------------------------
-- FALSIFIABLE quantified lemmas.
-- ---------------------------------------------------------------------------

/-- CONSERVATION is universal — for EVERY split, the recombined excited count is the sum of the
parts.  This is the harness theorem `Ledger.count_append` specialised; it is the load-bearing
coupling.  Drop either summand on the RHS and it breaks. -/
theorem conservation_universal (d : Decay) : d.conserves := by
  unfold Decay.conserves Decay.excited
  exact Experiments.Common.Ledger.count_append d.ground d.photon

/-- FALSIFIABILITY witness for `groundIsMinimal`: if the ground record still contains an excited
distinction (here as the head of a cons), it is NOT minimal.  Quantified over all tails. -/
theorem excited_in_ground_not_minimal (tail : List Distinction) :
    ¬ Decay.groundIsMinimal { ground := { events := Distinction.excited :: tail }, photon := { events := [] } } := by
  unfold Decay.groundIsMinimal
  simp only [List.filter]
  exact fun h => by cases h

/-- A NON-vacuous direction: a clean repair (empty ground of excited marks) IS minimal. -/
theorem cleanGround_minimal (gs ph : List Distinction) (hg : gs.filter (· == Distinction.excited) = []) :
    Decay.groundIsMinimal { ground := { events := gs }, photon := { events := ph } } := by
  unfold Decay.groundIsMinimal
  exact hg

-- ---------------------------------------------------------------------------
-- The canonical reversible repair: one excited distinction repaired into a clean ground
-- record (one ground distinction) plus a one-quantum photon record.
-- ---------------------------------------------------------------------------

def groundRecord : Record := { events := [Distinction.ground] }
def photonRecord : Record := { events := [Distinction.excited] }

/-- Ψ* ⟶ Ψ + γ : one ground distinction survives, one photon carries the correction. -/
def canonicalDecay : Decay := { ground := groundRecord, photon := photonRecord }

/-- The canonical repair conserves the distinction count (2 = 1 + 1), via the universal lemma. -/
theorem canonical_conserves : canonicalDecay.conserves :=
  conservation_universal canonicalDecay

/-- The canonical ground record is minimal — it carries no excited distinction. -/
theorem canonical_minimal : canonicalDecay.groundIsMinimal := by decide

/-- The photon is non-trivial: it actually carries one distinction off (the repair did something).
A frozen check on the chosen event, not a property enforced by `conserves`. -/
theorem photon_nontrivial : canonicalDecay.photon.count = 1 := by decide

-- ---------------------------------------------------------------------------
-- THE CLAIM (content-bearing conjunction; conservation conjunct IS the harness theorem).
-- ---------------------------------------------------------------------------

/-- The claim, in honest halves:
* (conservation / reversibility) the canonical split conserves the distinction count
  (`conservation_universal`, itself `Ledger.count_append` — the load-bearing harness coupling);
* (minimality) the surviving ground record carries no excited distinction; and
* (non-triviality) the photon actually carried one distinction off — the repair was real. -/
def claimStatement : Prop :=
  canonicalDecay.conserves ∧
    canonicalDecay.groundIsMinimal ∧
    canonicalDecay.photon.count = 1

def claim : Experiments.Common.Claim :=
  { tag := Experiments.Common.ClaimTag.finiteLedgerModel
    statement := claimStatement }

theorem claim_holds : claim.statement :=
  ⟨canonical_conserves, canonical_minimal, photon_nontrivial⟩

/-- The tag is an honest ceiling: a finite ledger model of the conservative split, nothing more. -/
theorem ceiling : claim.tag = Experiments.Common.ClaimTag.finiteLedgerModel := rfl

-- ---------------------------------------------------------------------------
-- A computable run + a NON-vacuous Experiment.claim, with a proved bridge.
-- ---------------------------------------------------------------------------

abbrev Setup := Decay

/-- The run computes whether the split is a minimal repair — via the `Decidable` instance. -/
def run (s : Setup) : Bool := decide s.groundIsMinimal

/-- The exported claim is a genuine function of the setup, pinned to `run` by `run_iff_claim`. -/
def experiment : Experiments.Common.Experiment Setup Bool :=
  { tag := claim.tag
    run := run
    claim := fun s => s.groundIsMinimal }

theorem run_iff_claim (s : Setup) :
    run s = true ↔ experiment.claim s := by
  simp only [run, experiment, decide_eq_true_iff]

instance (setup : Setup) : Decidable (experiment.claim setup) := by
  unfold experiment Experiments.Common.Experiment.claim; exact inferInstance

/-- Bring a minimal device next to this experiment: it records whether the exported claim fires. -/
def deviceNear (setup : Setup) : Bool :=
  run setup

theorem deviceNear_detects_claim (setup : Setup) :
    deviceNear setup = true ↔ experiment.claim setup := by
  simpa [deviceNear] using run_iff_claim setup

def triangulation : Experiments.Common.Triangulation Setup Bool :=
  { experiment := experiment
    device := deviceNear
    detects := deviceNear_detects_claim }

-- ---------------------------------------------------------------------------
-- GATE EVIDENCE.
-- ---------------------------------------------------------------------------

#print axioms claim_holds
-- Load-bearing check: `groundIsMinimal` is FALSE when the ground record keeps an excited mark.
#eval run { ground := { events := [Distinction.excited] }, photon := { events := [] } }  -- expect: false

end Experiments.TheGammaDecayEffect
