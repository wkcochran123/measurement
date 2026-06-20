import Experiments.Common

/-!
# The Malus Effect — polarization termination

Source: `instrument/chapters/05.tex:430`, `ph:polarization-termination`.

## Physics (modelled finitely)
A beam passes a linear polarizer; every surviving photon is aligned to that axis. A second
polarizer is introduced at a relative angle. The transmission obeys Malus's law,
`I = I₀ · cos²(Δθ)`. When the second axis is **crossed** — orthogonal to the first, a quarter
turn — `cos²(90°) = 0`: **no photon passes**. There is no new distinguishable event, the count
of counts cannot increase, and the record ends.

We model the polarizer axis as a slot on a finite ring of `quarters * 4` slots (so a quarter
turn = `quarters` slots, the orthogonal direction is exact and integer). Transmission past the
analyzer is the boolean Malus gate `transmits`: a photon survives iff the relative axis is NOT a
quarter turn. The terminated beam carries an empty `Ledger`, whose count is therefore bounded by
zero (the harness `Counting.boundedBy` — the load-bearing coupling: the record cannot grow).

## NOT claimed
That `cos²` is *derived* — `transmits` is a finite boolean gate keyed to the orthogonal slot, not
a continuous intensity law; only the **crossed-axis zero** is modelled, not the full `cos²`
profile at intermediate angles. No photon statistics, no partial transmission, no quantum
measurement collapse, no rate. **Claim ceiling:** an `inadmissibilityNoGo` — crossed polarizers
forbid any surviving photon, so the post-analyzer ledger is empty and its count is bounded by 0.
-/

namespace Experiments.TheMalusEffect

/-- A polarizer: an axis slot on a ring whose total size is `quarters * 4`. A quarter turn is
`quarters` slots, so the orthogonal (crossed) direction is the exact integer `axis + quarters`. -/
structure Polarizer where
  axis : Nat
  quarters : Nat
deriving DecidableEq, Repr

/-- A photon already aligned to some axis slot. -/
structure Photon where
  axis : Nat
deriving DecidableEq, Repr

/-- The standard apparatus: a 90-slots-per-quarter ring (360 slots total), first axis at slot 0. -/
def defaultPolarizer : Polarizer := { axis := 0, quarters := 90 }

namespace Polarizer

/-- The ring size: four quarter turns. -/
def ring (a : Polarizer) : Nat := a.quarters * 4

/-- The second axis is **crossed** with the first when it is exactly a quarter turn away
(mod the ring): `(axis₁ + quarters) % ring = axis₂ % ring`. -/
def crossed (a : Polarizer) (b : Polarizer) : Prop :=
  (a.axis + a.quarters) % a.ring = b.axis % a.ring

/-- The Malus gate: a photon aligned to axis `a` is transmitted past analyzer `b` iff `b` is NOT
crossed with `a`. (Finite boolean stand-in for `cos²(Δθ) > 0`; only the orthogonal zero is
modelled.) A photon's own axis defines the first polarizer slot. -/
def transmits (a : Polarizer) (b : Polarizer) (p : Photon) : Prop :=
  p.axis % a.ring = a.axis % a.ring ∧ ¬ a.crossed b

instance (a b : Polarizer) : Decidable (a.crossed b) := by
  unfold crossed; exact inferInstance
instance (a b : Polarizer) (p : Photon) : Decidable (a.transmits b p) := by
  unfold transmits; exact inferInstance

end Polarizer

-- ---------------------------------------------------------------------------
-- FALSIFIABLE lemmas: each pins a conjunct, so the gate is load-bearing.
-- Drop the hypothesis and the conclusion breaks.
-- ---------------------------------------------------------------------------

/-- THE NO-GO: a photon aligned to the first axis is **never** transmitted past a crossed
analyzer. Quantified over ALL polarizers and aligned photons. Drop `h : a.crossed b` and this is
false (an aligned photon DOES pass an uncrossed analyzer — see `aligned_passes_uncrossed`). -/
theorem crossed_blocks_all
    (a b : Polarizer) (p : Photon) (h : a.crossed b) : ¬ a.transmits b p :=
  fun ht => ht.2 h

/-- Alignment to the first axis is necessary: a photon NOT aligned to `a` never transmits
(pins the FIRST conjunct of `transmits`). -/
theorem misaligned_blocks
    (a b : Polarizer) (p : Photon) (h : p.axis % a.ring ≠ a.axis % a.ring) :
    ¬ a.transmits b p :=
  fun ht => h ht.1

/-- The witness the no-go needs: an aligned photon DOES pass an UNcrossed analyzer. This is the
falsifier — it shows `crossed_blocks_all` is not vacuous (transmission is possible in general,
only the crossed case is blocked). -/
theorem aligned_passes_uncrossed
    (a b : Polarizer) (p : Photon)
    (hAligned : p.axis % a.ring = a.axis % a.ring) (hOpen : ¬ a.crossed b) :
    a.transmits b p :=
  ⟨hAligned, hOpen⟩

-- ---------------------------------------------------------------------------
-- The canonical crossed configuration and the TERMINATED ledger.
-- ---------------------------------------------------------------------------

/-- The first analyzer axis (= the photon source axis), slot 0. -/
def firstAxis : Polarizer := defaultPolarizer

/-- The crossed second analyzer: a quarter turn (90 slots) away, axis 90. -/
def crossedAxis : Polarizer := { axis := 90, quarters := 90 }

/-- A photon aligned to the first axis. -/
def alignedPhoton : Photon := { axis := 0 }

/-- The second analyzer really is crossed with the first (concrete check). -/
theorem default_is_crossed : firstAxis.crossed crossedAxis := by decide

/-- The aligned photon really is blocked by the crossed analyzer (concrete check). -/
theorem aligned_blocked_by_crossed : ¬ firstAxis.transmits crossedAxis alignedPhoton := by decide

/-- The ledger of photons SURVIVING the crossed analyzer is empty — the record ends. -/
def survivors : Experiments.Common.Ledger Photon :=
  Experiments.Common.Ledger.empty

/-- The terminated record has count zero. -/
theorem survivors_count : survivors.count = 0 := by
  rfl

-- ---------------------------------------------------------------------------
-- THE CLAIM (content-bearing; the counting conjunct is the harness theorem).
-- ---------------------------------------------------------------------------

/-- The claim, in honest parts:
* (no-go) the aligned photon is blocked by the crossed analyzer — proved by construction here;
* (universality) the crossed analyzer blocks EVERY photon — the falsifiable `∀` lemma;
* (termination = bounded record) the surviving ledger's count is bounded by `0`
  (`Experiments.Common.Counting.boundedBy` — the harness coupling: a counting-limit theorem, so a
  regression in the harness `Ledger`/`Counting` API breaks THIS build). -/
def claimStatement : Prop :=
  (¬ firstAxis.transmits crossedAxis alignedPhoton) ∧
    (∀ p : Photon, ¬ firstAxis.transmits crossedAxis p) ∧
    Experiments.Common.Counting.boundedBy survivors 0

def claim : Experiments.Common.Claim :=
  { tag := Experiments.Common.ClaimTag.inadmissibilityNoGo
    statement := claimStatement }

theorem claim_holds : claim.statement :=
  ⟨aligned_blocked_by_crossed,
    fun p => crossed_blocks_all firstAxis crossedAxis p default_is_crossed,
    Experiments.Common.Counting.boundedBy_of_eq survivors_count⟩

/-- The tag is an honest ceiling: a no-go, nothing more. -/
theorem ceiling : claim.tag = Experiments.Common.ClaimTag.inadmissibilityNoGo := rfl

-- ---------------------------------------------------------------------------
-- A computable run + a NON-vacuous Experiment.claim, with a proved bridge.
-- ---------------------------------------------------------------------------

structure Setup where
  first : Polarizer
  second : Polarizer
  probe : Photon

/-- The run computes whether the probe photon transmits — `true` means the record could grow,
`false` means it terminates. -/
def run (s : Setup) : Bool := decide (s.first.transmits s.second s.probe)

def experiment : Experiments.Common.Experiment Setup Bool :=
  { tag := claim.tag
    run := run
    claim := fun s => s.first.transmits s.second s.probe }

theorem run_iff_claim (s : Setup) :
    run s = true ↔ experiment.claim s := by
  simp only [run, experiment, decide_eq_true_iff]

def crossedSetup : Setup := { first := firstAxis, second := crossedAxis, probe := alignedPhoton }
def openSetup : Setup := { first := firstAxis, second := firstAxis, probe := alignedPhoton }

#eval run crossedSetup                                 -- expect: false (terminated)
#eval run openSetup                                    -- expect: true  (aligned, uncrossed)
#print axioms claim_holds                              -- ambient propext/Quot.sound footprint
#eval decide (firstAxis.transmits crossedAxis alignedPhoton)  -- expect: false (no-go is load-bearing)

instance (setup : Setup) : Decidable (experiment.claim setup) := by
  unfold experiment Experiments.Common.Experiment.claim; exact inferInstance

/-- Bring a minimal device next to this experiment: it records whether the exported claim fires. -/
def deviceNear (setup : Setup) : Bool :=
  decide (experiment.claim setup)

theorem deviceNear_detects_claim (setup : Setup) :
    deviceNear setup = true ↔ experiment.claim setup := by
  simp only [deviceNear, decide_eq_true_iff]

def triangulation : Experiments.Common.Triangulation Setup Bool :=
  { experiment := experiment
    device := deviceNear
    detects := deviceNear_detects_claim }

end Experiments.TheMalusEffect
