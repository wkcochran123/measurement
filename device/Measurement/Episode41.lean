import Measurement.Episode40

set_option maxHeartbeats 4000000
set_option maxRecDepth 1000
set_option allowUnsafeReducibility true

namespace Measurement

/-
__EPISODE 41__: _Mathematics Without an Instrument_

Episode40 grounded the whole ladder: `Rung3` climbs `Fact` to `INFERRED`.  But
the top witness, `rung3Inferred`, is `noncomputable` -- it exists as a proof term
yet carries no executable realizer.  That is the per-witness shadow of a sharper
distinction:

  mathematical existence  ≠  physical realizability.

This episode names the boundary.  An invariant is *physically modeled* by an
apparatus class when some apparatus in the class realizes it from finite counter
readings; it is *metaphysical relative to that class* when none can.  The
distinction is not absolute -- a stronger apparatus may realize tomorrow what is
obstructed today -- so it is always relative to an apparatus class.

The chain the apparatus must survive is exactly the ladder of Episodes 1-15:

  distinguishability -> measurement -> counter construction -> second variation
  -> SPD/Galerkin realization -> weak residual -> kernel integration.

Stated formally:
* `ApparatusRealizesInvariant` / `PhysicallyModeled` / `MetaphysicalRelativeTo`.
* `Obstruction` is the certificate that every apparatus in the class fails, and
  `obstruction_implies_metaphysical` discharges it.
* `EvenApparatus` is the discrete curvature obstruction (closed loops carry even
  parity); `odd_invariant_metaphysical` shows an odd invariant has no witness in
  it -- mathematics without an instrument.
* `metaphysical_is_relative` shows the same invariant `1` IS realized by a richer
  class, so metaphysicality is relative, not eternal.
* `groundInvariant_physical` ties it back: the universe kernel's ground invariant
  (the zero activity's energy, `= 0`) is realizable, hence physical.

Residue left:
The strong form -- quantifying over *every* apparatus the universe kernel admits
-- needs the obstruction sourced from a genuine `CurvatureObstruction` (the loop
that will not close, Ch. 9 strain).  Parity is its smallest shadow.
-/

/-- An apparatus turns finite counter readings into an invariant value. -/
structure Apparatus where
  evaluate : List Nat -> Nat

/-- The apparatus realizes the invariant if some finite counter configuration
evaluates to it.  This is the constructive witness whose absence Lean otherwise
only hints at by stamping a definition `noncomputable`. -/
def Apparatus.Realizes (a : Apparatus) (inv : Nat) : Prop :=
  ∃ counters, a.evaluate counters = inv

abbrev ApparatusClass := Apparatus -> Prop

/-- Physically modeled: some apparatus in the class realizes the invariant. -/
def PhysicallyModeled (C : ApparatusClass) (inv : Nat) : Prop :=
  ∃ a, C a ∧ a.Realizes inv

/-- Metaphysical relative to a class: no apparatus in it realizes the invariant.
The math is sound; it simply has no instrument here. -/
def MetaphysicalRelativeTo (C : ApparatusClass) (inv : Nat) : Prop :=
  ¬ PhysicallyModeled C inv

/-- An obstruction certificate: a direct proof that every apparatus in the class
fails to realize the invariant. -/
def Obstruction (C : ApparatusClass) (inv : Nat) : Prop :=
  ∀ a, C a -> ¬ a.Realizes inv

/-- The hard boundary: an obstruction makes the invariant metaphysical relative
to the class.  `no apparatus -> no physical model`. -/
theorem obstruction_implies_metaphysical {C : ApparatusClass} {inv : Nat}
    (h : Obstruction C inv) : MetaphysicalRelativeTo C inv := by
  intro hpm
  obtain ⟨a, hC, hr⟩ := hpm
  exact h a hC hr

/-- Monotonicity: a larger apparatus class realizes everything a smaller one
does (`hCD : C ⊆ D`). -/
theorem physicallyModeled_mono {C D : ApparatusClass} {inv : Nat}
    (hCD : ∀ a, C a -> D a) (h : PhysicallyModeled C inv) :
    PhysicallyModeled D inv := by
  obtain ⟨a, hC, hr⟩ := h
  exact ⟨a, hCD a hC, hr⟩

/-- Antitonicity: if the larger class cannot realize the invariant, neither can
any smaller class.  The backbone of obstruction hierarchies -- an obstruction at
a permissive class descends to every subclass. -/
theorem metaphysical_antitone {C D : ApparatusClass} {inv : Nat}
    (hCD : ∀ a, C a -> D a) (h : MetaphysicalRelativeTo D inv) :
    MetaphysicalRelativeTo C inv := by
  intro hCphys
  exact h (physicallyModeled_mono hCD hCphys)

/-- The discrete curvature obstruction: an apparatus class that can only read
even invariants -- the parity shadow of a loop that must close. -/
def EvenApparatus : ApparatusClass :=
  fun a => ∀ counters, ∃ k, a.evaluate counters = 2 * k

theorem odd_is_obstructed : Obstruction EvenApparatus 1 := by
  intro a ha hr
  obtain ⟨counters, hc⟩ := hr
  obtain ⟨k, hk⟩ := ha counters
  omega

/-- An odd invariant is metaphysical relative to the even-parity apparatus:
it exists in the mathematics, but no even-reading instrument witnesses it. -/
theorem odd_invariant_metaphysical : MetaphysicalRelativeTo EvenApparatus 1 :=
  obstruction_implies_metaphysical odd_is_obstructed

/-- The maximal *logical* apparatus class: every evaluator, unconstrained.
NOTE: this is a comparison class, not a physical/laboratory apparatus class.  It
witnesses the *relativity* of metaphysicality, not realizability in any
instrument.  Relative to `AllApparatus` everything is "physical" precisely
because the class is unconstrained -- which is why the meaningful question is
realizability relative to the *universe-kernel* apparatus class, not this one. -/
def AllApparatus : ApparatusClass := fun _ => True

/-- The constant apparatus reads `n` from any counters. -/
def constApparatus (n : Nat) : Apparatus := { evaluate := fun _ => n }

/-- The maximal logical class realizes every invariant, via the constant
apparatus.  This is exactly what makes `AllApparatus` the comparison ceiling:
nothing is metaphysical relative to it, so it cannot be the physical class. -/
theorem allApparatus_realizes_every_invariant (inv : Nat) :
    PhysicallyModeled AllApparatus inv := by
  refine ⟨constApparatus inv, trivial, ?_⟩
  exact ⟨[], rfl⟩

theorem one_physical_for_all : PhysicallyModeled AllApparatus 1 :=
  allApparatus_realizes_every_invariant 1

/-- Metaphysicality is relative, not eternal: the same invariant `1` is
obstructed for the even-parity class yet realized by a richer one. -/
theorem metaphysical_is_relative :
    MetaphysicalRelativeTo EvenApparatus 1 ∧ PhysicallyModeled AllApparatus 1 :=
  ⟨odd_invariant_metaphysical, one_physical_for_all⟩

/-- The invariant an apparatus must realize, drawn from the universe kernel
(Episode39): the conserved energy of an activity. -/
def kernelInvariant (k : UniverseKernel) (x : k.spd.form.V) : Nat :=
  k.invariant x

/-- The universe kernel's ground invariant is physical: the zero activity
carries energy `0`, which an apparatus realizes.  The coercive bottom of the
kernel is on the physical side of the boundary. -/
theorem groundInvariant_physical :
    PhysicallyModeled AllApparatus
      (kernelInvariant threeRungUniverse threeRungUniverse.spd.form.zero) := by
  have h :
      kernelInvariant threeRungUniverse threeRungUniverse.spd.form.zero = 0 :=
    UniverseKernel.invariant_zero threeRungUniverse
  rw [h]
  exact ⟨constApparatus 0, trivial, ⟨[], rfl⟩⟩

end Measurement
