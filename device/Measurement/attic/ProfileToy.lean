import Measurement.Formalization.Epiphany

/-!
# ProfileToy: the Boolean profile diagnostic model (sidelined)

This file is **not** the main formalization. It carries the Boolean-profile
content from the first draft, which is now understood to be a diagnostic
toy model rather than the project's actual claim.

The real cascade is a serial production grammar (`Grammar.lean`,
`Cost.lean`, `Herbrand.lean`, `Irredundance.lean`, `Minimality.lean`). The
36 gates are **not** independent coordinates in a `Bool^36` cube; they are
ordered formation stages. Treating them as a finite Boolean basis produces
a true theorem (Stone-Weierstrass-flavored DNF closure on `Bool^36`) that
doesn't say what the project actually says.

This file is kept as a record of that detour. It may be useful as:

- a sanity check on the gate count (the count theorem also lives here);
- a contrast that makes the serial-grammar pivot easier to motivate;
- a place to retire dead-ends without losing the formal content.

Do not cite the theorems in this file as the basis-gauge thesis. Cite
`Grammar.lean` and `Minimality.lean` instead.

## Contents (sidelined)

- `GateProfile` — `Gate → Bool` (toy coordinate basis).
- `Gate.probe` — per-gate Boolean observation on a `FullCascadeObject`.
- `GateSet`, `allGates`, `GateSet.Contains`.
- `GeneratedProperty`, `InGeneratedClosure`.
- `FrameworkMeasurable`.
- `generated_property_measurable` — soundness (proved).
- `framework_measurable_generated` — toy completeness (proved by collapse
  to the single all-true profile).
- `SameProfile`, `SeparatesProfiles`, `allGates_separates`.
- `IrredundantOnProfiles`, `allGates_irredundant_profiles` (proved).
-/

namespace Measurement.Formalization

/-! ## Profiles (toy model) -/

/-- A Boolean profile over the 36 gates. **Toy model**: this treats the
gates as independent coordinates, which is wrong. The real cascade is
serial. See `Grammar.lean`. -/
abbrev GateProfile := Gate → Bool

/-- Per-gate Boolean observation on a cascade object. For a `FullCascadeObject`
every probe returns `true` (every typeclass instance is present). Stage 5b
would need partial-cascade objects to get non-constant probes; the pivot
abandons that approach. -/
def Gate.probe (_g : Gate) (_O : FullCascadeObject) : Bool := true

/-- Profile of a cascade object via per-gate probes. -/
def FullCascadeObject.probeProfile (O : FullCascadeObject) : GateProfile :=
  fun g => Gate.probe g O

/-! ## Gate sets (toy model) -/

abbrev GateSet := Gate → Bool

def allGates : GateSet := fun _ => true

def GateSet.Contains (S : GateSet) (g : Gate) : Prop :=
  S g = true

/-! ## Generated Boolean algebra (toy model) -/

inductive GeneratedProperty (S : GateSet) :
    (FullCascadeObject → Prop) → Prop
  | probe (g : Gate) (h : GateSet.Contains S g) :
      GeneratedProperty S (fun O => Gate.probe g O = true)
  | top :
      GeneratedProperty S (fun _ => True)
  | bot :
      GeneratedProperty S (fun _ => False)
  | not {P : FullCascadeObject → Prop} :
      GeneratedProperty S P →
      GeneratedProperty S (fun O => ¬ P O)
  | and {P Q : FullCascadeObject → Prop} :
      GeneratedProperty S P →
      GeneratedProperty S Q →
      GeneratedProperty S (fun O => P O ∧ Q O)
  | or {P Q : FullCascadeObject → Prop} :
      GeneratedProperty S P →
      GeneratedProperty S Q →
      GeneratedProperty S (fun O => P O ∨ Q O)

def InGeneratedClosure (S : GateSet) (P : FullCascadeObject → Prop) : Prop :=
  ∃ Q, GeneratedProperty S Q ∧ ∀ O, P O ↔ Q O

def FrameworkMeasurable (P : FullCascadeObject → Prop) : Prop :=
  ∃ Q : GateProfile → Prop,
    ∀ O, P O ↔ Q (FullCascadeObject.probeProfile O)

/-- Soundness on the toy: generated ⇒ measurable. -/
theorem generated_property_measurable
    {S : GateSet} {P : FullCascadeObject → Prop}
    (h : GeneratedProperty S P) :
    FrameworkMeasurable P := by
  induction h with
  | probe g _ =>
      refine ⟨fun π => π g = true, fun _ => ?_⟩
      exact Iff.rfl
  | top =>
      exact ⟨fun _ => True, fun _ => Iff.rfl⟩
  | bot =>
      exact ⟨fun _ => False, fun _ => Iff.rfl⟩
  | not _ ih =>
      obtain ⟨Q, hQ⟩ := ih
      refine ⟨fun π => ¬ Q π, fun O => ?_⟩
      exact ⟨fun hnotP hQπ => hnotP ((hQ O).mpr hQπ),
             fun hnotQ hP => hnotQ ((hQ O).mp hP)⟩
  | and _ _ ihP ihQ =>
      obtain ⟨QP, hQP⟩ := ihP
      obtain ⟨QQ, hQQ⟩ := ihQ
      refine ⟨fun π => QP π ∧ QQ π, fun O => ?_⟩
      exact ⟨fun ⟨hP, hQ⟩ => ⟨(hQP O).mp hP, (hQQ O).mp hQ⟩,
             fun ⟨hP, hQ⟩ => ⟨(hQP O).mpr hP, (hQQ O).mpr hQ⟩⟩
  | or _ _ ihP ihQ =>
      obtain ⟨QP, hQP⟩ := ihP
      obtain ⟨QQ, hQQ⟩ := ihQ
      refine ⟨fun π => QP π ∨ QQ π, fun O => ?_⟩
      refine ⟨fun h => h.elim ?_ ?_, fun h => h.elim ?_ ?_⟩
      · intro hP; exact Or.inl ((hQP O).mp hP)
      · intro hQ; exact Or.inr ((hQQ O).mp hQ)
      · intro hQP'; exact Or.inl ((hQP O).mpr hQP')
      · intro hQQ'; exact Or.inr ((hQQ O).mpr hQQ')

/-- Completeness on the toy: measurable ⇒ generated. In this retired model,
every full cascade object has the same all-true profile, so every measurable
predicate is either constantly true or constantly false on the available
objects. -/
theorem framework_measurable_generated
    (P : FullCascadeObject → Prop)
    (h : FrameworkMeasurable P) :
    InGeneratedClosure allGates P := by
  rcases h with ⟨Q, hQ⟩
  by_cases hbase : Q (fun _ => true : GateProfile)
  · refine ⟨fun _ => True, GeneratedProperty.top, ?_⟩
    intro O
    have hPO : P O ↔ Q (fun _ => true : GateProfile) := by
      simpa [FullCascadeObject.probeProfile, Gate.probe] using hQ O
    exact ⟨fun _ => True.intro, fun _ => hPO.mpr hbase⟩
  · refine ⟨fun _ => False, GeneratedProperty.bot, ?_⟩
    intro O
    have hPO : P O ↔ Q (fun _ => true : GateProfile) := by
      simpa [FullCascadeObject.probeProfile, Gate.probe] using hQ O
    exact ⟨fun hP => hbase (hPO.mp hP), fun hFalse => False.elim hFalse⟩

/-! ## Profile separation (sidelined) -/

def SameProfile (p1 p2 : GateProfile) : Prop :=
  ∀ g : Gate, p1 g = p2 g

def SeparatesProfiles (S : GateSet) : Prop :=
  ∀ p1 p2 : GateProfile,
    ¬ SameProfile p1 p2 →
    ∃ g, GateSet.Contains S g ∧ p1 g ≠ p2 g

theorem allGates_separates : SeparatesProfiles allGates := by
  intro p1 p2 hne
  classical
  have hdiff : ∃ g, p1 g ≠ p2 g := by
    apply Classical.byContradiction
    intro hnone
    apply hne
    intro g
    apply Classical.byContradiction
    intro hg
    exact hnone ⟨g, hg⟩
  rcases hdiff with ⟨g, hg⟩
  exact ⟨g, rfl, hg⟩

/-! ## Profile irredundance (sidelined) -/

def GateProfile.flip (g : Gate) (p : GateProfile) : GateProfile :=
  fun h => if h = g then ! p h else p h

def IrredundantOnProfiles (S : GateSet) : Prop :=
  ∀ g, GateSet.Contains S g →
    ∃ p1 p2 : GateProfile,
      (∀ h, h ≠ g → p1 h = p2 h) ∧ p1 g ≠ p2 g

theorem allGates_irredundant_profiles : IrredundantOnProfiles allGates := by
  intro g _
  refine
    ⟨ fun h => if h = g then true  else false
    , fun h => if h = g then false else false
    , ?_
    , ?_ ⟩
  · intro h hne
    simp [hne]
  · simp

end Measurement.Formalization
