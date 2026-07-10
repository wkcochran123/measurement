import Measurement.Episode32

set_option maxHeartbeats 4000000
set_option maxRecDepth 1000
set_option allowUnsafeReducibility true

namespace Measurement

/-
__EPISODE 33__: _The Evaluated Middle_

Episode32 proved that the mixed-coupling route and the second-variation route
produce one logical result, while the timing layer remembers two computational
proof paths.

This episode names the computed middle between two endpoints.  The middle is
not a new truth value.  It is a value evaluated from the endpoints.

Compilation gives existence:
  the declarations below store the witness-producing proof.

Evaluation gives the witness:
  the witness is `middle a c`.

Functionality gives uniqueness:
  the middle cannot drift independently from its endpoints.

If the evaluated middle changes, at least one endpoint changed.

Residue left:
The timing middle is still a measurement of compiler-path residue.  Proof
irrelevance remains the theorem-level equality of the two proof routes.
-/

theorem middle_exists
    {A C B : Type}
    (middle : A -> C -> B)
    (a : A) (c : C) :
    ∃ b, b = middle a c := by
  exact ⟨middle a c, rfl⟩

theorem middle_unique
    {A C B : Type}
    (middle : A -> C -> B)
    (a : A) (c : C) :
    ∃ b, b = middle a c ∧
      forall b', b' = middle a c -> b' = b := by
  refine ⟨middle a c, rfl, ?_⟩
  intro b hb
  exact hb

theorem middle_changed_implies_endpoint_changed
    {A C B : Type}
    (middle : A -> C -> B)
    {a a' : A} {c c' : C}
    (h : middle a c ≠ middle a' c') :
    a ≠ a' ∨ c ≠ c' := by
  classical
  by_cases ha : a = a'
  · right
    intro hc
    apply h
    rw [ha, hc]
  · left
    exact ha

def boolMiddle (a c : Bool) : Bool :=
  a && c

theorem endpoints_true_middle_true
    {a c : Bool}
    (ha : a = true)
    (hc : c = true) :
    boolMiddle a c = true := by
  subst a
  subst c
  rfl

structure CompiledMiddle
    (A C B : Type)
    (middle : A -> C -> B)
    (a : A) (c : C) where
  value : B
  value_eq : value = middle a c
  unique :
    forall b,
      b = middle a c -> b = value

namespace CompiledMiddle

def ofEval
    {A C B : Type}
    (middle : A -> C -> B)
    (a : A) (c : C) :
    CompiledMiddle A C B middle a c where
  value := middle a c
  value_eq := rfl
  unique := by
    intro b hb
    rw [hb]

theorem exists_from_compilation
    {A C B : Type}
    {middle : A -> C -> B}
    {a : A} {c : C}
    (compiled : CompiledMiddle A C B middle a c) :
    ∃ b, b = middle a c := by
  exact ⟨compiled.value, compiled.value_eq⟩

theorem unique_from_compilation
    {A C B : Type}
    {middle : A -> C -> B}
    {a : A} {c : C}
    (compiled : CompiledMiddle A C B middle a c) :
    ∃ b, b = middle a c ∧
      forall b', b' = middle a c -> b' = b := by
  refine ⟨compiled.value, compiled.value_eq, ?_⟩
  exact compiled.unique

end CompiledMiddle

def natAbsDiff (a b : Nat) : Nat :=
  if a <= b then b - a else a - b

structure ProofTimingSnapshot where
  mixed : Nat
  secondVariation : Nat

namespace ProofTimingSnapshot

def middle
    (s : ProofTimingSnapshot) : Nat :=
  natAbsDiff s.mixed s.secondVariation

end ProofTimingSnapshot

theorem timingMiddle_exists
    (s : ProofTimingSnapshot) :
    ∃ b, b = s.middle := by
  exact ⟨s.middle, rfl⟩

theorem timingMiddle_unique
    (s : ProofTimingSnapshot) :
    ∃ b, b = s.middle ∧
      forall b', b' = s.middle -> b' = b := by
  refine ⟨s.middle, rfl, ?_⟩
  intro b hb
  exact hb

theorem timingMiddle_changed_implies_one_route_changed
    (before after : ProofTimingSnapshot)
    (h : before.middle ≠ after.middle) :
    before.mixed ≠ after.mixed ∨
      before.secondVariation ≠ after.secondVariation := by
  by_cases hMixed : before.mixed = after.mixed
  · right
    intro hSecond
    apply h
    unfold ProofTimingSnapshot.middle
    rw [hMixed, hSecond]
  · left
    exact hMixed

def currentProofTimingSnapshot : ProofTimingSnapshot where
  mixed := mixedProofTime
  secondVariation := secondVariationProofTime

theorem currentProofTimingSnapshot_middle_eq_proofTimingResidue :
    currentProofTimingSnapshot.middle = proofTimingResidue := by
  unfold currentProofTimingSnapshot ProofTimingSnapshot.middle
    proofTimingResidue natAbsDiff
  rfl

def compiledProofTimingMiddle :
    CompiledMiddle
      ProofTimingSnapshot
      Unit
      Nat
      (fun s _ => s.middle)
      currentProofTimingSnapshot
      () :=
  CompiledMiddle.ofEval
    (fun s _ => s.middle)
    currentProofTimingSnapshot
    ()

theorem currentTimingMiddle_exists :
    ∃ b, b = proofTimingResidue := by
  refine ⟨currentProofTimingSnapshot.middle, ?_⟩
  exact currentProofTimingSnapshot_middle_eq_proofTimingResidue

theorem currentTimingMiddle_unique :
    ∃ b, b = proofTimingResidue ∧
      forall b', b' = proofTimingResidue -> b' = b := by
  refine ⟨currentProofTimingSnapshot.middle,
    currentProofTimingSnapshot_middle_eq_proofTimingResidue, ?_⟩
  intro b hb
  rw [hb]
  exact Eq.symm currentProofTimingSnapshot_middle_eq_proofTimingResidue

end Measurement
