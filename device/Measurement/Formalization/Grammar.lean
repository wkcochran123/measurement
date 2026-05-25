import Measurement.Formalization.Epiphany

/-!
# Grammar: the serial production system

This file replaces the Boolean-profile model with the correct one: the 36
gates plus `.fact` form a serial BNF/Herbrand-style production grammar.
Derivations begin at `.fact` and progress one stage at a time through
`Stage.next`, terminating at `.inferred`.

The grammar is the central structure. Cost, Herbrand terms, and
irredundance are layered on top of it in later files.

## Contents

- `Step s t` — the immediate-successor relation between stages.
- `Derivation s` — a proof that `s` is reachable from `.fact` via repeated
  `Step` applications.
- `inferred_derivable` — the existence theorem: a derivation reaches
  `.inferred`.
- `Derivation.length` — the number of `Step` applications in a derivation.

The canonical derivation `derivation_inferred` is constructed explicitly as
a 36-step chain from `.fact` to `.inferred`.
-/

namespace Measurement.Formalization

/-! ## Steps -/

/-- A single production step in the serial grammar. `Step s t` holds iff
`Stage.next s = some t`. -/
def Step (s t : Stage) : Prop := Stage.next s = some t

namespace Step

/-- A `Step` from `s` to `t` is uniquely determined by `s`: the successor is
the value of `Stage.next`. -/
theorem unique {s t₁ t₂ : Stage} (h₁ : Step s t₁) (h₂ : Step s t₂) :
    t₁ = t₂ := by
  unfold Step at h₁ h₂
  rw [h₁] at h₂
  exact Option.some.inj h₂

/-- A step from `s` to `t` increments the rank by exactly one.

This is the linearity lemma Codex flagged as a prerequisite for Level 1
irredundance: every step advances the rank by 1, so a derivation of stage
`t` has length `Stage.rank t`. -/
theorem rank_succ {s t : Stage} (h : Step s t) :
    Stage.rank t = Stage.rank s + 1 := by
  cases s <;> (
    unfold Step Stage.next at h
    first
      | (cases h; rfl)
      | nomatch h
  )

/-- A step from `s` to `t` means `s` is the unique immediate predecessor of `t`.

The companion lemma to `Step.unique`: `Stage.next` and `Stage.prev` are
inverses on the chain, so any derivation of a non-initial stage must enter
through its single predecessor. -/
theorem prev_eq {s t : Stage} (h : Step s t) :
    Stage.prev t = some s := by
  cases s <;> (
    unfold Step Stage.next at h
    first
      | (cases h; rfl)
      | nomatch h
  )

/-- The target of any step has positive rank: a step always produces some
stage with rank ≥ 1, never rank 0 (which is `.fact`'s rank). -/
theorem target_rank_pos {s t : Stage} (h : Step s t) : 0 < Stage.rank t := by
  rw [Step.rank_succ h]
  exact Nat.succ_pos _

end Step

/-! ## Derivations -/

/-- A `Derivation s` is a proof that the stage `s` is reachable from `.fact`
by repeated `Step` applications. This is the serial grammar's notion of a
well-formed derivation. -/
inductive Derivation : Stage → Type
  | fact : Derivation .fact
  | step {s t : Stage} : Step s t → Derivation s → Derivation t

namespace Derivation

/-- The length of a derivation: the number of `Step` applications. The
canonical derivation from `.fact` to `.inferred` has length 36. -/
def length {s : Stage} : Derivation s → Nat
  | .fact      => 0
  | .step _ d  => d.length + 1

end Derivation

/-! ## The canonical derivation to `.inferred`

Constructed explicitly as 36 nested `.step rfl` applications. Each `rfl`
discharges the corresponding `Step` premise by reducing
`Stage.next ... = some ...`. -/

/-- The canonical derivation from `.fact` to `.inferred`, 36 steps long. -/
def derivation_inferred : Derivation .inferred :=
  Derivation.step (rfl : Step .compiled       .inferred)        <|
  Derivation.step (rfl : Step .measured       .compiled)        <|
  Derivation.step (rfl : Step .halted         .measured)        <|
  Derivation.step (rfl : Step .logical        .halted)          <|
  Derivation.step (rfl : Step .universal      .logical)         <|
  Derivation.step (rfl : Step .«local»        .universal)       <|
  Derivation.step (rfl : Step .real           .«local»)         <|
  Derivation.step (rfl : Step .witnessed      .real)            <|
  Derivation.step (rfl : Step .truth          .witnessed)       <|
  Derivation.step (rfl : Step .scientific     .truth)           <|
  Derivation.step (rfl : Step .acolyte        .scientific)      <|
  Derivation.step (rfl : Step .propaganda     .acolyte)         <|
  Derivation.step (rfl : Step .bullshit       .propaganda)      <|
  Derivation.step (rfl : Step .finiteElephant .bullshit)        <|
  Derivation.step (rfl : Step .load           .finiteElephant)  <|
  Derivation.step (rfl : Step .scaled         .load)            <|
  Derivation.step (rfl : Step .magnitude      .scaled)          <|
  Derivation.step (rfl : Step .value          .magnitude)       <|
  Derivation.step (rfl : Step .executed       .value)           <|
  Derivation.step (rfl : Step .source         .executed)        <|
  Derivation.step (rfl : Step .gungan         .source)          <|
  Derivation.step (rfl : Step .measurable     .gungan)          <|
  Derivation.step (rfl : Step .present        .measurable)      <|
  Derivation.step (rfl : Step .observed       .present)         <|
  Derivation.step (rfl : Step .comparable     .observed)        <|
  Derivation.step (rfl : Step .physical       .comparable)      <|
  Derivation.step (rfl : Step .representable  .physical)        <|
  Derivation.step (rfl : Step .numeric        .representable)   <|
  Derivation.step (rfl : Step .repeatable     .numeric)         <|
  Derivation.step (rfl : Step .binary         .repeatable)      <|
  Derivation.step (rfl : Step .residue        .binary)          <|
  Derivation.step (rfl : Step .encoded        .residue)         <|
  Derivation.step (rfl : Step .countable      .encoded)         <|
  Derivation.step (rfl : Step .admissible     .countable)       <|
  Derivation.step (rfl : Step .distinguishable .admissible)     <|
  Derivation.step (rfl : Step .fact           .distinguishable) <|
  Derivation.fact

/-! ## The grammar reaches `.inferred` -/

/-- The serial grammar derives `.inferred` from `.fact`. -/
theorem inferred_derivable : Nonempty (Derivation .inferred) :=
  ⟨derivation_inferred⟩

/-- The canonical derivation has length 36. -/
theorem inferred_derivation_length :
    derivation_inferred.length = 36 := by
  decide

end Measurement.Formalization
