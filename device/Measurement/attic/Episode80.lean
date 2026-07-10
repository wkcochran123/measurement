import Measurement.Episode79

set_option maxHeartbeats 4000000
set_option maxRecDepth 1000
set_option allowUnsafeReducibility true

namespace Measurement

/-!
__EPISODE 80__: _How Much Do You Want?_

Episode79 closed the binary-to-inferred tower.  The last remaining move is not
another universe level.  It is the stop rule:

* keep the invariant;
* choose an observer frame;
* choose how much of the tower the reader wants;
* project to that level;
* put anything above that level in the appendix unless it changes a measurable
  prediction, a formal theorem, or a necessary distinction.

So the final answer to recursion is finite and binary: stop here, or ask for
more depth.
-/

/-- The reader frame for an explanation. -/
inductive ObserverFrame where
  | leanReader
  | physicist
  | mathematician
  | philosopher
  | generalTechnicalReader
  | self

/-- The explanation ladder. -/
inductive ExplanationLevel where
  | parable
  | finiteMachine
  | theoremStatement
  | leanConstruction
  | analyticPhysical
  | metaphysicalTopological

namespace ExplanationLevel

/-- Clamp a requested depth to the six-level explanation ladder. -/
def ofDepth : Nat -> ExplanationLevel
  | 0 => .parable
  | 1 => .finiteMachine
  | 2 => .theoremStatement
  | 3 => .leanConstruction
  | 4 => .analyticPhysical
  | _ => .metaphysicalTopological

end ExplanationLevel

/-- The only reasons to climb another universe level in the main argument. -/
inductive ExplanationChange where
  | none
  | measurablePrediction
  | formalTheorem
  | necessaryDistinction

namespace ExplanationChange

/-- No change means stop.  A measurable prediction, formal theorem, or necessary
distinction authorizes continuing. -/
def liftSignal : ExplanationChange -> BoundarySignal
  | .none => BoundarySignal.off
  | .measurablePrediction => BoundarySignal.on
  | .formalTheorem => BoundarySignal.on
  | .necessaryDistinction => BoundarySignal.on

theorem none_liftSignal_off :
    ExplanationChange.none.liftSignal = BoundarySignal.off := rfl

theorem formalTheorem_liftSignal_on :
    ExplanationChange.formalTheorem.liftSignal = BoundarySignal.on := rfl

/-- The proposition that the next level genuinely changes the invariant. -/
def changesInvariant : ExplanationChange -> Prop
  | .none => False
  | .measurablePrediction => True
  | .formalTheorem => True
  | .necessaryDistinction => True

theorem no_change_liftSignal_off {change : ExplanationChange}
    (hNoNewChange : ¬ change.changesInvariant) :
    change.liftSignal = BoundarySignal.off := by
  cases change <;> simp [changesInvariant, liftSignal] at hNoNewChange ⊢

theorem new_boundary_liftSignal_on {change : ExplanationChange}
    (hNewChange : change.changesInvariant) :
    change.liftSignal = BoundarySignal.on := by
  cases change <;> simp [changesInvariant, liftSignal] at hNewChange ⊢

end ExplanationChange

namespace BoundarySignal

/-- Binary negation at the outside-reader layer. -/
def neg : BoundarySignal -> BoundarySignal
  | .off => .on
  | .on => .off

/-- Binary conjunction at the outside-reader layer. -/
def meet : BoundarySignal -> BoundarySignal -> BoundarySignal
  | .on, .on => .on
  | _, _ => .off

/-- Binary disjunction at the outside-reader layer. -/
def join : BoundarySignal -> BoundarySignal -> BoundarySignal
  | .off, .off => .off
  | _, _ => .on

theorem neg_off : neg BoundarySignal.off = BoundarySignal.on := rfl

theorem neg_on : neg BoundarySignal.on = BoundarySignal.off := rfl

/-- De Morgan for the finite on/off carrier:
not (a and b) equals (not a) or (not b). -/
theorem deMorgan_meet (a b : BoundarySignal) :
    neg (meet a b) = join (neg a) (neg b) := by
  cases a <;> cases b <;> rfl

/-- De Morgan for the finite on/off carrier:
not (a or b) equals (not a) and (not b). -/
theorem deMorgan_join (a b : BoundarySignal) :
    neg (join a b) = meet (neg a) (neg b) := by
  cases a <;> cases b <;> rfl

end BoundarySignal

/-- Constructive De Morgan: denying a disjunction is the same as denying both
sides. -/
theorem prop_deMorgan_not_or (P Q : Prop) :
    ¬ (P ∨ Q) ↔ ¬ P ∧ ¬ Q := by
  constructor
  · intro h
    exact ⟨fun hp => h (Or.inl hp), fun hq => h (Or.inr hq)⟩
  · intro h hpq
    cases hpq with
    | inl hp => exact h.left hp
    | inr hq => exact h.right hq

/-- De Morgan, given a decision oracle for `P`: denying a conjunction yields a
denied side.  The supplied `Decidable P` is the oracle -- it end-runs the
undecidable case split that would otherwise call for choice. -/
theorem prop_deMorgan_not_and (P Q : Prop) [Decidable P] :
    ¬ (P ∧ Q) ↔ ¬ P ∨ ¬ Q := by
  constructor
  · intro h
    by_cases hp : P
    · exact Or.inr (fun hq => h ⟨hp, hq⟩)
    · exact Or.inl hp
  · intro h hpq
    cases h with
    | inl hnp => exact hnp hpq.left
    | inr hnq => exact hnq hpq.right

/-- The invariant that must survive every simplification: the final inferred
close from Episode79. -/
def inferredCloseInvariant : Prop :=
  truthBinaryToInferredTower.first = BinaryToInferredRung.binary ∧
    truthBinaryToInferredTower.last = BinaryToInferredRung.inferred ∧
    secondGodelProofLanguageSentence.source = godelProofLanguageTarget ∧
    secondGodelProofLanguageSentence.target =
      Closure.inferred.{0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0}
        godelProofLanguageFact
        godelProofLanguageFact
        godelProofLanguageOrigin
        godelProofLanguageOutput
        godelProofLanguageRelation
        godelProofLanguageTarget ∧
    secondGodelProofLanguageSentence.encoded =
      secondGodelProofLanguageSentence.target ∧
    secondGodelProofLanguageSentence.says =
      Closure.le.{0, 0, 0, 0}
        secondGodelProofLanguageSentence.source
        secondGodelProofLanguageSentence.target ∧
    zeroStrainResidue.fact = Fact.FALSE ∧
    zeroStrainResidue.strain = 0 ∧
    zeroStrainResidue.signal = BoundarySignal.off ∧
    Distinguished.trueRead SECOND_DISTINGUISHED_GODEL_SENTENCE ≠
      Distinguished.falseRead SECOND_DISTINGUISHED_GODEL_SENTENCE ∧
    SECOND_DISTINGUISHED_GODEL_SENTENCE.obstruction.errorCode = -1 ∧
      SECOND_DISTINGUISHED_GODEL_SENTENCE.outside = BoundarySignal.on

theorem inferredCloseInvariant_holds :
    inferredCloseInvariant :=
  inferred_closed_for_the_last_time

/-- The requested explanation projection.  It is allowed to stop exactly where
the observer asked, unless the next level contains a measurable, formal, or
necessary distinction. -/
structure ExplanationProjection where
  invariant : Prop
  projectedLevel : ExplanationLevel
  appendixStartsAt : Nat
  nextChangesInvariant : Prop
  stopSignal : BoundarySignal

/-- The recursion stop rule as a finite selector. -/
structure RecursionStopRule extends ExplanationProjection where
  observer : ObserverFrame
  requestedDepth : Nat
  invariant_survives : invariant
  projection_matches_depth :
    projectedLevel = ExplanationLevel.ofDepth requestedDepth
  appendix_after_request :
    appendixStartsAt = requestedDepth + 1
  nextChange : ExplanationChange
  nextChangesInvariant_reads_change :
    nextChangesInvariant = nextChange.changesInvariant
  stopSignal_reads_change : stopSignal = nextChange.liftSignal
  stop_now :
    ¬ nextChangesInvariant -> stopSignal = BoundarySignal.off
  continue_if_new_boundary :
    nextChangesInvariant -> stopSignal = BoundarySignal.on

/-- Duh: binary is built.  The remaining parameters are how much explanation the
observer wants before the appendix begins, and whether the next level genuinely
changes the invariant. -/
noncomputable def HOW_MUCH_DO_YOU_WANT_WITH_CHANGE
    (observer : ObserverFrame) (depth : Nat)
    (nextChange : ExplanationChange) :
    RecursionStopRule where
  invariant := inferredCloseInvariant
  projectedLevel := ExplanationLevel.ofDepth depth
  appendixStartsAt := depth + 1
  nextChangesInvariant := nextChange.changesInvariant
  stopSignal := nextChange.liftSignal
  observer := observer
  requestedDepth := depth
  invariant_survives := inferredCloseInvariant_holds
  projection_matches_depth := rfl
  appendix_after_request := rfl
  nextChange := nextChange
  nextChangesInvariant_reads_change := rfl
  stopSignal_reads_change := rfl
  stop_now := by
    intro hNoNewChange
    exact ExplanationChange.no_change_liftSignal_off hNoNewChange
  continue_if_new_boundary := by
    intro hNewChange
    exact ExplanationChange.new_boundary_liftSignal_on hNewChange

/-- The no-new-content projection: the observer asked for a depth, and the next
main-text level adds no measurable/formal/necessary boundary. -/
noncomputable def HOW_MUCH_DO_YOU_WANT
    (observer : ObserverFrame) (depth : Nat) :
    RecursionStopRule :=
  HOW_MUCH_DO_YOU_WANT_WITH_CHANGE observer depth ExplanationChange.none

/-- If a new formal theorem is supplied, the binary gate authorizes another
main-text level. -/
theorem formal_theorem_authorizes_more :
    ExplanationChange.formalTheorem.liftSignal = BoundarySignal.on :=
  ExplanationChange.formalTheorem_liftSignal_on

/-- The final recursion receipt: the invariant survives, the projection is
exactly the requested depth, and without a new measurable/formal/necessary
change the binary stop signal is off. -/
theorem requested_depth_projection_receipt
    (observer : ObserverFrame) (depth : Nat)
    (hNoNewChange :
      ¬ (HOW_MUCH_DO_YOU_WANT observer depth).nextChangesInvariant) :
    (HOW_MUCH_DO_YOU_WANT observer depth).invariant ∧
      (HOW_MUCH_DO_YOU_WANT observer depth).projectedLevel =
        ExplanationLevel.ofDepth depth ∧
      (HOW_MUCH_DO_YOU_WANT observer depth).appendixStartsAt =
        depth + 1 ∧
      (HOW_MUCH_DO_YOU_WANT observer depth).stopSignal =
        BoundarySignal.off :=
  ⟨(HOW_MUCH_DO_YOU_WANT observer depth).invariant_survives,
    (HOW_MUCH_DO_YOU_WANT observer depth).projection_matches_depth,
    (HOW_MUCH_DO_YOU_WANT observer depth).appendix_after_request,
    (HOW_MUCH_DO_YOU_WANT observer depth).stop_now hNoNewChange⟩

/-- If the next level introduces a new measurable/formal/necessary distinction,
the recursion boundary turns on and the material belongs in the next frame, not
silently in the current explanation. -/
theorem how_much_do_you_want_continue_if_new_boundary
    (observer : ObserverFrame) (depth : Nat)
    (nextChange : ExplanationChange)
    (hNewChange :
      (HOW_MUCH_DO_YOU_WANT_WITH_CHANGE observer depth nextChange).nextChangesInvariant) :
    (HOW_MUCH_DO_YOU_WANT_WITH_CHANGE observer depth nextChange).stopSignal =
      BoundarySignal.on :=
  (HOW_MUCH_DO_YOU_WANT_WITH_CHANGE observer depth nextChange).continue_if_new_boundary
    hNewChange

/-- The neon sign: the default no-new-content projection closes exactly where
the observer asked. -/
theorem duh_we_made_binary_how_much_do_you_want
    (observer : ObserverFrame) (depth : Nat) :
    (HOW_MUCH_DO_YOU_WANT observer depth).invariant ∧
      (HOW_MUCH_DO_YOU_WANT observer depth).projectedLevel =
        ExplanationLevel.ofDepth depth ∧
      (HOW_MUCH_DO_YOU_WANT observer depth).appendixStartsAt =
        depth + 1 ∧
      (HOW_MUCH_DO_YOU_WANT observer depth).stopSignal =
        BoundarySignal.off :=
  requested_depth_projection_receipt observer depth (by
    intro hNewChange
    cases hNewChange)

/-
The standing record.
-/

#print axioms ExplanationChange.none_liftSignal_off
#print axioms BoundarySignal.deMorgan_meet
#print axioms BoundarySignal.deMorgan_join
#print axioms prop_deMorgan_not_or
#print axioms prop_deMorgan_not_and
#print axioms formal_theorem_authorizes_more
#print axioms inferredCloseInvariant_holds
#print axioms HOW_MUCH_DO_YOU_WANT
#print axioms requested_depth_projection_receipt
#print axioms how_much_do_you_want_continue_if_new_boundary
#print axioms duh_we_made_binary_how_much_do_you_want

end Measurement
