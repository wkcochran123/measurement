import Measurement.Episode59

set_option maxHeartbeats 4000000
set_option maxRecDepth 1000
set_option allowUnsafeReducibility true

namespace Measurement

/-
__EPISODE 60__: _Counting to Three_

The old `Natural` type is the count. Its successor constructor carries a
`Number` label, so we first make that label as the number `0.succ.succ`.
Then we define the local successor, local addition, and enough numeral
elaboration for `Natural` to say:

  * 1 + 1 = 2
  * 1 + 2 = 3
  * 1 + 1 + 1 = 3

For these truth-phase numerals, the equalities are definitional.
-/

namespace Number

/-- The truth-phase successor used to build the `Natural` constructor label. -/
def succ (n : Number) : Number :=
  .one Fact.Truth n

/-- The truth-phase numeral embedding used only for small constructor labels. -/
def ofNat : Nat -> Number
  | 0 => .zero Fact.Truth
  | n + 1 => succ (ofNat n)

instance instOfNat (n : Nat) : OfNat Number n where
  ofNat := ofNat n

end Number

namespace Natural

/-- The `Number` label used by one `Natural` successor step. This is the
number the user pointed to: `0.succ.succ`. -/
def successorNumber : Number :=
  (0 : Number).succ.succ

theorem successorNumber_eq_zero_succ_succ :
    successorNumber = (0 : Number).succ.succ := rfl

/-- The local successor on `Natural`. -/
def succ (n : Natural) : Natural :=
  .number Fact.Truth successorNumber n

/-- Truth-phase numerals for `Natural`. -/
def ofNat : Nat -> Natural
  | 0 => .zero Fact.Truth
  | n + 1 => succ (ofNat n)

instance instOfNat (n : Nat) : OfNat Natural n where
  ofNat := ofNat n

/-- Addition by peeling the left `Natural` input. -/
def add : Natural -> Natural -> Natural
  | .zero _, right => right
  | .number phase label left, right => .number phase label (add left right)

instance instAdd : Add Natural where
  add := add

/-- The canonical naturals are exactly the ones generated from zero by the
local successor whose label is `0.succ.succ`. -/
inductive Canonical : Natural -> Prop where
  | zero : Canonical (0 : Natural)
  | succ {n : Natural} : Canonical n -> Canonical (succ n)

theorem canonical_ofNat : forall n : Nat, Canonical (ofNat n)
  | 0 => Canonical.zero
  | n + 1 => Canonical.succ (canonical_ofNat n)

/-- Proof by induction on the canonical `Natural` spine. This is the induction
principle for the `succ` definition above, not for arbitrary labelled
`Natural.number` values. -/
theorem induction_on_canonical
    {motive : Natural -> Prop}
    (zero : motive (0 : Natural))
    (step : forall n : Natural, Canonical n -> motive n -> motive (succ n))
    {n : Natural} (hn : Canonical n) :
    motive n := by
  induction hn with
  | zero => exact zero
  | succ hn ih => exact step _ hn ih

theorem induction_on_ofNat
    {motive : Natural -> Prop}
    (zero : motive (0 : Natural))
    (step : forall n : Natural, Canonical n -> motive n -> motive (succ n))
    (n : Nat) :
    motive (ofNat n) :=
  induction_on_canonical zero step (canonical_ofNat n)

theorem succ_succ (n : Natural) :
    succ (succ n) = (2 : Natural) + n := rfl

theorem succ_one_eq_two :
    succ (1 : Natural) = (2 : Natural) := by
  simpa using succ_succ (0 : Natural)

theorem succ_two_eq_three :
    succ (2 : Natural) = (3 : Natural) := by
  simpa using succ_succ (1 : Natural)

theorem succ_certificate_lift :
    succ (succ (1 : Natural)) = succ (2 : Natural) :=
  congrArg succ succ_one_eq_two

theorem one_add_one_eq_two :
    (1 : Natural) + (1 : Natural) = (2 : Natural) := rfl

theorem one_add_two_eq_three :
    (1 : Natural) + (2 : Natural) = (3 : Natural) := rfl

theorem one_add_one_add_one_eq_three :
    (1 : Natural) + (1 : Natural) + (1 : Natural) = (3 : Natural) := rfl

#print axioms successorNumber_eq_zero_succ_succ
#print axioms canonical_ofNat
#print axioms induction_on_canonical
#print axioms induction_on_ofNat
#print axioms succ_succ
#print axioms succ_one_eq_two
#print axioms succ_two_eq_three
#print axioms succ_certificate_lift
#print axioms one_add_one_eq_two
#print axioms one_add_two_eq_three
#print axioms one_add_one_add_one_eq_three

end Natural

end Measurement
