/-
Measurement/Chapter2.lean
-/

import Measurement.Chapter1

namespace Measurement


/- --------------------------------------------------------
-/


/- --------------------------------------------------------
-/

abbrev PAIR (Symbol: Type i) := Symbol × Symbol

class DECOMPOSED
    (Symbol: Type i)
    (Whole: Symbol)
    (Part_1: Symbol)
    (Part_2: NEXT Symbol)

    (NextDecomposition: Symbol → NEXT (PAIR (NEXT Symbol)) → Bool)    -- This checks to see if the next Whole is decomposed.
    (Decompose: Symbol → PROCESS (PAIR (NEXT Symbol)) → Bool)
    where

  before? : (Symbol → NEXT (PAIR (NEXT Symbol)) → Bool) := NextDecomposition
  decompose? : (Symbol → PROCESS (PAIR (NEXT Symbol)) → Bool) := Decompose

namespace PRECEDES

variable {Symbol_1 : Type i}
         {Symbol_2 : Type i}
         {s1 : Symbol_1}
         {s2 : Symbol_2}
         {Before : Symbol_1 → NEXT Symbol_2 → Bool}
         {Concatenated : (Symbol_1 × Symbol_2) → Bool}
         [relation: PRECEDES Symbol_1 Symbol_2 s1 s2 Before Concatenated]

def concatenated
    (a: Symbol_1)
    (b: Symbol_2)
      : Bool :=
  relation.concatenated? (a, b)

def before
    (a: Symbol_1)
    (b: Symbol_2)
      : Bool :=
  relation.before? a b

-- Can these things be concantenated?  Interesting question..
def concatenate?
    (a: Symbol_1)
    (b: Symbol_2)
      : Bool :=
  relation.concatenated? (a, b) && relation.before? a b

def correlate
    (a: Symbol_1)
    (b: Symbol_2)
      : Bool :=
  relation.concatenated? (a, b) && !relation.before? a b

end PRECEDES

inductive DecompositionOf
    (Symbol: Type i)    -- This is the symbol being decomposed.
    (Whole: Symbol)     -- This is the whole symbol that is being decomposed.
    (Part_1: Symbol)    -- First part.
    (Part_2: Symbol)    -- Second part.

    (s: Symbol)
    (s1: Part_1)         -- <- The Tape distinguishes them as before and after
    (s2: NEXT Part_2)    -- <- The approximate arrow of time due to the
                           -- Tape being a process that takes time the first time.
    (Before: Symbol_1 → NEXT Symbol_2 → Bool)
    (Concatenated: (Symbol_1 × Symbol_2) → Bool)

/- --------------------------------------------------------
-/


class ORDERING
    (Symbol: Type i)
    (Name: Symbol)
    (Value: Symbol)
    (FeatureName: Symbol → NEXT Symbol → Bool)
    (FeatureRelation: (Symbol × Symbol) → Bool)
    [PRECEDES Symbol Name Value FeatureName FeatureRelation]
    where

  name? : Symbol → NEXT Symbol → Bool := FeatureName
  less_than?: (Symbol × Symbol) → Bool := FeatureRelation


namespace ORDERING
variable {Symbol : Type i}
         {Name : Symbol}
         {Value : Symbol}
         {FeatureName : Symbol → NEXT Symbol → Bool}
         {FeatureRelation : (Symbol × Symbol) → Bool}
         [related: PRECEDES Symbol Name Value FeatureName FeatureRelation]
         [ordering: ORDERING Symbol Name Value FeatureName FeatureRelation]

def name
    (name: Symbol)
    (word: Symbol)
      : Bool :=
  ordering.name? name word

def less_than
    (a: Symbol)
    (b: Symbol)
      : Bool :=
  ordering.less_than? (a, b)

def value
    (name: Symbol)
    (value: Symbol)
      : Bool :=
  related.same? name value

def inside
    (a: Symbol)
    (b: Symbol)
      : Bool :=
  related.related? (a, b) && related.same? a b

end ORDERING

inductive OrderingOf
    (Symbol: Type i)
    (Name: Symbol)
    (Value: Symbol)
    (FeatureName: Symbol → NEXT Symbol → Bool)
    (FeatureRelation: (Symbol × Symbol) → Bool)
    [PRECEDES Symbol Name Value FeatureName FeatureRelation]
    [ORDERING Symbol Name Value FeatureName FeatureRelation]
  | nil : OrderingOf Symbol Name Value FeatureName FeatureRelation
  | cons: Symbol →
          Symbol →
          PRECEDES Symbol Name Value FeatureName FeatureRelation →
          ORDERING Symbol Name Value FeatureName FeatureRelation →
          OrderingOf Symbol Name Value FeatureName FeatureRelation →
          OrderingOf Symbol Name Value FeatureName FeatureRelation








/- --------------------------------------------------------
-/

class DECOMPOSABLE
    (Symbol: Type i)
    (Whole: Symbol)
    (Parts: (Symbol × Symbol))
    (Feature: Symbol → NEXT Symbol → Bool)
    (Relation: (Symbol × Symbol) → Bool)
    (Decompose:  (NEXT Symbol × NEXT Symbol) → PROCESS (NEXT Symbol) → PROCESS (PROCESS (NEXT Symbol)) → Bool)
    [PRECEDES Symbol Whole Whole Feature Relation]
    [ORDERING Symbol Whole Whole Feature Relation]
    where

  left?: Symbol → NEXT Symbol → Bool
  right?: Symbol → NEXT Symbol → Bool
  whole? : Symbol → Bool

namespace DECOMPOSABLE
variable {Symbol : Type i}
         {Whole : Symbol}
         {Parts : (Symbol×Symbol)}
         {Feature : Symbol → NEXT Symbol → Bool}
         {Relation : (Symbol × Symbol) → Bool}
         {Decompose :  (NEXT Symbol × NEXT Symbol) → PROCESS (NEXT Symbol) → PROCESS (PROCESS (NEXT Symbol)) → Bool}
         [related: PRECEDES Symbol Whole Whole Feature Relation]
         [ordering: ORDERING Symbol Whole Whole Feature Relation]
         [decomposable: DECOMPOSABLE Symbol Whole Parts Feature Relation Decompose]

def left
    (whole: Symbol)
    (part: NEXT Symbol)
      : Bool :=
  decomposable.left? whole part

def right
    (whole: Symbol)
    (part: NEXT Symbol)
      : Bool :=
  decomposable.right? whole part

def whole
      : Bool :=
   decomposable.whole? Whole


end DECOMPOSABLE


inductive DecompositionOf
    (Symbol: Type i)
    (Whole: Symbol)
    (Parts: (Symbol×Symbol))
    (Feature: Symbol → NEXT Symbol → Bool)
    (Relation: (Symbol × Symbol) → Bool)
    (Decompose:  (NEXT Symbol × NEXT Symbol) → PROCESS (NEXT Symbol) → PROCESS (PROCESS (NEXT Symbol)) → Bool)
    [PRECEDES Symbol Whole Whole Feature Relation]
    [ORDERING Symbol Whole Whole Feature Relation]
    [DECOMPOSABLE Symbol Whole Parts Feature Relation Decompose]
  | nil : DecompositionOf Symbol Whole Parts Feature Relation Decompose
  | cons: Symbol →
          NEXT Symbol →
          PRECEDES Symbol Whole Whole Feature Relation →
          ORDERING Symbol Whole Whole Feature Relation →
          DECOMPOSABLE Symbol Whole Parts Feature Relation Decompose →
          DecompositionOf Symbol Whole Parts Feature Relation Decompose →
          DecompositionOf Symbol Whole Parts Feature Relation Decompose








/- --------------------------------------------------------
-/

class NAMED
    (Symbol: Type i)
    (Name: Symbol)
    (Feature: Symbol → NEXT Symbol → Bool)
    [PRECEDES Symbol Name Name Feature (λ _ => false)]
    where

  name? : Symbol → NEXT Symbol → Bool := Feature



namespace NAMED
variable {Symbol : Type i}
         {Name : Symbol}
         {Feature : Symbol → NEXT Symbol → Bool}
         [related: PRECEDES Symbol Name Name Feature (λ _ => false)]
         [named: NAMED Symbol Name Feature]

-- How much wood could a woodchuck chuck?
def name
    (name: Symbol)
    (word: Symbol)
      : Bool :=
  named.name? name word

inductive DictionaryOf
    (Symbol: Type i)
    (Name: Symbol)
    (Feature: Symbol → NEXT Symbol → Bool)
    [PRECEDES Symbol Name Name Feature (λ _ => false)]
    [NAMED Symbol Name Feature]
  | nil : DictionaryOf Symbol Name Feature
  | cons: Symbol →
          NAMED Symbol Name Feature →
          DictionaryOf Symbol Name Feature →
          DictionaryOf Symbol Name Feature

end NAMED









/- --------------------------------------------------------
-/


class STATEFUL
    (Symbol: Type i)
    (Instruction: Symbol)
    (Answer_State: NEXT (NEXT Symbol×NEXT Symbol))
    (NextResult: Symbol → NEXT Symbol → Bool)
    (Next_Answer_State: (NEXT Symbol×NEXT Symbol) → PROCESS (NEXT Symbol×NEXT Symbol) → Bool)
    [PRECEDES Symbol Instruction (NEXT Symbol×NEXT Symbol)))]
    where

  state? : Symbol → NEXT Symbol → Bool := Change
  next_state? : Symbol -> PROCESS Symbol -> Bool := NextState


namespace STATEFUL
variable {Symbol : Type i}
         {Name : Symbol}
         {State : Symbol}
         {Change : Symbol → NEXT Symbol → Bool}
         {NextState : Symbol → PROCESS Symbol → Bool}
         [related_name: PRECEDES Symbol Name Name Change (λ _ => false)]
         [related_state: PRECEDES Symbol State State Change (λ _ => true)]
         [named: NAMED Symbol Name Change]

def state
    (name: Symbol)
    (state: Symbol)
      : Bool :=
  related_name.same? name state

def next_state
    (state: Symbol)
    (next_state: Symbol)
      : Bool :=
  related_state.same? state next_state

end STATEFUL

inductive Tape
    (Symbol: Type i)
    (Name: Symbol)
    (State: Symbol)
    (Change: Symbol → NEXT Symbol → Bool)
    (NextState: Symbol → PROCESS Symbol → Bool)
    [PRECEDES Symbol Name Name Change (λ _ => false)]
    [PRECEDES Symbol State State Change (λ _ => true)]
    [NAMED Symbol Name Change]
    [STATEFUL Symbol Name State Change NextState]
  | nil : Tape Symbol Name State Change NextState
  | cons: Symbol →
          Symbol →
          PRECEDES Symbol Name Name Change (λ _ => false) →
          PRECEDES Symbol State State Change (λ _ => true) →
          NAMED Symbol Name Change →
          Tape Symbol Name State Change NextState →
          Tape Symbol Name State Change NextState








/- --------------------------------------------------------
-/


class CARRIED
    (Symbol:    Type i)


    (Particle:  Symbol)
    (Amplitude: Symbol)
    (Frequency: Symbol)
    (Wave: (NEXT Symbol × NEXT Symbol))
    (Carrier: (NEXT Symbol×NEXT Symbol) → Bool)
    (Wavefunction: Symbol × (NEXT Symbol×NEXT Symbol))
    (Detector: (NEXT Symbol) × (NEXT Symbol) → PROCESS (NEXT Symbol))

    (Æther: NEXT Symbol → NEXT (NEXT Symbol) → Bool) -- Notice the Æther is metaphysical and does not require observation.
    (Elliptic: Symbol → NEXT Symbol → Bool)
    (Hyperbolic: (NEXT (NEXT Symbol)×NEXT (NEXT Symbol)) → PROCESS (NEXT (NEXT Symbol)) → PROCESS (PROCESS (NEXT (NEXT Symbol))) → Bool)
    (Parabolic: (NEXT Symbol×NEXT Symbol) → PROCESS (NEXT (Symbol×Symbol)) → Bool)
    (Schroedinger: (Symbol × (NEXT Symbol×NEXT Symbol)) → PROCESS Symbol → Bool)

    [PRECEDES (NEXT Symbol) (some Particle) (some Particle) Æther Carrier]
    [PRECEDES (NEXT Symbol) (some Particle) (some Particle) Æther (λ _ => false)]
    [ORDERING (NEXT Symbol) (some Particle) (some Particle) Æther Carrier]
    [DECOMPOSABLE (NEXT Symbol) Particle Wave Æther Carrier Hyperbolic]
    [NAMED (NEXT Symbol) Particle Æther]
    [STATEFUL (NEXT Symbol) Particle Æther Hyperbolic Schroedinger]
    (Symbol: Type i)
    (Name: Symbol)
    (State: Symbol)
    (Change: Symbol → NEXT Symbol → Bool)
    (NextState: Symbol → PROCESS Symbol → Bool)
      where


namespace CARRIED
variable  {Symbol: Type i}
          {Value: Symbol}
          {State: Symbol}
          {Mechanism: Symbol → NEXT Symbol → Bool}
          {StateChange: NEXT Symbol → NEXT (NEXT Symbol) → Bool}
          {Emitted: NEXT Symbol → PROCESS (NEXT Symbol) → Bool}
          {Received: PROCESS (NEXT Symbol) → PROCESS (PROCESS (NEXT Symbol)) → Bool} -- Nothing can go in the middle of the counts.

def emitted
    (value: Symbol)
    (state: PROCESS (NEXT Symbol))
      : Bool :=
  carrier.emitted? value state

def received
    (state: PROCESS (NEXT Symbol))
    (value: PROCESS (PROCESS (NEXT Symbol)))
      : Bool :=
  carrier.received? state value

def value
    (state: NEXT Symbol)
    (mechanism: NEXT Symbol)
    : Symbol :=
  number.name?  mechanism

end CARRIED

inductive PhenomenonOf
    (Symbol: Type i)
    (Value: Symbol)
    (State: Symbol)
    (Mechanism: Symbol → NEXT Symbol → Bool)
    (StateChange: NEXT Symbol → NEXT (NEXT Symbol) → Bool)
    (Emitted: NEXT Symbol → PROCESS (NEXT Symbol) → Bool)
    (Received: PROCESS (NEXT Symbol) → PROCESS (PROCESS (NEXT Symbol)) → Bool) -- Nothing can go in the middle of the counts.
    [PRECEDES Symbol Value Value Mechanism (λ _ => false)]
    [PRECEDES Symbol State State Mechanism (λ _ => true)]
    [PRECEDES (NEXT Symbol) (some Value) (some Value) StateChange fun _x => false]  -- More free bits!
    [PRECEDES (NEXT Symbol) (some State) (some State) StateChange fun _x => true] -- Who needs memory allocation?
    [NAMED Symbol Value Mechanism] -- You know, like PHOTON GUN. Much better name than laser.
    [NAMED (NEXT Symbol) (some Value) StateChange]
    [STATEFUL (NEXT Symbol) Value State StateChange Emitted]
    [CARRIED Symbol Value State Mechanism StateChange Emitted Received]
  | nil : PhenomenonOf Symbol Value State Mechanism StateChange Emitted Received
  | cons: Symbol →
          NEXT Symbol →
          PROCESS (NEXT Symbol) →
          PROCESS (PROCESS (NEXT Symbol)) →
          PhenomenonOf Symbol Value State Mechanism StateChange Emitted Received →
          PhenomenonOf Symbol Value State Mechanism StateChange Emitted Received

end Measurement
