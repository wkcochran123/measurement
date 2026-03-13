/-
Measurement/Chapter2.lean
-/

import Measurement.Chapter1

namespace Measurement

inductive TuringDevice
    (Symbol: Type i)
    (Encoding: Symbol -> Symbol -> Bool )
    (Encoded: Symbol -> NEXT Symbol -> Bool)
    (Value : Symbol -> Symbol -> Bool)
    (Phenomenon: Symbol -> NEXT Symbol -> Bool)
    [DISTINGUISHABLE Symbol Encoding]
    [ENCODED Symbol Encoding Encoded]
    [DISTINGUISHABLE Symbol Value]
    [ENCODED Symbol Value Phenomenon]
    [ADMISSIBLE Symbol Value Phenomenon]
    [COMPUTABLE Symbol Encoding Encoded]
    [COMPUTABLE Symbol Value Phenomenon]
    : Type (i+1)
  | nil : TuringDevice Symbol Encoding Execution
  | cons : Symbol ->
           ENCODED Symbol Encoding ->
           ADMISSIBLE Symbol Execution ->
           COMPUTABLE Symbol Encoding Execution ->
           TuringDevice Symbol Encoding Execution

class COUNTABLE
    (Symbol: Type i)
    (Arrival : Symbol -> Symbol -> Bool)
    (CountingProcess : Symbol -> NEXT Symbol -> Bool)
    (Encoding : Symbol -> Symbol -> Bool)
    [DISTINGUISHABLE Symbol Arrival]
    [DECOMPOSABLE Symbol Arrival]
    [DISTINGUISHABLE Symbol Encoding]
    [ADMISSIBLE Symbol CountingProcess]
      where
  now: Symbol
  next? : Symbol -> Symbol -> Bool
  count? : Symbol -> NEXT Symbol -> Bool

namespace COUNTABLE
variable {Symbol: Type i}
         {Arrival : Symbol -> Symbol -> Bool}
         {CountingProcess : Symbol -> NEXT Symbol -> Bool}
         {Encoding : Symbol -> Symbol -> Bool}
         (carrier_symbol: DISTINGUISHABLE Symbol Arrival)
         (observed_symbol: DECOMPOSABLE Symbol Arrival)
         (gauge_reading: DISTINGUISHABLE Symbol Encoding)
         (awaited_return: ADMISSIBLE Symbol CountingProcess)
         [count_of_carriers: COUNTABLE Symbol Arrival CountingProcess Encoding ]

def next
    (n: Symbol)
    (n_plus_one: Symbol)
    : Bool :=
  count_of_carriers.next? n n_plus_one

def count
    (number_i1: Symbol)
    (number_i2: NEXT Symbol)
    : Bool :=
  count_of_carriers.count? number_i1 number_i2

end COUNTABLE


class TIMED
    (Symbol: Type i)
    (Data: Symbol)
    (Carrier: NEXT Symbol)
    (Elapsed: Symbol -> NEXT Symbol -> NEXT (NEXT Symbol) -> Bool)
    where
  sent? : Symbol -> NEXT Symbol -> Bool
  received? : NEXT Symbol -> NEXT (NEXT Symbol) -> Bool

namespace TIMED
variable {Symbol: Type i}
         {Data: Symbol}
         {Carrier: NEXT Symbol}
         {Elapsed: Symbol -> NEXT Symbol -> NEXT (NEXT Symbol) -> Bool}
         (Timer: TIMED Symbol Data Carrier Elapsed)

def sent
    (data: Symbol)
    (carrier: NEXT Symbol)
    : Bool :=
  Timer.sent? data carrier

def received
    (carrier: NEXT Symbol)
    (response: NEXT (NEXT Symbol))
    : Bool :=
  Timer.received? carrier response

end TIMED

inductive Clock
    (Symbol: Type i)
    (Data: Symbol)
    (Carrier: NEXT Symbol)
    (Elapsed: Symbol -> NEXT Symbol -> NEXT (NEXT Symbol) -> Bool)
    [TIMED Symbol Data Carrier Elapsed]
  | nil : Clock Symbol Data Carrier Elapsed
  | cons: Symbol -> NEXT Symbol -> NEXT (NEXT Symbol) -> Clock Symbol Data Carrier Elapsed


class PHENOMENAL
    (Symbol: Type i)
    (Process: Symbol)
    (Carrier: NEXT Symbol)
    (Response: NEXT (NEXT Symbol))
    (CarrierEmitted: Symbol -> NEXT Symbol -> Bool)
    (CarrierReceived: NEXT Symbol -> NEXT (NEXT Symbol) -> Bool)
    (Observed: Symbol -> NEXT Symbol -> NEXT (NEXT Symbol) -> Bool)
    (Hypothesis: NEXT Symbol -> NEXT Symbol -> Bool)
    [TIMED Symbol Process Carrier Observed]                        -- The emission and reception of a particle
    [ADMISSIBLE Symbol CarrierEmitted]
    [ADMISSIBLE (NEXT Symbol) CarrierReceived]
    [DISTINGUISHABLE (NEXT Symbol) Hypothesis]
    [DECOMPOSABLE (NEXT Symbol) Hypothesis]
    [TIMED Symbol Process Carrier Observed]
    [COUNTABLE (NEXT Symbol) Hypothesis CarrierReceived Hypothesis] -- The samples of individual particles

inductive Instrument
    (Symbol: Type i)
    (Process: Symbol)
    (Carrier: NEXT Symbol)
    (Response: NEXT (NEXT Symbol))
    (CarrierEmitted: Symbol -> NEXT Symbol -> Bool)
    (CarrierReceived: NEXT Symbol -> NEXT (NEXT Symbol) -> Bool)
    (Observed: Symbol -> NEXT Symbol -> NEXT (NEXT Symbol) -> Bool)
    (Phenomenon: NEXT Symbol -> NEXT Symbol -> Bool)
    [TIMED Symbol Process Carrier Observed]                        -- The emission and reception of a particle
    [ADMISSIBLE Symbol CarrierEmitted]
    [ADMISSIBLE (NEXT Symbol) CarrierReceived]
    [DISTINGUISHABLE (NEXT Symbol) Phenomenon]
    [DECOMPOSABLE (NEXT Symbol) Phenomenon]
    [COUNTABLE (NEXT Symbol) Phenomenon CarrierReceived Phenomenon] -- The samples of individual particles
    [PHENOMENAL Symbol Process Carrier Response CarrierEmitted CarrierReceived Observed Phenomenon]
  | nil : Instrument Symbol Process Carrier Response CarrierEmitted CarrierReceived Observed Phenomenon
  | cons : Symbol ->
           Process ->
           Carrier ->
           Response ->
           TIMED Symbol Process Carrier Observed ->
           ADMISSIBLE Symbol CarrierEmitted ->
           ADMISSIBLE (NEXT Symbol) Phenomenon ->
           DISTINGUISHABLE (NEXT Symbol) Phenomenon ->
           OBSERVABLE (NEXT Symbol) Phenomenon ->
           COUNTABLE ()


class COUNTABLE
    (symbol : Type now)
    (event  : Type (now+1))
    [DISTINGUISHABLE symbol event]
    (η : symbol)
    (LT : symbol -> symbol -> Bool)
    where
  witness : symbol -> Option (ULift.{now+1, now} symbol)
  number: symbol

namespace COUNTABLE
variable {symbol : Type now}
         {event : Type (now+1)}
         [ds: DISTINGUISHABLE symbol event]
         {η : symbol}
         {LT : symbol -> symbol -> Bool}
         [cs: COUNTABLE symbol event η LT]
def η?
  (n : symbol) : Option (ULift.{now+1, now} symbol) :=
  cs.witness n
end COUNTABLE

structure Event
    (Symbol: Type i)
    (Distinguishable: Symbol -> Symbol -> Bool)
    [DISTINGUISHABLE Symbol Distinguishable]
    where
  admissible? : Symbol -> NEXT Symbol -> Bool
  observation : Symbol

namespace Event
variable {Symbol : Type i}
         {Distinguishable : Symbol -> Symbol -> Bool}
         [DISTINGUISHABLE Symbol Distinguishable]

def admissible (s : Symbol)(e : Event Symbol Distinguishable) : Bool :=
  Distinguishable s e.observation

end Event

structure Sensor
    (Event: Type i)
    (Stimulus: Event -> Event -> Bool)
    (Response: Event -> (NEXT Event) -> Bool)
    [DISTINGUISHABLE Event Stimulus]
    [ENCODED Event Stimulus]
    [COMPUTABLE Event Stimulus Response]
    where
  read? : Event -> Option (NEXT Event)
  correlant? : Event -> Event -> Bool

class REPEATABLE
    (Symbol : Type i)
    (Experiment: Symbol -> NEXT Symbol -> Bool)
    where
  observation: Symbol
  outcome?: Symbol -> NEXT Symbol -> Bool

namespace REPEATABLE
variable {Symbol : Type i}
         {Experiment: Symbol -> NEXT Symbol -> Bool}
         [r: REPEATABLE Symbol Experiment]
def trial
    (value: Symbol)
    (outcome: NEXT Symbol)
      : Bool :=
  (r.outcome? value outcome) && (Experiment value outcome)
end REPEATABLE


abbrev Next (σ : Type now) := ULift.{now+1,now} σ

inductive Count
    (symbol : Type now)
    (next  : Type (now+1))
    [DISTINGUISHABLE symbol (Next symbol)]
    : Type (now+1)
  | nil : Count symbol next
  | cons : (next × symbol) → Count symbol next → Count symbol next

namespace Count
variable {symbol : Type now}
         {event : Type (now+1)}
         [DISTINGUISHABLE symbol event]
end Count

structure Bounds
    (symbol : Type now)
    (event : Type (now+1))
    [i: DISTINGUISHABLE symbol event]
    [j: DISTINGUISHABLE symbol event]
    (number : symbol)
    (LT : symbol -> symbol -> Bool)
    [i_count: COUNTABLE symbol event number LT]
    [j_count: COUNTABLE symbol event number LT]
    where
  left_number: symbol
  right_number: symbol
  in_bounds?: symbol → symbol → Bool


namespace Bisection
end Bisection

structure Decomposition
    (symbol : Type now)
    (event : Type (now+1))
    [i: DISTINGUISHABLE symbol event]
    [j: DISTINGUISHABLE symbol event]
    (η : symbol)
    (LT : symbol -> symbol -> Bool)
    [i_count: COUNTABLE symbol event η LT]
    where
  top: symbol
  bottom: symbol

structure Ordering
    (symbol : Type now)
    (event : Type (now+1))
    [DISTINGUISHABLE symbol event]
    (η : symbol)
    (LT : symbol -> symbol -> Bool)
    [count: COUNTABLE symbol event η LT]
    where
  lt? : symbol -> symbol -> Bool

namespace Ordering
variable {symbol : Type now}
         {event : Type (now+1)}
         [DISTINGUISHABLE symbol event]
         {η : symbol}
         {LT : symbol -> symbol -> Bool}
         [count: COUNTABLE symbol event η LT]

def lt (a b : symbol) : Bool :=
  LT a b

end Ordering

class Invariant
    (symbol : Type now)
    (event  : Type (now+1))
    [DISTINGUISHABLE symbol event]
    (η : symbol)
    (LE : symbol -> symbol -> Bool)
    [COUNTABLE symbol event η LE]
    where
  indicative: symbol
  less_than? : symbol -> symbol -> Bool
  rounds? : symbol -> Option (ULift.{now+1, now} symbol) -> Bool

namespace Invariant
variable {symbol : Type now}
         {event : Type (now+1)}
         [DISTINGUISHABLE symbol event]
         {η : symbol}
         {LT : symbol -> symbol -> Bool}
         [COUNTABLE symbol event η LT]

def lt (a b : symbol) : Bool :=
  LT a b

def round (a : symbol) (n : Option (ULift.{now+1, now} symbol)) : Bool :=
  match n with
  | none => false
  | some n' => LT a n'.down

end Invariant

end Measurement
