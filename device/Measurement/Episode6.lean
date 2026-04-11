/-
__Measurement: The Tragedy of John Henry__
__A Satire in Look-Ahead Backus-Naur Form__

_This is a gentle reminder that the long, long stories we tell ourselves are just that: far, far away._

(c) 2026 All rights are lefts.

-/



-- Would you even trust a theorem if I wrote one at this point?
import Measurement.Episode5

namespace Measurement

structure MathematicalProcess
    (Value: Type)
    (Carrier: CarrierProcess Value)
    [d: DISTINGUISHABLE Value Carrier]
    [a: ADMISSIBLE Value Carrier]
    [c: COUNTABLE Value Carrier]
    [e: ENCODED Value Carrier]
    [r: RESIDUE Value Carrier]
    [b: BINARY Value Carrier]
    [f: REPEATABLE Value Carrier]
    [n: NUMERIC Value Carrier]
    [h: REPRESENTABLE Value Carrier]
    [p: PHYSICAL Value Carrier]
    [z: COMPARABLE Value Carrier]
    [particle: OBSERVED Value Carrier]
    [frquency: PRESENT Value Carrier]
    [what_meesa_saying: MEASURABLE Value Carrier]
    [zero: GUNGAN Value Carrier]
    [one: SOURCE Value Carrier]
    [result: EXECUTED Value Carrier]
  where
  compiled_process: CompiledProcess Value Carrier
  result: EXECUTED Value Carrier
  mapping: Abstraction Value Carrier  -- Could it be that we are instantiating things?

  -- lepidopterology
  calculate? : Abstraction Value Carrier → Abstraction Value Carrier := fun function =>
  match function with
  | @Abstraction.compile _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ f _ =>
      @Abstraction.compile _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ one one f function
  | @Abstraction.execute _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ prog _ =>
      @Abstraction.execute _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ one compiled_process prog mapping


class VALUE
     (Value: Type)
     (Carrier: CarrierProcess Value)
     [d: DISTINGUISHABLE Value Carrier]
     [a: ADMISSIBLE Value Carrier]
     [c: COUNTABLE Value Carrier]
     [e: ENCODED Value Carrier]
     [r: RESIDUE Value Carrier]
     [b: BINARY Value Carrier]
     [f: REPEATABLE Value Carrier]
     [n: NUMERIC Value Carrier]
     [h: REPRESENTABLE Value Carrier]
     [p: PHYSICAL Value Carrier]
     [z: COMPARABLE Value Carrier]
     [particle: OBSERVED Value Carrier]
     [frquency: PRESENT Value Carrier]
     [what_meesa_saying: MEASURABLE Value Carrier]
     [zero: GUNGAN Value Carrier]
     [one: SOURCE Value Carrier]
     [result: EXECUTED Value Carrier]

   where
   mathematical_process : MathematicalProcess Value Carrier
   lt? : Abstraction Value Carrier → Abstraction Value Carrier → Prop := fun function output=>
     match function,output with
     | .compile _ _ _ , .compile _ _ _ => false
     | .compile _ _ _ , .execute _ _ _ => true
     | .execute _ _ _ , .compile _ _ _ => false
     | .execute _ _ a , .execute _ _ b => a < b



inductive Sum
  | zero: Prop → Area → Sum
  | add: Fact → Area → Sum → Sum

namespace Sum
def le: Sum → Sum → Prop := fun s1 s2 =>
  match s1, s2 with
  | .zero p1 a1, .zero p2 a2 => p1 = p2 ∧ a1 ≤ a2
  | .zero p1 a1, .add f2 a2 _ => p1 = f2.truth ∧ a1 ≤ a2
  | .add f1 a1 _, .zero p2 a2 => f1.truth = p2 ∧ a1 ≤ a2
  | .add f1 a1 _, .add f2 a2 _ => f1 = f2 ∧ a1 ≤ a2

-- Sums are well orderd.
def lt: Sum → Sum → Prop := fun s1 s2 => le s1 s2 ∧ ¬ le s2 s1
end Sum

instance : LE Sum := ⟨Sum.le⟩
instance : LT Sum := ⟨Sum.lt⟩

structure AddingProcess
    (Value: Type)
    (Carrier: CarrierProcess Value)
    [d: DISTINGUISHABLE Value Carrier]
    [a: ADMISSIBLE Value Carrier]
    [c: COUNTABLE Value Carrier]
    [e: ENCODED Value Carrier]
    [r: RESIDUE Value Carrier]
    [b: BINARY Value Carrier]
    [f: REPEATABLE Value Carrier]
    [n: NUMERIC Value Carrier]
    [h: REPRESENTABLE Value Carrier]
    [p: PHYSICAL Value Carrier]
    [z: COMPARABLE Value Carrier]
    [particle: OBSERVED Value Carrier]
    [frquency: PRESENT Value Carrier]
    [what_meesa_saying: MEASURABLE Value Carrier]
    [zero: GUNGAN Value Carrier]
    [one: SOURCE Value Carrier]
    [result: EXECUTED Value Carrier]
    [value: VALUE Value Carrier]

  where
  mathematical_process : MathematicalProcess Value Carrier
  plus: VALUE Value Carrier
  sum: Sum
  add? : Sum → Sum := fun s =>
    match s with
    | .zero p a => match p with
      | _ => .add Fact.Truth a (.zero p a)
    | .add f a _ => .add f a sum

class MAGNITUDE
     (Value: Type)
     (Carrier: CarrierProcess Value)
     [d: DISTINGUISHABLE Value Carrier]
     [a: ADMISSIBLE Value Carrier]
     [c: COUNTABLE Value Carrier]
     [e: ENCODED Value Carrier]
     [r: RESIDUE Value Carrier]
     [b: BINARY Value Carrier]
     [f: REPEATABLE Value Carrier]
     [n: NUMERIC Value Carrier]
     [h: REPRESENTABLE Value Carrier]
     [p: PHYSICAL Value Carrier]
     [z: COMPARABLE Value Carrier]
     [particle: OBSERVED Value Carrier]
     [frquency: PRESENT Value Carrier]
     [what_meesa_saying: MEASURABLE Value Carrier]
     [zero: GUNGAN Value Carrier]
     [one: SOURCE Value Carrier]
     [result: EXECUTED Value Carrier]
    [value: VALUE Value Carrier]

   where
   adding_process : AddingProcess Value Carrier
   magnitude? : Sum → Area := fun s =>
    match s with
    | .zero _ a => a
    | .add _ a _ => a

inductive Product
  | One: Prop → Area → Product
  | Mul: Fact → Area → Product → Product

namespace Product

def le: Product → Product → Prop := fun p1 p2 =>
  match p1, p2 with
  | .One p1 a1, .One p2 a2 => p1 = p2 ∧ a1 ≤ a2
  | .One p1 a1, .Mul f2 a2 _ => p1 = f2.truth ∧ a1 ≤ a2
  | .Mul f1 a1 _, .One p2 a2 => f1.truth = p2 ∧ a1 ≤ a2
  | .Mul f1 a1 _, .Mul f2 a2 _ => f1 = f2 ∧ a1 ≤ a2

def lt: Product → Product → Prop := fun p1 p2 => le p1 p2 ∧ ¬ le p2 p1
end Product

instance : LE Product := ⟨Product.le⟩
instance : LT Product := ⟨Product.lt⟩

structure MultiplyingProcess
    (Value: Type)
    (Carrier: CarrierProcess Value)
    [d: DISTINGUISHABLE Value Carrier]
    [a: ADMISSIBLE Value Carrier]
    [c: COUNTABLE Value Carrier]
    [e: ENCODED Value Carrier]
    [r: RESIDUE Value Carrier]
    [b: BINARY Value Carrier]
    [f: REPEATABLE Value Carrier]
    [n: NUMERIC Value Carrier]
    [h: REPRESENTABLE Value Carrier]
    [p: PHYSICAL Value Carrier]
    [z: COMPARABLE Value Carrier]
    [particle: OBSERVED Value Carrier]
    [frquency: PRESENT Value Carrier]
    [what_meesa_saying: MEASURABLE Value Carrier]
    [zero: GUNGAN Value Carrier]
    [one: SOURCE Value Carrier]
    [result: EXECUTED Value Carrier]
    [value: VALUE Value Carrier]
    [length: MAGNITUDE Value Carrier]

  where
  addding_process : AddingProcess Value Carrier
  product: Product
  multiply? : Product → Product := fun p =>
    match p with
    | .One prop a => match prop with
      | _ => .Mul Fact.Truth a p
    | .Mul f a _ => .Mul f a product

class SCALED
    (Value: Type)
    (Carrier: CarrierProcess Value)
    [d: DISTINGUISHABLE Value Carrier]
    [a: ADMISSIBLE Value Carrier]
    [c: COUNTABLE Value Carrier]
    [e: ENCODED Value Carrier]
    [r: RESIDUE Value Carrier]
    [b: BINARY Value Carrier]
    [f: REPEATABLE Value Carrier]
    [n: NUMERIC Value Carrier]
    [h: REPRESENTABLE Value Carrier]
    [p: PHYSICAL Value Carrier]
    [z: COMPARABLE Value Carrier]
    [particle: OBSERVED Value Carrier]
    [frquency: PRESENT Value Carrier]
    [what_meesa_saying: MEASURABLE Value Carrier]
    [zero: GUNGAN Value Carrier]
    [one: SOURCE Value Carrier]
    [result: EXECUTED Value Carrier]
    [value: VALUE Value Carrier]
    [length: MAGNITUDE Value Carrier]
  where
  multiplying_process : MultiplyingProcess Value Carrier
  norm? : Product → Sum:= fun p =>
    match p with
    | .One f a => .zero f a
    | .Mul f a _ => .add f a (.zero f.truth a)

-- Dyson vacuums are _so-so_.  Dyson series, on the other hand?
inductive Basis
  | origin: Prop → Area → Basis
  | basis: Fact → Product → Area → Basis → Basis
-- Surely you're joking Mr. Henry!


structure BASICOperation
    (Value: Type)
    (Carrier: CarrierProcess Value)
    [d: DISTINGUISHABLE Value Carrier]
    [a: ADMISSIBLE Value Carrier]
    [c: COUNTABLE Value Carrier]
    [e: ENCODED Value Carrier]
    [r: RESIDUE Value Carrier]
    [b: BINARY Value Carrier]
    [f: REPEATABLE Value Carrier]
    [n: NUMERIC Value Carrier]
    [h: REPRESENTABLE Value Carrier]
    [p: PHYSICAL Value Carrier]
    [z: COMPARABLE Value Carrier]
    [particle: OBSERVED Value Carrier]
    [frquency: PRESENT Value Carrier]
    [what_meesa_saying: MEASURABLE Value Carrier]
    [zero: GUNGAN Value Carrier]
    [one: SOURCE Value Carrier]
    [result: EXECUTED Value Carrier]
    [value: VALUE Value Carrier]
    [length: MAGNITUDE Value Carrier]
    [scaled: SCALED Value Carrier]
  where
  GOSUB: MultiplyingProcess Value Carrier     -- <-- I think I found the gosub
  TEN: Area                                   -- <-- and a line number!
  span: Basis

  jmp? : Basis → Basis := fun b =>
    match b with
    | .origin _ _ => .basis Fact.Truth GOSUB.product TEN span
    | .basis f p a _ => .basis f (GOSUB.multiply? p) a b

class LOAD
    (Value: Type)
    (Carrier: CarrierProcess Value)
    [d: DISTINGUISHABLE Value Carrier]
    [a: ADMISSIBLE Value Carrier]
    [c: COUNTABLE Value Carrier]
    [e: ENCODED Value Carrier]
    [r: RESIDUE Value Carrier]
    [b: BINARY Value Carrier]
    [f: REPEATABLE Value Carrier]
    [n: NUMERIC Value Carrier]
    [h: REPRESENTABLE Value Carrier]
    [p: PHYSICAL Value Carrier]
    [z: COMPARABLE Value Carrier]
    [particle: OBSERVED Value Carrier]
    [frquency: PRESENT Value Carrier]
    [what_meesa_saying: MEASURABLE Value Carrier]
    [zero: GUNGAN Value Carrier]
    [one: SOURCE Value Carrier]
    [result: EXECUTED Value Carrier]
    [value: VALUE Value Carrier]
    [length: MAGNITUDE Value Carrier]
    [scaled: SCALED Value Carrier]

  where
  basic_operation : BASICOperation Value Carrier
  --  Is this an eigenvector?
  decoded? : Basis → Basis → Prop := fun b1 b2 =>
   match b1,b2 with
    | .origin t _, .origin f _ => t ≠ f          -- This is our clock.
    | .origin t _, .basis f _ _ _ => t ≠ f.truth -- Again, this is our clock.
    | .basis _ _ _ _, .origin _ _ => False       -- Disallow this.
    | .basis f1 _ a1 _, .basis f2 _ a2 _ => f1 ≠ f2 ∧ a1 ≤ a2

inductive Polynomial
  | zero: Prop → Basis → Polynomial
  | add: Fact → Basis → Polynomial → Polynomial

structure GalerkinProcess
    (Value: Type)
    (Carrier: CarrierProcess Value)
    [d: DISTINGUISHABLE Value Carrier]
    [a: ADMISSIBLE Value Carrier]
    [c: COUNTABLE Value Carrier]
    [e: ENCODED Value Carrier]
    [r: RESIDUE Value Carrier]
    [b: BINARY Value Carrier]
    [f: REPEATABLE Value Carrier]
    [n: NUMERIC Value Carrier]
    [h: REPRESENTABLE Value Carrier]
    [p: PHYSICAL Value Carrier]
    [z: COMPARABLE Value Carrier]
    [particle: OBSERVED Value Carrier]
    [frquency: PRESENT Value Carrier]
    [what_meesa_saying: MEASURABLE Value Carrier]
    [zero: GUNGAN Value Carrier]
    [one: SOURCE Value Carrier]
    [result: EXECUTED Value Carrier]
    [value: VALUE Value Carrier]
    [length: MAGNITUDE Value Carrier]
    [scaled: SCALED Value Carrier]
    [oriented: LOAD Value Carrier]

  where
  load_process : LOAD Value Carrier
  polynomial : Polynomial

  dot? : Polynomial → Polynomial := fun p =>
    match p with
    | .zero t b => match t with
      | _ => .add Fact.Truth b p
    | .add f b _ => .add f b polynomial

class FINITE_ELEPHANT
    (Value: Type)
    (Carrier: CarrierProcess Value)
    [d: DISTINGUISHABLE Value Carrier]
    [a: ADMISSIBLE Value Carrier]
    [c: COUNTABLE Value Carrier]
    [e: ENCODED Value Carrier]
    [r: RESIDUE Value Carrier]
    [b: BINARY Value Carrier]
    [f: REPEATABLE Value Carrier]
    [n: NUMERIC Value Carrier]
    [h: REPRESENTABLE Value Carrier]
    [p: PHYSICAL Value Carrier]
    [z: COMPARABLE Value Carrier]
    [particle: OBSERVED Value Carrier]
    [frquency: PRESENT Value Carrier]
    [what_meesa_saying: MEASURABLE Value Carrier]
    [zero: GUNGAN Value Carrier]
    [one: SOURCE Value Carrier]
    [result: EXECUTED Value Carrier]
    [value: VALUE Value Carrier]
    [length: MAGNITUDE Value Carrier]
    [scaled: SCALED Value Carrier]
    [oriented: LOAD Value Carrier]

  where
  galerkin_process : GalerkinProcess Value Carrier
  finite? : Polynomial → Prop := fun p =>
   match p with
   | .zero _ _ => True
   | .add _ _ _ => False


-- reticulate, damn you!
inductive Spline
  | knot: Prop → Polynomial → Spline → Spline
  | interpolant: Fact → Polynomial → Spline → Spline → Spline


 end Measurement
