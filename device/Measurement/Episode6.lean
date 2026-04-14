/-
__Measurement: The Tragedy of John Henry__
__A Satire in Look-Ahead Backus-Naur Form__

_This is a gentle reminder that the long, long stories we tell ourselves are just that: far, far away._

HOW ARE YOU GENTLEMEN !!
(c) 2026 All your base are belong to us.

You have no chance to survive make your time. Ha ha ha ha ...



Welcome back episode 6.  And you know what?

I'm all about that base, 'bout that base, 'bout that base, no treble.
                                    -- Linda Ronstadt


-/


-- WE GET SIGNAL!
import Measurement.Episode5
set_option allowUnsafeReducibility true

-- MAIN SCREEN TURN ON !
namespace Measurement

@[reducible]
structure MathematicalProcess  -- Bullshit meter = 2963.  That's about 2/3 increase.
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


@[reducible]
class VALUE  -- Bullshit meter = 3327.  3x increase!  That's a lot of bullshit!
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



inductive Sum    -- Bullshit meter = 119.   Seems like that Abstraction bullshit doesn't stick around.  Probably should, though.
  | zero: Prop → Area → Sum
  | add: Fact → Area → Sum → Sum

namespace Sum   -- Bullshit meter = 76.
def le: Sum → Sum → Prop := fun s1 s2 =>
  match s1, s2 with
  | .zero p1 a1, .zero p2 a2 => p1 = p2 ∧ a1 ≤ a2
  | .zero p1 a1, .add f2 a2 _ => p1 = f2.truth ∧ a1 ≤ a2
  | .add f1 a1 _, .zero p2 a2 => f1.truth = p2 ∧ a1 ≤ a2
  | .add f1 a1 _, .add f2 a2 _ => f1 = f2 ∧ a1 ≤ a2

-- Sums are well orderd.
def lt: Sum → Sum → Prop := fun s1 s2 => le s1 s2 ∧ ¬ le s2 s1
end Sum

instance : LE Sum := ⟨Sum.le⟩  -- Bullshit meter = 8
instance : LT Sum := ⟨Sum.lt⟩

@[reducible]
structure AddingProcess  -- Bullshit meter ≈ 2063.   Thats 33% less bullshit than a generic mathematical process!
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

@[reducible]
class MAGNITUDE  -- Bullshit meter ≈ 1503.  That's less than 1/2 the bullshit of a value!
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

inductive Product  -- Bullshit meter = 119
  | One: Prop → Area → Product
  | Mul: Fact → Area → Product → Product

namespace Product  -- Bullshit meter = 75
def le: Product → Product → Prop := fun p1 p2 =>
  match p1, p2 with
  | .One p1 a1, .One p2 a2 => p1 = p2 ∧ a1 ≤ a2
  | .One p1 a1, .Mul f2 a2 _ => p1 = f2.truth ∧ a1 ≤ a2
  | .Mul f1 a1 _, .One p2 a2 => f1.truth = p2 ∧ a1 ≤ a2
  | .Mul f1 a1 _, .Mul f2 a2 _ => f1 = f2 ∧ a1 ≤ a2

def lt: Product → Product → Prop := fun p1 p2 => le p1 p2 ∧ ¬ le p2 p1
end Product

instance : LE Product := ⟨Product.le⟩  -- Bullshit meter = 5
instance : LT Product := ⟨Product.lt⟩

@[reducible]
structure MultiplyingProcess  -- Bullshit meter = 2157  5% increase.  Call that flat response over the AddingProcess.
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

@[reducible]
class SCALED  -- Bullshit meter = 1756
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
inductive Basis   -- Bullshit meter = 134
  | origin: Prop → Area → Basis
  | basis: Fact → Product → Area → Basis → Basis
-- Surely you're joking Mr. Henry!


@[reducible]
structure BASICOperation  -- Bullshit meter ≈ 2759
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
        --                                             ^
        --                                             |
        -- Tail recursion -----------------------------+

@[reducible]
class LOAD  -- Bullshit meter 2089
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

inductive Polynomial    --  Bullshit meter 119
  | zero: Prop → Basis → Polynomial
  | add: Fact → Basis → Polynomial → Polynomial

@[reducible]
structure GalerkinProcess   -- Bullshit meter 2794
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

-- Let's address the _elephant in the room_.  First, let's agree that it is _SINGULAR_ and that it is only _SO BIG_.
-- It can get really, really, __REALLY__ big in just a few keystrokes.  That's the problem.  We have only
-- one stack frame, our __FINITE_ELEPHANT__.
@[reducible]
class FINITE_ELEPHANT   -- 2368
    (Value: Type)
    (Carrier: CarrierProcess Value)
    [d: DISTINGUISHABLE Value Carrier]     -- So, she _ASSUMES_ they have an undocumented one and proceed to add the release.
    [a: ADMISSIBLE Value Carrier]          -- Only to realize she can't _EXACTLY_ find the _RIGHT_ release of their media to catalog.
    [c: COUNTABLE Value Carrier]           -- And spends hours every day on DISCOGS organizing her collection.
    [e: ENCODED Value Carrier]             -- The audiophile purchases the finest copies of any analog recordings.
    [r: RESIDUE Value Carrier]             -- The audiophile meticulously cleans her records.
    [b: BINARY Value Carrier]              -- Invariably, there will be two camps.  The _AUDIOPHILE_ and the _NORMIE_.
    [f: REPEATABLE Value Carrier]          -- And I can burn the output of the DAC to a CD?  Holy crap!
    [n: NUMERIC Value Carrier]             -- How about that, I just built a DAC !?
    [h: REPRESENTABLE Value Carrier]       -- Which means I can quantize and take the DFT!
    [p: PHYSICAL Value Carrier]            -- I just know that what I hear is measured by this physical process of oscillations.
    [z: COMPARABLE Value Carrier]          -- Dunno what they mean though.
    [particle: OBSERVED Value Carrier]     -- There we are, I found some phonemes.
    [frequency: PRESENT Value Carrier]     -- Fucking Jar Jar. Let me use an osciliscope and measure their tones and figure it out.
    [what_meesa_saying: MEASURABLE Value Carrier]  -- MEESA TRUE!
    [zero: GUNGAN Value Carrier]           -- Translate that into Gungan and ask Jar Jar Binks if he can relate to it?
    [one: SOURCE Value Carrier]            -- To quote Johnny Five: "NEED INPUT!"  Doesn't matter what kind.
    [result: EXECUTED Value Carrier]       -- Actually, I take that back, we have a program that can compute the value from an input
    [value: VALUE Value Carrier]           -- No, just some sort of representation of the value.
    [length: MAGNITUDE Value Carrier]      -- And this the length?   Do we have _e^iθ_?
    [scaled: SCALED Value Carrier]         -- Could this possibly represent the direction of said load?
    [oriented: LOAD Value Carrier]         -- hmmm, an _ORIENTED LOAD_?  Like _μ_ __N__?
--     ^                     ^
--     |                     |       +------------- Just this once, let's read it ^ this way.
--     +--------+------------+       |
--              |                    |
--              +--------------------+


  where
  galerkin_process : GalerkinProcess Value Carrier
  finite? : Polynomial → Prop := fun p =>
   match p with
   | .zero _ _ => True
   | .add _ _ _ => False


-- reticulate, damn you!
inductive Spline  -- 152
  | knot: Prop → Polynomial → Spline → Spline
  | interpolant: Fact → Polynomial → Spline → Spline → Spline


 end Measurement
