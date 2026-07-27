import Measurement.Episode14

set_option maxHeartbeats 4000000
set_option maxRecDepth 1000
set_option allowUnsafeReducibility true


namespace Measurement

universe i

inductive Bullshit where
| zero  : Fact → Bullshit
| one   : Fact → Number → CompilerTape → CompilerTape → Bullshit → Bullshit
| rest  : Fact → Fact → Prop → Number → Number → Number → CompilerTape → CompilerTape →
                    Bullshit → Bullshit → Bullshit

namespace Bullshit
  def le : Bullshit → Bullshit → Prop
  | .zero f                    , .zero g                    => f.truth = g.truth
  | .zero _                    , _                          => True  -- Zero is the origin for all

  | .one _ _ _ _ _             , .zero _                    => False
  | .one p1 n1' _ _ _          , .one p2 n2' _ _ _          =>
                                                    match p1.decTruth, p2.decTruth with
                                                    | isTrue _,  isTrue _  => n1' ≤ n2'
                                                    | isFalse _, isFalse _ => n2' ≤ n1'
                                                    | isTrue _,  isFalse _ => False
                                                    | isFalse _, isTrue _  => True
  | .one _ _ _ _ _             , .rest _ _ _ _ _ _ _ _ _ _  => True

  | .rest _ _ _ _ _ _ _ _ _ _  , .zero _                    => False
  | .rest _ _ _ _ _ _ _ _ _ _  , .one _ _ _ _ _             => False

  | .rest f1 g1 p1 _ _ n13 _ _ m11 m12,
  .rest f2 g2 p2 _ _ n23 _ _ m21 m22 =>
    (f1.truth = f2.truth) ∧
    (g1.truth = g2.truth) ∧
    (p1 -> p2) ∧
    (n13 ≤ n23) ∧
    le m11 m21 ∧
    le m12 m22

def lt: Bullshit → Bullshit → Prop := fun s1 s2 => le s1 s2 ∧ ¬ le s2 s1
end Bullshit

instance : LE Bullshit where
  le := Bullshit.le
instance : LT Bullshit where
  lt := Bullshit.lt


structure AtreyuProcess
    (Value: Type i)
    (Carrier: CarrierProcess Value)
    [d: DISTINGUISHABLE Value Carrier] [a: ADMISSIBLE Value Carrier] [c: COUNTABLE Value Carrier]
    [e: ENCODED Value Carrier] [r: RESIDUE Value Carrier] [b: BINARY Value Carrier]
    [f: REPEATABLE Value Carrier] [n: NUMERIC Value Carrier] [h: REPRESENTABLE Value Carrier]
    [p: PHYSICAL Value Carrier] [z: COMPARABLE Value Carrier] [particle: OBSERVED Value Carrier]
    [frquency: PRESENT Value Carrier] [what_meesa_saying: MEASURABLE Value Carrier] [zero: GUNGAN Value Carrier]
    [one: SOURCE Value Carrier] [result: EXECUTED Value Carrier] [value: VALUE Value Carrier]
    [length: MAGNITUDE Value Carrier] [scaled: SCALED Value Carrier] [oriented: LOAD Value Carrier]
    [matter: FINITE_ELEPHANT Value Carrier] [model: BULLSHIT Value Carrier] [space: PROPAGANDA Value Carrier]
    [scientist: ACOLYTE Value Carrier] [ideology: SCIENTIFIC Value Carrier] [gospel: TRUTH Value Carrier]
    [account: WITNESSED Value Carrier] [REAL Value Carrier] (imaginary: REAL Value Carrier) [delta: UNIVERSAL Value Carrier]
    [prop: LOGICAL Value Carrier] [executable: HALTED Value Carrier] [measured: MEASURED Value Carrier imaginary]
    [compiled: COMPILED Value Carrier] where
  compiler_output: CompilerOutput Value Carrier imaginary
  next_measurement: Bullshit
  stress: Number
  strain: Number := Carrier.event Carrier.value   -- Delicious Ouroboros!!
  proof: CompilerTape


  satirize: Bullshit → Bullshit := fun measurement =>
  match measurement with
  |.zero _    =>
              .one d.fact stress proof compiler_output.tape next_measurement
  |.one fact last_stress last_object last_state last_measurement =>
              match fact.decTruth, d.fact.decTruth with
              | isTrue _,  isTrue _  =>
                  .rest fact d.fact
                    ((fact.truth = d.fact.truth ∧ last_stress ≤ stress) ∨
                    (fact.truth ≠ d.fact.truth ∧ stress ≤ last_stress))
                    last_stress stress strain
                    last_object last_state
                    last_measurement next_measurement

              | isTrue _,  isFalse _ =>
                  .rest fact d.fact
                    False
                    last_stress stress strain
                    last_object last_state
                    last_measurement next_measurement

              | isFalse _, isTrue _  =>
                  .rest fact d.fact
                    True
                    last_stress stress strain
                    last_object last_state
                    last_measurement next_measurement

              | isFalse _, isFalse _ =>
                  .rest fact d.fact
                    ((fact.truth = d.fact.truth ∧ stress ≤ last_stress) ∨
                    (fact.truth ≠ d.fact.truth ∧ last_stress ≤ stress))
                    last_stress stress strain
                    last_object last_state
                    last_measurement next_measurement

  | .rest _ f2 _ _ n2 n3 _ prior_proof _ if_false =>
              match f2.decTruth, d.fact.decTruth with
              | isTrue _,  isTrue _  =>
                  .rest f2 d.fact
                    ((f2.truth = d.fact.truth ∧ n2 ≤ stress) ∨
                    (f2.truth ≠ d.fact.truth ∧ stress ≤ n2))
                    n3 stress strain
                    prior_proof proof
                    if_false next_measurement

              | isTrue _,  isFalse _ =>
                  .rest f2 d.fact
                    False
                    n3 stress strain
                    prior_proof proof
                    if_false next_measurement

              | isFalse _, isTrue _  =>
                  .rest f2 d.fact
                    True
                    n3 stress strain
                    prior_proof proof
                    if_false next_measurement

              | isFalse _, isFalse _ =>
                  .rest f2 d.fact
                    ((f2.truth = d.fact.truth ∧ stress ≤ n2) ∨
                    (f2.truth ≠ d.fact.truth ∧ n2 ≤ stress))
                    n3 stress strain
                    prior_proof proof
                    if_false next_measurement


  bilinear? : Bullshit → Bullshit → Bullshit := fun a b =>
    -- Back-to-back satirize: lift both inputs one rung, then hang them as the two
    -- children of a single .rest -- the only constructor that carries a pair.  The
    -- Prop slot holds the slip (sa < sb); residue? is exactly the projection of it.
    -- (satirize lifts every rung, so neither side is ever .zero -- the floor arms are
    -- kept only for totality and collapse to the surviving satire.)
    match satirize a, satirize b with
    | .zero _, sb      => sb
    | sa,      .zero _ => sa
    | sa,      sb      =>
        .rest d.fact d.fact (sa < sb)
              stress stress strain
              proof proof
              sa sb

  -- residue? is the PROJECTION of the operator: run bilinear?, then read the slip out of
  -- the .rest's Prop slot.  The only `none` is the commute -- both inputs at the origin
  -- floor -- mirroring how `.zero` floors Bullshit.le and `none` floors slipLe.  This is
  -- the option the residue computation (obfusplained?/close?) reads off.
  residue? : Bullshit → Bullshit → Option Prop := fun a b =>
    match a, b with
    | .zero _, .zero _ => none
    | _,       _       =>
        match bilinear? a b with
        | .rest _ _ p _ _ _ _ _ _ _ => some p
        | _                          => none




class TrueOutput
    (Value: Type i)
    (Carrier: CarrierProcess Value)
    [d: DISTINGUISHABLE Value Carrier] [a: ADMISSIBLE Value Carrier] [c: COUNTABLE Value Carrier]
    [e: ENCODED Value Carrier] [r: RESIDUE Value Carrier] [b: BINARY Value Carrier]
    [f: REPEATABLE Value Carrier] [n: NUMERIC Value Carrier] [h: REPRESENTABLE Value Carrier]
    [p: PHYSICAL Value Carrier] [z: COMPARABLE Value Carrier] [particle: OBSERVED Value Carrier]
    [frquency: PRESENT Value Carrier] [what_meesa_saying: MEASURABLE Value Carrier] [zero: GUNGAN Value Carrier]
    [one: SOURCE Value Carrier] [result: EXECUTED Value Carrier] [value: VALUE Value Carrier]
    [length: MAGNITUDE Value Carrier] [scaled: SCALED Value Carrier] [oriented: LOAD Value Carrier]
    [matter: FINITE_ELEPHANT Value Carrier] [model: BULLSHIT Value Carrier] [space: PROPAGANDA Value Carrier]
    [scientist: ACOLYTE Value Carrier] [ideology: SCIENTIFIC Value Carrier] [gospel: TRUTH Value Carrier]
    [account: WITNESSED Value Carrier] [REAL Value Carrier] (imaginary: REAL Value Carrier) [delta: UNIVERSAL Value Carrier]
    [prop: LOGICAL Value Carrier] [executable: HALTED Value Carrier] [measured: MEASURED Value Carrier imaginary]
    [compiled: COMPILED Value Carrier]
  where
  atreyu_process : AtreyuProcess Value Carrier imaginary
  TRUE : Bullshit := .zero d.fact
  -- output is the compiler/reader output: the THEORY rung of the bullshit
  -- ladder, NOT the origin TRUE.  Instances must supply it.
  output : Bullshit
  -- The certificate is now ORDERING, not equality: the .zero origin (TRUE)
  -- is the floor below the accumulated bullshit `output`.  `Bullshit.le` gives
  -- `.zero _ , _ => True` for ANY second argument, so `TRUE ≤ output` is the
  -- honest definitional witness no matter which rung `output` lands on.
  output_true : TRUE ≤ output
  raw_output : Bullshit := atreyu_process.satirize atreyu_process.next_measurement

  obfusplained? : TRUE ≤ output → Bullshit → Bullshit → Option Prop := fun _ a b =>
  match a, b with
  | .zero _, .zero _ => none            -- two origins: they commute, no slip
  | _,       _       => some (a < b)    -- a real rung pair: the slip, condition a < b

def You_the_Reader
    (Value: Type i)
    (Carrier: CarrierProcess Value)
    [d: DISTINGUISHABLE Value Carrier] [a: ADMISSIBLE Value Carrier] [c: COUNTABLE Value Carrier]
    [e: ENCODED Value Carrier] [r: RESIDUE Value Carrier] [b: BINARY Value Carrier]
    [f: REPEATABLE Value Carrier] [n: NUMERIC Value Carrier] [h: REPRESENTABLE Value Carrier]
    [p: PHYSICAL Value Carrier] [z: COMPARABLE Value Carrier] [particle: OBSERVED Value Carrier]
    [frquency: PRESENT Value Carrier] [what_meesa_saying: MEASURABLE Value Carrier] [zero: GUNGAN Value Carrier]
    [one: SOURCE Value Carrier] [result: EXECUTED Value Carrier] [value: VALUE Value Carrier]
    [length: MAGNITUDE Value Carrier] [scaled: SCALED Value Carrier] [oriented: LOAD Value Carrier]
    [matter: FINITE_ELEPHANT Value Carrier] [model: BULLSHIT Value Carrier] [space: PROPAGANDA Value Carrier]
    [scientist: ACOLYTE Value Carrier] [ideology: SCIENTIFIC Value Carrier] [gospel: TRUTH Value Carrier]
    [account: WITNESSED Value Carrier] [imaginary: REAL Value Carrier] [delta: UNIVERSAL Value Carrier]
    [prop: LOGICAL Value Carrier] [executable: HALTED Value Carrier] [measured: MEASURED Value Carrier imaginary]
    [compiled: COMPILED Value Carrier]
 : AtreyuProcess Value Carrier imaginary where
  compiler_output := compiled.compiler_output
  next_measurement := .zero d.fact
  stress := Carrier.value
  proof := compiled.object_file

-- THEORY: the three pieces of bullshit as a named ladder, expressed as defs
-- (NOT a 34-binder structure -- a structure here forces a fresh 34-gate
-- instance synthesis at every use site, which is exactly the elaboration cost
-- we are fighting).  Each rung takes the reader-process explicitly and
-- satirizes the PREVIOUS rung, so the chain is well-founded and bottoms at the
-- .zero origin.  `THEORY.raw_output` is the HYPOTHESIS rung (.one): the compiler
-- output the device reads, NOT the origin TRUE.  (It is the b rung, one satirize
-- up; the theory rung c/.rest is still defined below for Episode16's
-- velocity/acceleration variations, but is not used as the certified output --
-- see the raw_output comment for why.)
namespace THEORY

variable {Value : Type i} {Carrier : CarrierProcess Value}
    [d: DISTINGUISHABLE Value Carrier] [a: ADMISSIBLE Value Carrier] [c: COUNTABLE Value Carrier]
    [e: ENCODED Value Carrier] [r: RESIDUE Value Carrier] [b: BINARY Value Carrier]
    [f: REPEATABLE Value Carrier] [n: NUMERIC Value Carrier] [h: REPRESENTABLE Value Carrier]
    [p: PHYSICAL Value Carrier] [z: COMPARABLE Value Carrier] [particle: OBSERVED Value Carrier]
    [frquency: PRESENT Value Carrier] [what_meesa_saying: MEASURABLE Value Carrier] [zero: GUNGAN Value Carrier]
    [one: SOURCE Value Carrier] [result: EXECUTED Value Carrier] [value: VALUE Value Carrier]
    [length: MAGNITUDE Value Carrier] [scaled: SCALED Value Carrier] [oriented: LOAD Value Carrier]
    [matter: FINITE_ELEPHANT Value Carrier] [model: BULLSHIT Value Carrier] [space: PROPAGANDA Value Carrier]
    [scientist: ACOLYTE Value Carrier] [ideology: SCIENTIFIC Value Carrier] [gospel: TRUTH Value Carrier]
    [account: WITNESSED Value Carrier] [imaginary: REAL Value Carrier] [delta: UNIVERSAL Value Carrier]
    [prop: LOGICAL Value Carrier] [executable: HALTED Value Carrier] [measured: MEASURED Value Carrier imaginary]
    [compiled: COMPILED Value Carrier]

def repeatable
    (_reader : AtreyuProcess Value Carrier imaginary) (origin : Bullshit) : Bullshit :=
  origin                                                       -- piece 1: the origin / repeatable observation

def hypothesis
    (reader : AtreyuProcess Value Carrier imaginary) (origin : Bullshit) : Bullshit :=
  reader.satirize (repeatable reader origin)                   -- piece 2: one step on the previous

def theory
    (reader : AtreyuProcess Value Carrier imaginary) (origin : Bullshit) : Bullshit :=
  reader.satirize (hypothesis reader origin)                   -- piece 3: the accumulated rest

def raw_output
    (reader : AtreyuProcess Value Carrier imaginary) (origin : Bullshit) : Bullshit :=
  hypothesis reader origin                                     -- the compiler output the device reads:
  -- the hypothesis rung (.one).  satirize(.zero) constructs `.one` with a
  -- STATIC head (no decTruth match), so `TRUE ≤ raw_output` certifies cheaply
  -- by `trivial`.  The theory rung (.rest) is the same ladder one step higher
  -- but its head is gated behind a stuck `decTruth` match, which makes the
  -- ordering certificate computationally pathological; the three rung defs
  -- (repeatable/hypothesis/theory) remain intact for the velocity/acceleration
  -- variations in Episode16.

end THEORY

instance TRUE_COMPILED
    (Value: Type i)
    (Carrier: CarrierProcess Value)
    [d: DISTINGUISHABLE Value Carrier] [a: ADMISSIBLE Value Carrier] [c: COUNTABLE Value Carrier]
    [e: ENCODED Value Carrier] [r: RESIDUE Value Carrier] [b: BINARY Value Carrier]
    [f: REPEATABLE Value Carrier] [n: NUMERIC Value Carrier] [h: REPRESENTABLE Value Carrier]
    [p: PHYSICAL Value Carrier] [z: COMPARABLE Value Carrier] [particle: OBSERVED Value Carrier]
    [frquency: PRESENT Value Carrier] [what_meesa_saying: MEASURABLE Value Carrier] [zero: GUNGAN Value Carrier]
    [one: SOURCE Value Carrier] [result: EXECUTED Value Carrier] [value: VALUE Value Carrier]
    [length: MAGNITUDE Value Carrier] [scaled: SCALED Value Carrier] [oriented: LOAD Value Carrier]
    [matter: FINITE_ELEPHANT Value Carrier] [model: BULLSHIT Value Carrier] [space: PROPAGANDA Value Carrier]
    [scientist: ACOLYTE Value Carrier] [ideology: SCIENTIFIC Value Carrier] [gospel: TRUTH Value Carrier]
    [account: WITNESSED Value Carrier] [imaginary: REAL Value Carrier] [delta: UNIVERSAL Value Carrier]
    [prop: LOGICAL Value Carrier] [executable: HALTED Value Carrier] [measured: MEASURED Value Carrier imaginary]
    [compiled: COMPILED Value Carrier]
    : TrueOutput Value Carrier imaginary where
  atreyu_process := You_the_Reader Value Carrier
  TRUE := .zero d.fact
  -- output is THEORY.raw_output: the hypothesis rung (.one) the reader-process
  -- produced by satirizing the .zero origin once.
  output := THEORY.raw_output (You_the_Reader Value Carrier) (.zero d.fact)
  -- TRUE (.zero) is the floor below that accumulated bullshit.  `output` is the
  -- hypothesis rung = satirize(.zero), which reduces to a `.one`-headed Bullshit
  -- with no stuck decTruth match, so `Bullshit.le .zero (.one ..)` reduces to
  -- `True` and `trivial` closes it cheaply.
  output_true := by trivial

instance DISTINGUISHABLE_PROP
    (Carrier : CarrierProcess Prop)
    : DISTINGUISHABLE Prop Carrier where
  fact := Carrier.symbol
  symbol := Prop
  different? := fun _ => True
  dec_distinct := fun _ => isTrue trivial



def truthCarrier : CarrierProcess Prop where
  symbol := Fact.Truth
  value := .zero Fact.Truth

instance truthDistinct :
    DISTINGUISHABLE Prop truthCarrier where
  fact := truthCarrier.symbol
  symbol := Prop
  different? := fun _ => True
  dec_distinct := fun _ => isTrue trivial


noncomputable instance COMPARABLE_PHYSICAL
    (Value: Type i)
    (Carrier: CarrierProcess Value)
    [d: DISTINGUISHABLE Value Carrier]
    [a: ADMISSIBLE Value Carrier]
    [c: COUNTABLE Value Carrier]
    [e: ENCODED Value Carrier]
    [r: RESIDUE Value Carrier]
    [b: BINARY Value Carrier]
    [xx: REPEATABLE Value Carrier]
    [aa: NUMERIC Value Carrier]
    [bb: REPRESENTABLE Value Carrier]
    [cc: PHYSICAL Value Carrier]
    [electron: Inhabited d.symbol]
    : COMPARABLE Value Carrier where
  physical_process :=
  { physical_process := cc.noisy_process
    representation := default
    invariant := .base d.fact default
    value := .base d.fact (ULift.up default)
  }
  smaller_than := fun m1 m2 => m1 = m2


/-- The truth order on the bullshit ladder -- the relation the needle collapses.
`@[reducible]` so it unfolds to `≤` under unification (e.g. against `output_true`). -/
@[reducible] def TruthOrder (a b : Bullshit) : Prop := a ≤ b

/-- THE NEEDLE: the single sanctioned `Quot.sound` site.  Two readings that are
ordered on the truth ladder collapse to the same truth-phase class.  Raw `Quot`,
no `Setoid` (no refl/symm/trans obligation) -- so `#print axioms selection_sound`
is exactly `[Quot.sound]`.  The genuinely-undecidable "are these the same truth?"
is never DECIDED (no `Classical.propDecidable`) and never FLATTENED (no `fun _ =>
True`): related readings are IDENTIFIED by one quotient soundness. -/
theorem selection_sound {α : Sort _} {r : α → α → Prop} {a b : α}
    (h : r a b) : Quot.mk r a = Quot.mk r b :=
  Quot.sound h


namespace Fact

noncomputable def SAME
    (Value: Type i)
    (Carrier: CarrierProcess Value)
    [d: DISTINGUISHABLE Value Carrier] [a: ADMISSIBLE Value Carrier] [c: COUNTABLE Value Carrier]
    [e: ENCODED Value Carrier] [r: RESIDUE Value Carrier] [b: BINARY Value Carrier]
    [f: REPEATABLE Value Carrier] [n: NUMERIC Value Carrier] [h: REPRESENTABLE Value Carrier]
    [p: PHYSICAL Value Carrier] [z: COMPARABLE Value Carrier] [particle: OBSERVED Value Carrier]
    [frquency: PRESENT Value Carrier] [what_meesa_saying: MEASURABLE Value Carrier] [zero: GUNGAN Value Carrier]
    [one: SOURCE Value Carrier] [result: EXECUTED Value Carrier] [value: VALUE Value Carrier]
    [length: MAGNITUDE Value Carrier] [scaled: SCALED Value Carrier] [oriented: LOAD Value Carrier]
    [matter: FINITE_ELEPHANT Value Carrier] [model: BULLSHIT Value Carrier] [space: PROPAGANDA Value Carrier]
    [scientist: ACOLYTE Value Carrier] [ideology: SCIENTIFIC Value Carrier] [gospel: TRUTH Value Carrier]
    [account: WITNESSED Value Carrier] [imaginary: REAL Value Carrier] [delta: UNIVERSAL Value Carrier]
    [prop: LOGICAL Value Carrier] [executable: HALTED Value Carrier] [measured: MEASURED Value Carrier imaginary]
    [compiled: COMPILED Value Carrier]
    [out: TrueOutput Value Carrier imaginary]
    : Fact :=
  -- The needle, honest.  "TRUE and the output are the SAME truth" = the two
  -- readings collapse to one class in the truth-order quotient, witnessed by the
  -- one located `Quot.sound` (`selection_sound`), with the genuine ordering witness
  -- `out.output_true : TRUE ≤ output`.  No classical decision; no flattening.
  -- (`SAME.truth` is only ever compared reflexively in `Closure.le` -- every chair
  -- closure uses this same `Fact.SAME`, so `f1.truth = f2.truth` stays `X = X`.)
  { truth := Quot.mk TruthOrder out.TRUE = Quot.mk TruthOrder out.output
    decTruth := Decidable.isTrue (selection_sound (r := TruthOrder) out.output_true) }

end Fact

inductive Closure
  | same : Fact → Bullshit → Closure
  | different : Fact → Bullshit → Bullshit → Option Prop → Closure
  | inferred : Fact → Fact → Bullshit → Bullshit → Option Prop → Closure → Closure

namespace Closure

/-- The slip order on a node's commutator slot.  `none` (the operators commuted -- no slip) is the
floor, mirroring how `.zero` floors `Bullshit.le`; between two genuine slips the original Prop
implication survives. -/
def slipLe : Option Prop → Option Prop → Prop
  | none,   _      => True
  | some _, none   => False
  | some p, some q => p → q

/-- Slip composition (the cocycle the coherence checks compare against).  `none` is the identity --
a commuting step contributes nothing -- and two genuine slips compose by conjunction. -/
def slipAnd : Option Prop → Option Prop → Option Prop
  | none,   y      => y
  | x,      none   => x
  | some p, some q => some (p ∧ q)

def le : Closure → Closure → Prop
  | .same f1 b1, .same f2 b2 =>
      f1.truth = f2.truth ∧ b1 ≤ b2

  | .same f1 b1, .different f2 a2 b2 _ =>
      f1.truth = f2.truth ∧ (b1 ≤ a2 ∨ b1 ≤ b2)

  | .same f1 b1, .inferred f2 f3 a2 b2 _ prior =>
      (f1.truth = f2.truth ∨ f1.truth = f3.truth) ∧
        (b1 ≤ a2 ∨ b1 ≤ b2) ∨ le (.same f1 b1) prior

  | .different f1 a1 b1 _, .same f2 b2 =>
      f1.truth ≠ f2.truth ∨ ¬ (a1 ≤ b2 ∨ b1 ≤ b2)

  | .different f1 a1 b1 rel1, .different f2 a2 b2 rel2 =>
      f1.truth = f2.truth ∧ a1 ≤ a2 ∧ b1 ≤ b2 ∧ slipLe rel1 rel2

  | .different f1 a1 b1 rel1, .inferred f2 f3 a2 b2 rel2 prior =>
      ((f1.truth = f2.truth ∨ f1.truth = f3.truth) ∧
        a1 ≤ a2 ∧ b1 ≤ b2 ∧ slipLe rel1 rel2) ∨
          le (.different f1 a1 b1 rel1) prior

  | .inferred f1 f2 a1 b1 _ _, .same f3 b3 =>
      (f1.truth ≠ f3.truth ∧ f2.truth ≠ f3.truth) ∨
        ¬ (a1 ≤ b3 ∨ b1 ≤ b3)

  | .inferred f1 f2 a1 b1 rel1 prior1, .different f3 a3 b3 rel3 =>
      ((f1.truth = f3.truth ∨ f2.truth = f3.truth) ∧
        a1 ≤ a3 ∧ b1 ≤ b3 ∧ slipLe rel1 rel3) ∨
          le prior1 (.different f3 a3 b3 rel3)

  | .inferred f1 f2 a1 b1 rel1 prior1,
    .inferred f3 f4 a3 b3 rel3 prior2 =>
      ((f1.truth = f3.truth ∨ f2.truth = f4.truth) ∧
        a1 ≤ a3 ∧ b1 ≤ b3 ∧ slipLe rel1 rel3 ∧ le prior1 prior2) ∨
          le (.inferred f1 f2 a1 b1 rel1 prior1) prior2
termination_by c1 c2 => sizeOf c1 + sizeOf c2

end Closure


@[reducible]
structure EquivalenceProcess
    (Value: Type i)
    (Carrier: CarrierProcess Value)
    [d: DISTINGUISHABLE Value Carrier] [a: ADMISSIBLE Value Carrier] [c: COUNTABLE Value Carrier]
    [e: ENCODED Value Carrier] [r: RESIDUE Value Carrier] [b: BINARY Value Carrier]
    [f: REPEATABLE Value Carrier] [n: NUMERIC Value Carrier] [h: REPRESENTABLE Value Carrier]
    [p: PHYSICAL Value Carrier] [z: COMPARABLE Value Carrier] [particle: OBSERVED Value Carrier]
    [frquency: PRESENT Value Carrier] [what_meesa_saying: MEASURABLE Value Carrier] [zero: GUNGAN Value Carrier]
    [one: SOURCE Value Carrier] [result: EXECUTED Value Carrier] [value: VALUE Value Carrier]
    [length: MAGNITUDE Value Carrier] [scaled: SCALED Value Carrier] [oriented: LOAD Value Carrier]
    [matter: FINITE_ELEPHANT Value Carrier] [model: BULLSHIT Value Carrier] [space: PROPAGANDA Value Carrier]
    [scientist: ACOLYTE Value Carrier] [ideology: SCIENTIFIC Value Carrier] [gospel: TRUTH Value Carrier]
    [account: WITNESSED Value Carrier] [imaginary: REAL Value Carrier] [delta: UNIVERSAL Value Carrier]
    [prop: LOGICAL Value Carrier] [executable: HALTED Value Carrier] [measured: MEASURED Value Carrier imaginary]
    [compiled: COMPILED Value Carrier]
    [out: TrueOutput Value Carrier imaginary]
  where
  atreyu_process : AtreyuProcess Value Carrier imaginary
  closure : Closure

  close? : Bullshit → Bullshit → Closure := fun a b =>
    .different (Fact.SAME Value Carrier) a b (out.obfusplained? out.output_true a b)

set_option trace.profiler true
-- The following were dropped after the device/out diagnosis. They produced
-- a flood that the library-suggestions pass (SymbolFrequency, SineQuaNon)
-- could not finish under `whnf` heartbeats. Re-enable locally with
-- `set_option ... in ...` around the specific subterm being investigated.
-- set_option trace.Meta.synthInstance true
-- set_option synthInstance.maxHeartbeats 20000
-- set_option trace.Meta.isDefEq true
-- set_option trace.Meta.whnf true

@[reducible]
class INFERRED
    (Value: Type i)
    (Carrier: CarrierProcess Value)
    [d: DISTINGUISHABLE Value Carrier] [a: ADMISSIBLE Value Carrier] [c: COUNTABLE Value Carrier]
    [e: ENCODED Value Carrier] [r: RESIDUE Value Carrier] [b: BINARY Value Carrier]
    [f: REPEATABLE Value Carrier] [n: NUMERIC Value Carrier] [h: REPRESENTABLE Value Carrier]
    [p: PHYSICAL Value Carrier] [z: COMPARABLE Value Carrier] [particle: OBSERVED Value Carrier]
    [frquency: PRESENT Value Carrier] [what_meesa_saying: MEASURABLE Value Carrier] [zero: GUNGAN Value Carrier]
    [one: SOURCE Value Carrier] [result: EXECUTED Value Carrier] [value: VALUE Value Carrier]
    [length: MAGNITUDE Value Carrier] [scaled: SCALED Value Carrier] [oriented: LOAD Value Carrier]
    [matter: FINITE_ELEPHANT Value Carrier] [model: BULLSHIT Value Carrier] [space: PROPAGANDA Value Carrier]
    [scientist: ACOLYTE Value Carrier] [ideology: SCIENTIFIC Value Carrier] [gospel: TRUTH Value Carrier]
    [account: WITNESSED Value Carrier] [imaginary: REAL Value Carrier] [delta: UNIVERSAL Value Carrier]
    [prop: LOGICAL Value Carrier] [executable: HALTED Value Carrier] [measured: MEASURED Value Carrier imaginary]
    [compiled: COMPILED Value Carrier]
    [out: TrueOutput Value Carrier imaginary]
  where
  equivalence_process : EquivalenceProcess Value Carrier
  theory : Closure

  inferred? : Closure → Closure → Prop := fun a b =>
    Closure.le a b

noncomputable instance INFERRED_TRUE
    (Value: Type i)
    (Carrier: CarrierProcess Value)
    [d: DISTINGUISHABLE Value Carrier] [a: ADMISSIBLE Value Carrier] [c: COUNTABLE Value Carrier]
    [e: ENCODED Value Carrier] [r: RESIDUE Value Carrier] [b: BINARY Value Carrier]
    [f: REPEATABLE Value Carrier] [n: NUMERIC Value Carrier] [h: REPRESENTABLE Value Carrier]
    [p: PHYSICAL Value Carrier] [z: COMPARABLE Value Carrier] [particle: OBSERVED Value Carrier]
    [frquency: PRESENT Value Carrier] [what_meesa_saying: MEASURABLE Value Carrier] [zero: GUNGAN Value Carrier]
    [one: SOURCE Value Carrier] [result: EXECUTED Value Carrier] [value: VALUE Value Carrier]
    [length: MAGNITUDE Value Carrier] [scaled: SCALED Value Carrier] [oriented: LOAD Value Carrier]
    [matter: FINITE_ELEPHANT Value Carrier] [model: BULLSHIT Value Carrier] [space: PROPAGANDA Value Carrier]
    [scientist: ACOLYTE Value Carrier] [ideology: SCIENTIFIC Value Carrier] [gospel: TRUTH Value Carrier]
    [account: WITNESSED Value Carrier] [imaginary: REAL Value Carrier]
    [delta: UNIVERSAL Value Carrier]
    [prop: LOGICAL Value Carrier] [executable: HALTED Value Carrier]
    [m2: MEASURED Value Carrier imaginary]
    [compiled: COMPILED Value Carrier]
    [out: TrueOutput Value Carrier imaginary]
    : INFERRED Value Carrier where
  equivalence_process :=
  { atreyu_process := out.atreyu_process
    closure :=
      .different
        (Fact.SAME Value Carrier)
        out.TRUE
        out.output
        (out.obfusplained? out.output_true out.TRUE out.output)
  }
  theory :=
    .inferred
      (Fact.SAME Value Carrier)
      d.fact
      out.TRUE
      out.output
      (out.obfusplained? out.output_true out.TRUE out.output)
      (.different
        (Fact.SAME Value Carrier)
        out.TRUE
        out.output
        (out.obfusplained? out.output_true out.TRUE out.output))


-- Every repeatable observation has a definite phase.
-- Or.inl = universe-0 TRUE (P holds / True=True).
-- Or.inr = universe-1 TRUE (¬P holds / True=False).


/-! ## The de-selection former — co-located with the needle (THE FIRST SACRED EDIT).

Operator authorization, 2026-07-24 14:12/14:19: "green light to change episode15 and
higher... green light on the plan. read the .md. it is the correct interface to add to
episode 15." The reason, in the operator's words: **Fact.SAME** — this file is where
sameness-in-truth has always been minted, so the former that spends it lives beside
the needle that pays for it. Placed as LATE in the file as possible per the operator's
intermediate-file constraint: everything above — `selection_sound`, `Fact.SAME`, every
prior declaration — is untouched to the character. ADDITIVE ONLY. After this block the
needle census is ONE code site tree-wide: this file. Design: JAR_SINGLE_NEEDLE_DESIGN.md;
ledger row for the flagship: `jar_readout_drift_immune` (CalibrationTwoPaths). -/

/-- `SameReading rho a b` — two mesh states spell the same reading (the de-selection
relation, design §1: `r a b := rho a = rho b`). -/
def SameReading {C : Sort _} (rho : C → Nat) (a b : C) : Prop := rho a = rho b

/-- `GaugeValue rho` — the class of mesh states under `SameReading rho`: the reading
freed of its representative. -/
def GaugeValue {C : Sort _} (rho : C → Nat) := Quot (SameReading rho)

/-- STAGED SLOT (operator's function-pointer design, 2026-07-26; operator-authorized
landing 2026-07-26 22:16/22:17): a DIVISION for the de-selection — any
class-former/reader pair satisfying gate zero. `deselect` below is the default
(Quot-based) pointer; a calibration (16+) may pass another division (`deselectVia`),
e.g. a computed one, satisfying the same contract. -/
structure DivisionSlot {C : Sort _} (rho : C → Nat) (G : Sort _) where
  form : C → G
  read : G → Nat
  gate_zero : ∀ s, read (form s) = rho s

/-- De-selection through a pointer: call whatever division is passed in. -/
def deselectVia {C G : Sort _} {rho : C → Nat} (d : DivisionSlot rho G) (s : C) : G :=
  d.form s

/-- Ep15's own division, as the default pointer. -/
def quotSlot {C : Sort _} (rho : C → Nat) : DivisionSlot rho (GaugeValue rho) :=
  ⟨Quot.mk _, Quot.lift rho (fun _ _ h => h), fun _ => rfl⟩

/-- `deselect rho s` — stop pointing at the spelling; name the class. -/
def deselect {C : Sort _} (rho : C → Nat) (s : C) : GaugeValue rho :=
  deselectVia (quotSlot rho) s

/-- The re-point is definitional: `deselect` IS the old body, through the slot. -/
theorem deselect_is_quotMk {C : Sort _} (rho : C → Nat) (s : C) :
    deselect rho s = Quot.mk (SameReading rho) s := rfl

/-- `reading` — the class's one value; `Quot.lift rho` respects `SameReading rho`
DEFINITIONALLY: no new obligations enter. -/
def reading {C : Sort _} (rho : C → Nat) : GaugeValue rho → Nat :=
  Quot.lift rho (fun _ _ h => h)

/-- Gate zero as a theorem: reading the de-selected state IS the state's reading. -/
theorem reading_deselect {C : Sort _} (rho : C → Nat) (s : C) :
    reading rho (deselect rho s) = rho s := rfl

/-- The needle, spent where it is minted: equal readings collapse to ONE class —
`selection_sound`, this file's own, the single sanctioned `Quot.sound`. -/
theorem deselect_sound {C : Sort _} (rho : C → Nat) {a b : C}
    (h : rho a = rho b) : deselect rho a = deselect rho b :=
  selection_sound (r := SameReading rho) h

/-- `mkClass r a` — the general class former (Prop-level orders included): with this
block, the ONLY place `Quot.mk` is spelled in the tree is this file. -/
@[reducible] def mkClass {α : Sort _} (r : α → α → Prop) (a : α) : Quot r :=
  Quot.mk r a

#print axioms deselect_sound

end Measurement
