import Measurement.Episode14

set_option maxHeartbeats 4000000
set_option maxRecDepth 1000
set_option allowUnsafeReducibility true


namespace Measurement

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
    (Value: Type)
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
    [account: WITNESSED Value Carrier] [epsilon: LOCAL Value Carrier] [delta: UNIVERSAL Value Carrier]
    [prop: LOGICAL Value Carrier] [executable: HALTED Value Carrier] [measured: MEASURED Value Carrier]
    [compiled: COMPILED Value Carrier] where
  compiler_output: CompilerOutput Value Carrier
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

  | .rest f1 f2 rel n1 n2 n3 statement prior_proof if_true if_false =>
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







@[reducible]
class TrueOutput
    (Value: Type)
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
    [account: WITNESSED Value Carrier] [epsilon: LOCAL Value Carrier] [delta: UNIVERSAL Value Carrier]
    [prop: LOGICAL Value Carrier] [executable: HALTED Value Carrier] [measured: MEASURED Value Carrier]
    [compiled: COMPILED Value Carrier]
  where
  atreyu_process : AtreyuProcess Value Carrier
  output : Bullshit := atreyu_process.satirize atreyu_process.next_measurement

  obfusplained? : Bullshit → Bullshit → Prop := fun a b => a < b

instance TRUE_COMPILED
    (Value: Type)
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
    [account: WITNESSED Value Carrier] [epsilon: LOCAL Value Carrier] [delta: UNIVERSAL Value Carrier]
    [prop: LOGICAL Value Carrier] [executable: HALTED Value Carrier] [measured: MEASURED Value Carrier]
    [compiled: COMPILED Value Carrier]
    : TrueOutput Value Carrier where
  atreyu_process :=
  { compiler_output := compiled.compiler_output
    next_measurement := .zero d.fact
    stress := Carrier.value
    proof := compiled.object_file
  }

noncomputable instance DISTINGUISHABLE_PROP
    (Carrier : CarrierProcess Prop)
    : DISTINGUISHABLE Prop Carrier where
  fact := Carrier.symbol
  symbol := Prop
  dec_distinct := by
    intro s
    exact Classical.propDecidable (s ≠ Prop)



def truthCarrier : CarrierProcess Prop where
  symbol := Fact.Truth
  value := .zero Fact.Truth

noncomputable instance truthDistinct :
    DISTINGUISHABLE Prop truthCarrier where
  fact := truthCarrier.symbol
  symbol := Prop
  dec_distinct := by
    intro s
    exact Classical.propDecidable (s≠Prop)


noncomputable instance COMPARABLE_PHYSICAL
    (Value: Type)
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


namespace Fact

noncomputable def SAME
    (Value: Type)
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
    [account: WITNESSED Value Carrier] [epsilon: LOCAL Value Carrier] [delta: UNIVERSAL Value Carrier]
    [prop: LOGICAL Value Carrier] [executable: HALTED Value Carrier] [measured: MEASURED Value Carrier]
    [compiled: COMPILED Value Carrier]
    [out: TrueOutput Value Carrier]
    : Fact :=
  { truth := Subsingleton (out.obfusplained? (.zero Fact.Truth) out.atreyu_process.next_measurement)
    decTruth := Decidable.isTrue inferInstance }

end Fact

inductive Closure
  | same : Fact → Bullshit → Closure
  | different : Fact → Bullshit → Bullshit → Prop → Closure
  | inferred : Fact → Fact → Bullshit → Bullshit → Prop → Closure → Closure

namespace Closure

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
      f1.truth = f2.truth ∧ a1 ≤ a2 ∧ b1 ≤ b2 ∧ (rel1 → rel2)

  | .different f1 a1 b1 rel1, .inferred f2 f3 a2 b2 rel2 prior =>
      ((f1.truth = f2.truth ∨ f1.truth = f3.truth) ∧
        a1 ≤ a2 ∧ b1 ≤ b2 ∧ (rel1 → rel2)) ∨
          le (.different f1 a1 b1 rel1) prior

  | .inferred f1 f2 a1 b1 _ _, .same f3 b3 =>
      (f1.truth ≠ f3.truth ∧ f2.truth ≠ f3.truth) ∨
        ¬ (a1 ≤ b3 ∨ b1 ≤ b3)

  | .inferred f1 f2 a1 b1 rel1 prior1, .different f3 a3 b3 rel3 =>
      ((f1.truth = f3.truth ∨ f2.truth = f3.truth) ∧
        a1 ≤ a3 ∧ b1 ≤ b3 ∧ (rel1 → rel3)) ∨
          le prior1 (.different f3 a3 b3 rel3)

  | .inferred f1 f2 a1 b1 rel1 prior1,
    .inferred f3 f4 a3 b3 rel3 prior2 =>
      ((f1.truth = f3.truth ∨ f2.truth = f4.truth) ∧
        a1 ≤ a3 ∧ b1 ≤ b3 ∧ (rel1 → rel3) ∧ le prior1 prior2) ∨
          le (.inferred f1 f2 a1 b1 rel1 prior1) prior2
termination_by c1 c2 => sizeOf c1 + sizeOf c2

end Closure


@[reducible]
structure EquivalenceProcess
    (Value: Type)
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
    [account: WITNESSED Value Carrier] [epsilon: LOCAL Value Carrier] [delta: UNIVERSAL Value Carrier]
    [prop: LOGICAL Value Carrier] [executable: HALTED Value Carrier] [measured: MEASURED Value Carrier]
    [compiled: COMPILED Value Carrier]
    [out: TrueOutput Value Carrier]
  where
  atreyu_process : AtreyuProcess Value Carrier
  closure : Closure

  close? : Bullshit → Bullshit → Closure := fun a b =>
    .different (Fact.SAME Value Carrier) a b (out.obfusplained? a b)

@[reducible]
class INFERRED
    (Value: Type)
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
    [account: WITNESSED Value Carrier] [epsilon: LOCAL Value Carrier] [delta: UNIVERSAL Value Carrier]
    [prop: LOGICAL Value Carrier] [executable: HALTED Value Carrier] [measured: MEASURED Value Carrier]
    [compiled: COMPILED Value Carrier]
    [out: TrueOutput Value Carrier]
  where
  equivalence_process : EquivalenceProcess Value Carrier
  theory : Closure

  inferred? : Closure → Closure → Prop := fun a b =>
    Closure.le a b

noncomputable instance INFERRED_TRUE
    (Value: Type)
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
    [account: WITNESSED Value Carrier] [epsilon: LOCAL Value Carrier] [delta: UNIVERSAL Value Carrier]
    [prop: LOGICAL Value Carrier] [executable: HALTED Value Carrier] [measured: MEASURED Value Carrier]
    [compiled: COMPILED Value Carrier]
    [out: TrueOutput Value Carrier]
    : INFERRED Value Carrier where
  equivalence_process :=
  { atreyu_process := out.atreyu_process
    closure :=
      .different
        (Fact.SAME Value Carrier)
        (.zero Fact.Truth)
        out.atreyu_process.next_measurement
        (out.obfusplained? (.zero Fact.Truth) out.atreyu_process.next_measurement)
  }
  theory :=
    .inferred
      (Fact.SAME Value Carrier)
      d.fact
      (.zero Fact.Truth)
      out.atreyu_process.next_measurement
      (out.obfusplained? (.zero Fact.Truth) out.atreyu_process.next_measurement)
      (.different
        (Fact.SAME Value Carrier)
        (.zero Fact.Truth)
        out.atreyu_process.next_measurement
        (out.obfusplained? (.zero Fact.Truth) out.atreyu_process.next_measurement))

-- De Morgan clock-complement: a failed joint phase distributes into a
-- complement phase. Names the classical-duality bridge explicitly.
noncomputable def deMorganClockComplement (P Q : Prop) :
    ¬(P ∧ Q) → ¬P ∨ ¬Q := by
  intro h
  by_cases hp : P
  · exact Or.inr (fun hq : Q => h ⟨hp, hq⟩)
  · exact Or.inl hp

-- Every repeatable observation has a definite phase.
-- Or.inl = universe-0 TRUE (P holds / True=True).
-- Or.inr = universe-1 TRUE (¬P holds / True=False).
noncomputable def truthPhase (P : Prop) : P ∨ ¬P :=
  Classical.em P

noncomputable instance truthRepeatable_fixedPoint
    [xx : REPEATABLE Prop truthCarrier]
    : Inhabited (
        xx.typical_response
          xx.repeatable_process.expectation
          xx.repeatable_process.expectation
        ∨
        ¬ (xx.typical_response
             xx.repeatable_process.expectation
             xx.repeatable_process.expectation)) :=
  ⟨truthPhase
      (xx.typical_response
         xx.repeatable_process.expectation
         xx.repeatable_process.expectation)⟩

noncomputable def theory_true? : Prop :=
  (inferInstance : INFERRED Prop truthCarrier).inferred?
    (inferInstance : INFERRED Prop truthCarrier).equivalence_process.closure
    (inferInstance : INFERRED Prop truthCarrier).theory

#check theory_true?

end Measurement
