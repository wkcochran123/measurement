
import Measurement.Episode9

-- Homework:

namespace Measurement
@[reducible]
class UNIVERSAL
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
    [matter: FINITE_ELEPHANT Value Carrier]
    [model: BULLSHIT Value Carrier]
    [space: PROPAGANDA Value Carrier]
    [scientist: ACOLYTE Value Carrier]
    [ideology: SCIENTIFIC Value Carrier]
    [gospel: TRUTH Value Carrier]
    [account: WITNESSED Value Carrier]
  where
  theory: FiniteGaugeTheoryOfMeasurement Value Carrier
  invariant: d.fact.symbol
  experience: Variation → Fact := fun variation =>
    match variation with
    | .gateaux _ a b =>
    --                  +--------------  TRUE = True AND Not false lol.
    --                  |                I put a ball-gag on Godel.
    --                  V
        { truth    := (invariant = Fact.Truth.truth ) ∧ ¬(invariant ≠ Fact.Truth.truth)
        --                                                                               covariant: did the direction match the response?
        , decTruth := by
            -- FIX 2: invariant is now a known decidable Prop, so decide can fire.
            -- The Householder Razzle Dazzle holds: P ∧ ¬¬P reduces to P, and P is decidable.
            exact instDecidableAnd
              d.dec_distinct
              (instDecidableNot (instDecidableNot d.dec_distinct)) }

    | .frechet _ a b residue =>
        { truth    := residue      -- the residue IS the fact. strain or no strain.
        , decTruth :=
            -- FIX 3: fix the typo (invarinant -> invariant) and give the right type.
            -- residue : Prop, so we need Decidable residue.
            -- residue = (a ∧ ¬b) from transmute, both a and b are Props from Variation.
            -- We don't have dec instances for a/b in scope here, so we use Classical
            -- as the honest answer: we know it's a Prop, we cannot always decide it.
            --
            -- But! the invariant path gives us our ground:
            -- if invariant is true, the device measured something; residue is the strain.
            -- The compiler asked for decidability. We give it what we have.
            if h : invariant = Fact.Truth.truth
            then
              -- covariant case: invariant matched, residue is the strain a ∧ ¬b
              -- we cannot decide a and b without more structure, so we defer to Classical
              Classical.dec residue
            else
              -- contravariant case: invariant did not match, strain is certain
              Classical.dec residue }
/-
def program : CarrierProcess FiniteGaugeTheoryOfMeasurement := sorry

-- Problem 1: Implement de Morgan's law of the excluded middle.
instance : DISTINGUISHABLE FiniteGaugeTheoryOfMeasurement program := sorry

-- My answer:
def program : CarrierProcess FiniteGaugeTheoryOfMeasurement where
--                  +---------------------------    Weierstrauss Approximation Theorem  cuz Fuck the Continuum Hypothesis
--                  |                               I can make that three pointer all day long.  Swish.
--                  V
  symbol := { truth := False, decTruth := Decidable.isFalse (fun h => h) }
  value  := .one Fact.Truth (.zero Fact.Truth)


-- I believe this demonstrates Euler-Lagrange.  I mean, it had to demonstrate
-- a solution to Euler-Lagrange to compile.
-/


end Measurement
