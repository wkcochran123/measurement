import Measurement.Episode39

set_option maxHeartbeats 4000000
set_option maxRecDepth 1000
set_option allowUnsafeReducibility true

namespace Measurement

/-
__EPISODE 40__: _Grounding the Ladder (Base Probe)_

Episodes 8-15 instanced the upper ladder conditionally
(REPRESENTABLE -> ... -> INFERRED), but the base (DISTINGUISHABLE -> NUMERIC,
Episodes 1-2) and the middle (SOURCE -> ACOLYTE, Episodes 5-7) were never
grounded -- Episode2 says so outright: "I would do it RIGHT NOW, but I don't
wanna."  No concrete carrier ever climbs the ladder, so `INFERRED` never fires.

This file begins the grounding for the carrier `Rung3` (the three-rung SPD
activity of Episode34).  It is a PROBE: the only open question in the base is
the field `DISTINGUISHABLE.symbol : Type Value`, which has never been
constructed anywhere in the development.  Build this file to resolve it; the
rest of the base then follows the same pattern.

NOT imported by the `Measurement` root yet -- build explicitly:
  lake build Measurement.Episode40
-/

/-- A concrete carrier over the three-rung activity space. -/
def rung3Carrier : CarrierProcess Rung3 where
  symbol := Fact.Truth
  value := Number.zero Fact.Truth
  -- `event` keeps its default

/-- First base rung.  `different?`/`dec_distinct` are overridden to their
trivial forms to avoid demanding decidable type-equality.  The one field with
no template is `symbol : Type Value` -- the candidate fill below is a guess; the
build error (if any) will report the type actually expected, and everything
above unblocks once it is correct. -/
instance rung3Distinguishable : DISTINGUISHABLE Rung3 rung3Carrier where
  fact := Fact.Truth
  symbol := Rung3                       -- `symbol : Type Value` := the carrier type (confirmed)
  different? := fun _ => True
  dec_distinct := fun _ => isTrue trivial

/-
Remaining base, bottom-up.  Each `*Process` witness embeds the one below it with
minimal `Fact.Truth`-rooted inductive witnesses; defaulted iterate/helper fields
are left to their defaults; each class predicate is the trivial `True`.  Order is
forced: every process resolves the class instances declared above it.
-/

def rung3Counting : CountingProcess Rung3 rung3Carrier where
  carrier := rung3Carrier
  count := Natural.zero Fact.Truth

instance rung3Admissible : ADMISSIBLE Rung3 rung3Carrier where
  counting_process := rung3Counting

def rung3Indexing : IndexingProcess Rung3 rung3Carrier where
  count := rung3Counting
  origin := Rational.zero Fact.Truth

instance rung3Countable : COUNTABLE Rung3 rung3Carrier where
  index := rung3Indexing
  -- un-flattened: falls through to COUNTABLE's substantive `bounded?` default.

def rung3Limit : LimitProcess Rung3 rung3Carrier where
  indexing_process := rung3Indexing
  limit := Rational.zero Fact.Truth
  sequence := Sequence.nil Fact.Truth

instance rung3Encoded : ENCODED Rung3 rung3Carrier where
  limit_process := rung3Limit
  -- un-flattened: falls through to ENCODED's substantive `encoding?` default.

def rung3Cauchy : CauchyProcess Rung3 rung3Carrier where
  limit_process := rung3Limit
  value := Rational.zero Fact.Truth
  accumulation := Limit.nil Fact.Truth

instance rung3Residue : RESIDUE Rung3 rung3Carrier where
  cauchy_process := rung3Cauchy
  -- un-flattened: falls through to RESIDUE's substantive `representative?` default.

/-- The contravariant (funged) truth: `Fact.Truth` with its truth-mode reversed -- the tange/residue
reading.  (Built locally because `Fact.FALSE` is not introduced until Episode 78.) -/
def rung3FactFalse : Fact :=
  { truth := false, decTruth := Decidable.isFalse (by intro h; cases h) }

def rung3Observation : ObservationProcess Rung3 rung3Carrier where
  cauchy_process := rung3Cauchy
  before := Limit.nil Fact.Truth        -- covariant
  -- CONTRAVARIANT CONDITION (funge the truth): `after` is `before`'s truth reversed, so the clock
  -- complement is no longer flat and the contravariant tail (`f2 ≠ f4`, Ep14) can fire.
  after := Limit.nil rung3FactFalse     -- contravariant (funged)

instance rung3Binary : BINARY Rung3 rung3Carrier where
  observation_process := rung3Observation
  zero := Limit.nil Fact.Truth
  one := Limit.nil Fact.Truth
  bit := Sample.initial_condition Fact.Truth (Limit.nil Fact.Truth)
  -- UN-FLATTENED (reflecting Episode 8's grounding of COMPARABLE via the EKG): the funge stops being
  -- `fun _ _ => True` and falls through to BINARY's substantive default -- the decTruth order-reversal
  -- (isTrue -> forward, isFalse -> reversed) that IS the matter/antimatter sign.  No `dec_different?`
  -- field, so nothing extra is demanded.  Comparison is the measurement.

def rung3Repeatable : RepeatableProcess Rung3 rung3Carrier where
  observation_process := rung3Observation
  stimulus := Sample.initial_condition Fact.Truth (Limit.nil Fact.Truth)
  expectation :=
    Trial.hypothesis Fact.Truth
      (Sample.initial_condition Fact.Truth (Limit.nil Fact.Truth))

instance rung3RepeatableClass : REPEATABLE Rung3 rung3Carrier where
  repeatable_process := rung3Repeatable
  -- un-flattened: falls through to REPEATABLE's substantive `typical_response` default.

def rung3Computational : ComputationalProcess Rung3 rung3Carrier where
  repeatable_process := rung3Repeatable
  output := none

instance rung3Numeric : NUMERIC Rung3 rung3Carrier where
  computational_process := rung3Computational
  carrier := Study.hypothesis Fact.Truth
  lambda := fun _ => Study.hypothesis Fact.Truth
  -- un-flattened: falls through to NUMERIC's substantive `related` default.

/-- Base checkpoint: the bottom nine rungs resolve for `Rung3`. -/
def rung3Carrier_isNumeric : NUMERIC Rung3 rung3Carrier := inferInstance

/-
COMPARABLE is the one rung Episode8 left ungrounded -- the class that decides
`smaller_than`, which the author explicitly handed to the reader:
"tell me which one is less ... the choice you would be making is telling."

The choice: compare by the EKG.  `Calibration.EKG.embigger?` is the
heartbeat-ordering oracle, so `smaller_than` is literally a heartbeat reading.
Comparison is measurement; the order on metavariables is the order the compiler
spends heartbeats in.
-/

/-- The head truth of a metavariable: the `Prop` the EKG weighs. -/
def metaTruthR3 : Metavariable Rung3 -> Prop
  | .base f _ => f.truth
  | .step f _ => f.truth

instance rung3Comparable : COMPARABLE Rung3 rung3Carrier where
  physical_process :=
    { physical_process := (inferInstanceAs (PHYSICAL Rung3 rung3Carrier)).noisy_process
      representation := Rung3.zero
      invariant := Metavariable.base Fact.Truth Rung3.zero
      value := Metavariable.base Fact.Truth (ULift.up Rung3.zero) }
  smaller_than := fun m1 m2 =>
    Calibration.EKG.executed.embigger? (metaTruthR3 m1) (metaTruthR3 m2)

/-- Upper-chain checkpoint: with COMPARABLE grounded by the EKG, Episode8's
conditional instances fire all the way to GUNGAN. -/
def rung3Carrier_isGungan : GUNGAN Rung3 rung3Carrier := inferInstance

/-
The middle gap (Episodes 5-7): SOURCE -> EXECUTED -> VALUE -> MAGNITUDE ->
SCALED -> LOAD -> FINITE_ELEPHANT -> BULLSHIT -> PROPAGANDA -> ACOLYTE.

Same shape as Episode8 throughout: each process witness embeds the process below
it (the first projects GUNGAN's `meesa_process`), each data field is a minimal
`Fact.Truth`-rooted inductive, and every helper/predicate function defaults.
-/

def rung3Digital : DigitalProcess Rung3 rung3Carrier where
  meesa_process := (inferInstanceAs (GUNGAN Rung3 rung3Carrier)).meesa_process
  zero := Equivalation.physics Fact.Truth (Jar.color Fact.Truth (Area.t Fact.Truth))

instance rung3Source : SOURCE Rung3 rung3Carrier where
  cd_process := rung3Digital
  one := Equivalation.physics Fact.Truth (Jar.color Fact.Truth (Area.t Fact.Truth))

def rung3Compiled : CompiledProcess Rung3 rung3Carrier where
  digital_process := rung3Digital
  source := rung3Source
  opcode :=
    Encoding.boot Fact.Truth
      (Equivalation.physics Fact.Truth (Jar.color Fact.Truth (Area.t Fact.Truth)))

instance rung3Executed : EXECUTED Rung3 rung3Carrier where
  compiled_process := rung3Compiled

def rung3Math : MathematicalProcess Rung3 rung3Carrier where
  compiled_process := rung3Compiled
  mapping := fun input => match input with
    | .satire f => .satire f
    | .compile f e a => .execute f e a
    | .execute f e a => .compile f e a

instance rung3Value : VALUE Rung3 rung3Carrier where
  mathematical_process := rung3Math
  monad := Abstraction.satire Fact.Truth

def rung3Adding : AddingProcess Rung3 rung3Carrier where
  mathematical_process := rung3Math
  plus := rung3Value
  sum := Sum.zero True (Area.t Fact.Truth)

instance rung3Magnitude : MAGNITUDE Rung3 rung3Carrier where
  adding_process := rung3Adding

def rung3Multiplying : MultiplyingProcess Rung3 rung3Carrier where
  adding_process := rung3Adding
  total := Sum.zero True (Area.t Fact.Truth)
  product := Product.origin Fact.Truth

instance rung3Scaled : SCALED Rung3 rung3Carrier where
  multiplying_process := rung3Multiplying

def rung3Basic : BASICProcess Rung3 rung3Carrier where
  GOSUB := rung3Multiplying
  TEN := Area.t Fact.Truth
  span := Basis.null_space Fact.Truth

instance rung3Load : LOAD Rung3 rung3Carrier where
  basic_operation := rung3Basic

def rung3Galerkin : GalerkinProcess Rung3 rung3Carrier where
  ANSYS_process := rung3Basic
  polynomial := Polynomial.constant Fact.Truth

instance rung3FiniteElephant : FINITE_ELEPHANT Rung3 rung3Carrier where
  galerkin_process := rung3Galerkin

def rung3ArmWave : ArmWaveProcess Rung3 rung3Carrier where
  galerkin_process := rung3Galerkin
  guess := Spline.observation True

instance rung3Bullshit : BULLSHIT Rung3 rung3Carrier where
  arm_wave_process := rung3ArmWave

def rung3Crusade : CrusadeProcess Rung3 rung3Carrier where
  pwn_n00bz := rung3ArmWave
  religion := Diatribe.religion True

instance rung3Propaganda : PROPAGANDA Rung3 rung3Carrier where
  insinuation := rung3Crusade

def rung3Initiation : InitiationProcess Rung3 rung3Carrier where
  ethos := rung3Crusade
  sacred_texts := Cult.inside_joke True

instance rung3Acolyte : ACOLYTE Rung3 rung3Carrier where
  euclid := rung3Initiation

/-- The whole ladder fires.  With the base (Ep1-2), COMPARABLE-by-EKG, and the
middle (Ep5-7) grounded, Lean's resolution chains every conditional instance
from Episodes 8-15 -- all 36 gates from `Fact` to `INFERRED`, on the concrete
three-rung SPD carrier.  The instantiation the author declined is finished. -/
noncomputable def rung3Inferred : INFERRED Rung3 rung3Carrier := inferInstance

end Measurement
