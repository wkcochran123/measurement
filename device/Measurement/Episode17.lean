
import Measurement.Episode15
namespace Measurement

/-
SONAR SIMULATOR RECEIVER API

Episode16 transmits a fully assembled carrier into the measurement channel.
This episode is documented as if it were the receive-side API for a sonar
simulator.  Each Lean `*_backward` instance is the implementation of the Python
function named immediately above it.

API conventions:

* `before` is the transmitted reference stack.
* `after` is the already-decoded return stack.
* `carrier` is the simulated propagation medium.
* the return annotation is the next recovered sonar channel.

The API is contravariant: the receiver starts at the far echo and walks back
toward the low-level carrier bands.  The compiled/measured/halted section is a
branch/merge network; the later section is a descending channel decoder.
-/

/--
```python
def lock_far_ping(before: ReferenceStack, carrier: Medium) -> TrueOutput:
    """Acquire the far echo before any range channel has been decoded."""
```

Implementation note: the reader process is used as the return transducer.  The
receiver emits a raw `TrueOutput` lock bit; no returned `after` stack exists at
this range yet.
-/
instance (priority := low) INFERRED_TrueOutput_backward
    (Value: Type i)
    (PropCarrier: CarrierProcess Value)
    [b1_before:  DISTINGUISHABLE Value PropCarrier]   [b2_before:  ADMISSIBLE Value PropCarrier]        [b3_before:  COUNTABLE Value PropCarrier]
    [b4_before:  ENCODED Value PropCarrier]           [b5_before:  RESIDUE Value PropCarrier]           [b6_before:  BINARY Value PropCarrier]
    [b7_before:  REPEATABLE Value PropCarrier]        [b8_before:  NUMERIC Value PropCarrier]           [b9_before:  REPRESENTABLE Value PropCarrier]
    [b10_before: PHYSICAL Value PropCarrier]          [b11_before: COMPARABLE Value PropCarrier]        [b12_before: OBSERVED Value PropCarrier]
    [b13_before: PRESENT Value PropCarrier]           [b14_before: MEASURABLE Value PropCarrier]        [b15_before: GUNGAN Value PropCarrier]
    [b16_before: SOURCE Value PropCarrier]            [b17_before: EXECUTED Value PropCarrier]          [b18_before: VALUE Value PropCarrier]
    [b19_before: MAGNITUDE Value PropCarrier]         [b20_before: SCALED Value PropCarrier]            [b21_before: LOAD Value PropCarrier]
    [b22_before: FINITE_ELEPHANT Value PropCarrier]   [b23_before: BULLSHIT Value PropCarrier]          [b24_before: PROPAGANDA Value PropCarrier]
    [b25_before: ACOLYTE Value PropCarrier]           [b26_before: SCIENTIFIC Value PropCarrier]        [b27_before: TRUTH Value PropCarrier]
    [b28_before: WITNESSED Value PropCarrier]         [b29_before: REAL Value PropCarrier]
    [b31_before: UNIVERSAL Value PropCarrier]         [b32_before: LOGICAL Value PropCarrier]           [b33_before: HALTED Value PropCarrier]
    [b34_before: MEASURED Value PropCarrier b29_before]          [b35_before: COMPILED Value PropCarrier]
    (_ : CarrierProcess Value)
  : TrueOutput Value PropCarrier b29_before :=
  {
    atreyu_process := You_the_Reader Value PropCarrier
    output         := THEORY.raw_output (You_the_Reader Value PropCarrier) (.zero b1_before.fact)
    output_true    := by trivial
  }

/--
```python
def strap_echo_cell(
    before: ReferenceStack,
    after: ReturnStack[TrueOutput, Compiled],
    carrier: Medium,
) -> Compiled:
    """Demodulate the far ping onto the compiler tape."""
```

Implementation note: the receiver appends one strap cell to the transmitted
object file.  This is a tape update, not a semantic decode.
-/
instance (priority := low) TrueOutput_COMPILED_backward
    (Value: Type i)
    (PropCarrier: CarrierProcess Value)
    [b1_before:  DISTINGUISHABLE Value PropCarrier]   [b2_before:  ADMISSIBLE Value PropCarrier]        [b3_before:  COUNTABLE Value PropCarrier]
    [b4_before:  ENCODED Value PropCarrier]           [b5_before:  RESIDUE Value PropCarrier]           [b6_before:  BINARY Value PropCarrier]
    [b7_before:  REPEATABLE Value PropCarrier]        [b8_before:  NUMERIC Value PropCarrier]           [b9_before:  REPRESENTABLE Value PropCarrier]
    [b10_before: PHYSICAL Value PropCarrier]          [b11_before: COMPARABLE Value PropCarrier]        [b12_before: OBSERVED Value PropCarrier]
    [b13_before: PRESENT Value PropCarrier]           [b14_before: MEASURABLE Value PropCarrier]        [b15_before: GUNGAN Value PropCarrier]
    [b16_before: SOURCE Value PropCarrier]            [b17_before: EXECUTED Value PropCarrier]          [b18_before: VALUE Value PropCarrier]
    [b19_before: MAGNITUDE Value PropCarrier]         [b20_before: SCALED Value PropCarrier]            [b21_before: LOAD Value PropCarrier]
    [b22_before: FINITE_ELEPHANT Value PropCarrier]   [b23_before: BULLSHIT Value PropCarrier]          [b24_before: PROPAGANDA Value PropCarrier]
    [b25_before: ACOLYTE Value PropCarrier]           [b26_before: SCIENTIFIC Value PropCarrier]        [b27_before: TRUTH Value PropCarrier]
    [b28_before: WITNESSED Value PropCarrier]         [b29_before: REAL Value PropCarrier]
    [b31_before: UNIVERSAL Value PropCarrier]         [b32_before: LOGICAL Value PropCarrier]           [b33_before: HALTED Value PropCarrier]
    [b34_before: MEASURED Value PropCarrier b29_before]          [b35_before: COMPILED Value PropCarrier]          [b36_before: TrueOutput Value PropCarrier b29_before]
    (_: CarrierProcess Value)
    [b36_after:  TrueOutput Value PropCarrier b29_before]        [b35_after:  COMPILED Value PropCarrier]
  : COMPILED Value PropCarrier :=
  {
    compiler_output :=
      { satire := b34_before.satire                                   -- MEASURED.satire, cf. Episode14:102
        tape   := .strap b1_before.fact Fact.Truth Value (ULift.{i+1, i} Value) b35_before.object_file }
    object_file     := .strap b1_before.fact Fact.Truth Value (ULift.{i+1, i} Value) b35_before.object_file
  }

/--
```python
def branch_compiled_to_halt(
    before: ReferenceStack,
    after: ReturnStack[Measured, Compiled, TrueOutput],
    carrier: Medium,
) -> Halted:
    """Route the compiled echo through the halt branch."""
```

Implementation note: the run-band wrappers stay out of scope.  The receiver
extracts the returned scientific paper and leaves the close predicate at its
default because the measured payload does not expose a close decision.
-/
instance (priority := low) COMPILED_HALTED_backward
    (Value: Type i)
    (PropCarrier: CarrierProcess Value)
    [b1_before:  DISTINGUISHABLE Value PropCarrier]   [b2_before:  ADMISSIBLE Value PropCarrier]        [b3_before:  COUNTABLE Value PropCarrier]
    [b4_before:  ENCODED Value PropCarrier]           [b5_before:  RESIDUE Value PropCarrier]           [b6_before:  BINARY Value PropCarrier]
    [b7_before:  REPEATABLE Value PropCarrier]        [b8_before:  NUMERIC Value PropCarrier]           [b9_before:  REPRESENTABLE Value PropCarrier]
    [b10_before: PHYSICAL Value PropCarrier]          [b11_before: COMPARABLE Value PropCarrier]        [b12_before: OBSERVED Value PropCarrier]
    [b13_before: PRESENT Value PropCarrier]           [b14_before: MEASURABLE Value PropCarrier]        [b15_before: GUNGAN Value PropCarrier]
    [b16_before: SOURCE Value PropCarrier]            [b17_before: EXECUTED Value PropCarrier]          [b18_before: VALUE Value PropCarrier]
    [b19_before: MAGNITUDE Value PropCarrier]         [b20_before: SCALED Value PropCarrier]            [b21_before: LOAD Value PropCarrier]
    [b22_before: FINITE_ELEPHANT Value PropCarrier]   [b23_before: BULLSHIT Value PropCarrier]          [b24_before: PROPAGANDA Value PropCarrier]
    [b25_before: ACOLYTE Value PropCarrier]           [b26_before: SCIENTIFIC Value PropCarrier]        [b27_before: TRUTH Value PropCarrier]
    [b28_before: WITNESSED Value PropCarrier]         [b29_before: REAL Value PropCarrier]              (imaginary: REAL Value PropCarrier)
    -- UNIVERSAL / LOGICAL / HALTED deliberately NOT bound (see the note in MEASURED_HALTED below):
    -- opaque binders are not defeq to the concrete forward instances the nested structures re-synthesize.
    [b34_before: MEASURED Value PropCarrier imaginary]          [b35_before: COMPILED Value PropCarrier]
    (_ : CarrierProcess Value)
    [b34_after: MEASURED Value PropCarrier imaginary]          [b35_after:  COMPILED Value PropCarrier]          [b36_after: TrueOutput Value PropCarrier imaginary]
  : HALTED Value PropCarrier :=
  {
    scientific_paper := b34_after.satire.description
    -- halted? left at its default: MEASURED carries no close?, so the override could never type.
  }

/--
```python
def branch_compiled_to_range(
    before: ReferenceStack,
    after: ReturnStack[TrueOutput, Compiled],
    range_carrier: Medium,
) -> Measured:
    """Route the compiled echo through the measured-range branch."""
```

Implementation note: the receiver preserves the returned description, reads the
range carrier as length, and updates velocity as a propagated distance sample.
The projection is reconstructed locally.
-/
instance (priority := low) COMPILED_MEASURED_backward
    (Value: Type i)
    (PropCarrier: CarrierProcess Value)
    [b1_before:  DISTINGUISHABLE Value PropCarrier]   [b2_before:  ADMISSIBLE Value PropCarrier]        [b3_before:  COUNTABLE Value PropCarrier]
    [b4_before:  ENCODED Value PropCarrier]           [b5_before:  RESIDUE Value PropCarrier]           [b6_before:  BINARY Value PropCarrier]
    [b7_before:  REPEATABLE Value PropCarrier]        [b8_before:  NUMERIC Value PropCarrier]           [b9_before:  REPRESENTABLE Value PropCarrier]
    [b10_before: PHYSICAL Value PropCarrier]          [b11_before: COMPARABLE Value PropCarrier]        [b12_before: OBSERVED Value PropCarrier]
    [b13_before: PRESENT Value PropCarrier]           [b14_before: MEASURABLE Value PropCarrier]        [b15_before: GUNGAN Value PropCarrier]
    [b16_before: SOURCE Value PropCarrier]            [b17_before: EXECUTED Value PropCarrier]          [b18_before: VALUE Value PropCarrier]
    [b19_before: MAGNITUDE Value PropCarrier]         [b20_before: SCALED Value PropCarrier]            [b21_before: LOAD Value PropCarrier]
    [b22_before: FINITE_ELEPHANT Value PropCarrier]   [b23_before: BULLSHIT Value PropCarrier]          [b24_before: PROPAGANDA Value PropCarrier]
    [b25_before: ACOLYTE Value PropCarrier]           [b26_before: SCIENTIFIC Value PropCarrier]        [b27_before: TRUTH Value PropCarrier]
    [b28_before: WITNESSED Value PropCarrier]         [b29_before: REAL Value PropCarrier]              (imaginary: REAL Value PropCarrier)
    -- UNIVERSAL / LOGICAL / HALTED deliberately NOT bound: opaque binders are not defeq to the
    -- concrete forward instances the nested LeanProcess re-synthesizes.
    [b34_before: MEASURED Value PropCarrier imaginary]          [b35_before: COMPILED Value PropCarrier]          [b36_before: TrueOutput Value PropCarrier imaginary]
    (NumberPropCarrier : CarrierProcess Value)
    [b36_after:  TrueOutput Value PropCarrier imaginary]        [b35_after:  COMPILED Value PropCarrier]
  : MEASURED Value PropCarrier imaginary :=
  {
    satire :=
      { description := b35_after.compiler_output.satire.description
        length      := NumberPropCarrier.value
        velocity    := .distance b1_before.fact PropCarrier.value NumberPropCarrier.value Value (ULift.{i+1} Value) b34_before.satire.velocity
        projection  := ULift.{i} (ULift.{i} (ULift.{i} Value)) }
    bounded? := fun a b => Measurement.le a b
  }

/--
```python
def merge_range_into_halt(
    before: ReferenceStack,
    after: ReturnStack[TrueOutput, Compiled, Measured],
    carrier: Medium,
) -> Halted:
    """Merge the measured-range branch back into the halt branch."""
```

Implementation note: the receiver advances the transmitted computer state by
one explicit load transform.  This is a merge operation, not a fresh global
halt solve.
-/
instance (priority := low) MEASURED_HALTED_backward
    (Value: Type i)
    (PropCarrier: CarrierProcess Value)
    [b1_before:  DISTINGUISHABLE Value PropCarrier]   [b2_before:  ADMISSIBLE Value PropCarrier]        [b3_before:  COUNTABLE Value PropCarrier]
    [b4_before:  ENCODED Value PropCarrier]           [b5_before:  RESIDUE Value PropCarrier]           [b6_before:  BINARY Value PropCarrier]
    [b7_before:  REPEATABLE Value PropCarrier]        [b8_before:  NUMERIC Value PropCarrier]           [b9_before:  REPRESENTABLE Value PropCarrier]
    [b10_before: PHYSICAL Value PropCarrier]          [b11_before: COMPARABLE Value PropCarrier]        [b12_before: OBSERVED Value PropCarrier]
    [b13_before: PRESENT Value PropCarrier]           [b14_before: MEASURABLE Value PropCarrier]        [b15_before: GUNGAN Value PropCarrier]
    [b16_before: SOURCE Value PropCarrier]            [b17_before: EXECUTED Value PropCarrier]          [b18_before: VALUE Value PropCarrier]
    [b19_before: MAGNITUDE Value PropCarrier]         [b20_before: SCALED Value PropCarrier]            [b21_before: LOAD Value PropCarrier]
    [b22_before: FINITE_ELEPHANT Value PropCarrier]   [b23_before: BULLSHIT Value PropCarrier]          [b24_before: PROPAGANDA Value PropCarrier]
    [b25_before: ACOLYTE Value PropCarrier]           [b26_before: SCIENTIFIC Value PropCarrier]        [b27_before: TRUTH Value PropCarrier]
    [b28_before: WITNESSED Value PropCarrier]         [b29_before: REAL Value PropCarrier]
    -- UNIVERSAL / LOGICAL / HALTED deliberately NOT bound: opaque binders are not defeq to the
    -- concrete forward instances the nested ElaborationProcess re-synthesizes.
    [b34_before: MEASURED Value PropCarrier b29_before]          [b35_before: COMPILED Value PropCarrier]          [b36_before: TrueOutput Value PropCarrier b29_before]
    (_ : CarrierProcess Value)
    [b36_after:  TrueOutput Value PropCarrier b29_before]        [b35_after:  COMPILED Value PropCarrier]          [b34_after:  MEASURED Value PropCarrier b29_before]
  : HALTED Value PropCarrier :=
  {
    scientific_paper :=
      { b34_before.satire.description with
        -- the concrete forward paper's program (.load, cf. HALTED_LOGICAL) advanced one step by
        -- hand -- execute's load arm written out, since an inferInstance HALTED cannot pin its
        -- universe levels without a binder.
        computer_state := .transform Fact.Truth.truth (¬Fact.Truth.truth) Value (ULift.{i+1} Value)
                            (.load Fact.Truth.truth Value)
      }
  }

/--
```python
def phase_compare_halt_states(
    before: ReferenceStack,
    after: ReturnStack[TrueOutput, Compiled, Measured, Halted],
    carrier: Medium,
) -> Logical:
    """Convert halt-state displacement into a logical phase reading."""
```

Implementation note: the receiver compares transmitted and returned computer
states and stores the result as a geodesic reading.  The echo is now a logical
difference signal.
-/
instance (priority := low) HALTED_LOGICAL_backward
    (Value: Type i)
    (PropCarrier: CarrierProcess Value)
    [b1_before:  DISTINGUISHABLE Value PropCarrier]   [b2_before:  ADMISSIBLE Value PropCarrier]        [b3_before:  COUNTABLE Value PropCarrier]
    [b4_before:  ENCODED Value PropCarrier]           [b5_before:  RESIDUE Value PropCarrier]           [b6_before:  BINARY Value PropCarrier]
    [b7_before:  REPEATABLE Value PropCarrier]        [b8_before:  NUMERIC Value PropCarrier]           [b9_before:  REPRESENTABLE Value PropCarrier]
    [b10_before: PHYSICAL Value PropCarrier]          [b11_before: COMPARABLE Value PropCarrier]        [b12_before: OBSERVED Value PropCarrier]
    [b13_before: PRESENT Value PropCarrier]           [b14_before: MEASURABLE Value PropCarrier]        [b15_before: GUNGAN Value PropCarrier]
    [b16_before: SOURCE Value PropCarrier]            [b17_before: EXECUTED Value PropCarrier]          [b18_before: VALUE Value PropCarrier]
    [b19_before: MAGNITUDE Value PropCarrier]         [b20_before: SCALED Value PropCarrier]            [b21_before: LOAD Value PropCarrier]
    [b22_before: FINITE_ELEPHANT Value PropCarrier]   [b23_before: BULLSHIT Value PropCarrier]          [b24_before: PROPAGANDA Value PropCarrier]
    [b25_before: ACOLYTE Value PropCarrier]           [b26_before: SCIENTIFIC Value PropCarrier]        [b27_before: TRUTH Value PropCarrier]
    [b28_before: WITNESSED Value PropCarrier]         [b29_before: REAL Value PropCarrier]
    [b31_before: UNIVERSAL Value PropCarrier]         [b32_before: LOGICAL Value PropCarrier]           [b33_before: HALTED Value PropCarrier]
    [b34_before: MEASURED Value PropCarrier b29_before]          [b35_before: COMPILED Value PropCarrier]          [b36_before: TrueOutput Value PropCarrier b29_before]
    (_: CarrierProcess Value)
    [b36_after:  TrueOutput Value PropCarrier b29_before]        [b35_after:  COMPILED Value PropCarrier]          [b34_after:  MEASURED Value PropCarrier b29_before]
    [b33_after:  HALTED Value PropCarrier]
  : LOGICAL Value PropCarrier :=
  {
    feelings :=
      { bullshit_meter  := b31_before.the_compiler
        current_reading := .geodesic b1_before.fact Value
                  (b33_before.halted? b33_before.scientific_paper.computer_state b33_after.scientific_paper.computer_state)
                  (ULift.{i+1} Value)
                  b33_before.scientific_paper.stamina.current_reading
                  b33_after.scientific_paper.stamina.current_reading
        accumulated_bullshit := b32_before.feelings.weave? b32_before.feelings.accumulated_bullshit }
    ekg := Calibration.EKG.executed
  }

/--
```python
def fire_universal_transducer(
    before: ReferenceStack,
    after: ReturnStack[Halted, Logical],
    carrier: Medium,
) -> Universal:
    """Compile the logical return through the universal transducer."""
```

Implementation note: the receiver keeps the transmitted compiler, treats the
returned logical reading as source, and applies `photon_torpedo` as the compile
transducer.
-/
instance (priority := low) LOGICAL_UNIVERSAL_backward
    (Value: Type i)
    (PropCarrier: CarrierProcess Value)
    [b1_before:  DISTINGUISHABLE Value PropCarrier]   [b2_before:  ADMISSIBLE Value PropCarrier]        [b3_before:  COUNTABLE Value PropCarrier]
    [b4_before:  ENCODED Value PropCarrier]           [b5_before:  RESIDUE Value PropCarrier]           [b6_before:  BINARY Value PropCarrier]
    [b7_before:  REPEATABLE Value PropCarrier]        [b8_before:  NUMERIC Value PropCarrier]           [b9_before:  REPRESENTABLE Value PropCarrier]
    [b10_before: PHYSICAL Value PropCarrier]          [b11_before: COMPARABLE Value PropCarrier]        [b12_before: OBSERVED Value PropCarrier]
    [b13_before: PRESENT Value PropCarrier]           [b14_before: MEASURABLE Value PropCarrier]        [b15_before: GUNGAN Value PropCarrier]
    [b16_before: SOURCE Value PropCarrier]            [b17_before: EXECUTED Value PropCarrier]          [b18_before: VALUE Value PropCarrier]
    [b19_before: MAGNITUDE Value PropCarrier]         [b20_before: SCALED Value PropCarrier]            [b21_before: LOAD Value PropCarrier]
    [b22_before: FINITE_ELEPHANT Value PropCarrier]   [b23_before: BULLSHIT Value PropCarrier]          [b24_before: PROPAGANDA Value PropCarrier]
    [b25_before: ACOLYTE Value PropCarrier]           [b26_before: SCIENTIFIC Value PropCarrier]        [b27_before: TRUTH Value PropCarrier]
    [b28_before: WITNESSED Value PropCarrier]         [b29_before: REAL Value PropCarrier]
    [b31_before: UNIVERSAL Value PropCarrier]         [b32_before: LOGICAL Value PropCarrier]           [b33_before: HALTED Value PropCarrier]
    [b34_before: MEASURED Value PropCarrier b29_before]          [b35_before: COMPILED Value PropCarrier]          [b36_before: TrueOutput Value PropCarrier b29_before]
    (_: CarrierProcess Value)
    [b36_after:  TrueOutput Value PropCarrier b29_before]        [b35_after:  COMPILED Value PropCarrier]          [b34_after:  MEASURED Value PropCarrier b29_before]
    [b33_after:  HALTED Value PropCarrier]            [b32_after:  LOGICAL Value PropCarrier]
  : UNIVERSAL Value PropCarrier :=
  {
    the_compiler := b31_before.the_compiler
    source_program := b32_after.feelings.current_reading
    compiled_program := b31_before.the_compiler.photon_torpedo b32_after.feelings.current_reading
  }

/--
```python
def solve_local_frame(
    before: ReferenceStack,
    after: ReturnStack[Universal],
    carrier: Medium,
) -> Local:
    """Recover local displacement from the universal return."""
```

Implementation note: the receiver transmutes the transmitted Gateaux variation
and uses the returned compiler delta as local displacement.  The echo is now
localized without leaving the simulator.
-/
instance (priority := low) UNIVERSAL_LOCAL_backward
    (Value: Type i)
    (PropCarrier: CarrierProcess Value)
    [b1_before:  DISTINGUISHABLE Value PropCarrier]   [b2_before:  ADMISSIBLE Value PropCarrier]        [b3_before:  COUNTABLE Value PropCarrier]
    [b4_before:  ENCODED Value PropCarrier]           [b5_before:  RESIDUE Value PropCarrier]           [b6_before:  BINARY Value PropCarrier]
    [b7_before:  REPEATABLE Value PropCarrier]        [b8_before:  NUMERIC Value PropCarrier]           [b9_before:  REPRESENTABLE Value PropCarrier]
    [b10_before: PHYSICAL Value PropCarrier]          [b11_before: COMPARABLE Value PropCarrier]        [b12_before: OBSERVED Value PropCarrier]
    [b13_before: PRESENT Value PropCarrier]           [b14_before: MEASURABLE Value PropCarrier]        [b15_before: GUNGAN Value PropCarrier]
    [b16_before: SOURCE Value PropCarrier]            [b17_before: EXECUTED Value PropCarrier]          [b18_before: VALUE Value PropCarrier]
    [b19_before: MAGNITUDE Value PropCarrier]         [b20_before: SCALED Value PropCarrier]            [b21_before: LOAD Value PropCarrier]
    [b22_before: FINITE_ELEPHANT Value PropCarrier]   [b23_before: BULLSHIT Value PropCarrier]          [b24_before: PROPAGANDA Value PropCarrier]
    [b25_before: ACOLYTE Value PropCarrier]           [b26_before: SCIENTIFIC Value PropCarrier]        [b27_before: TRUTH Value PropCarrier]
    [b28_before: WITNESSED Value PropCarrier]         [b29_before: REAL Value PropCarrier]              [b30_before: LOCAL Value PropCarrier b29_before]
    [b31_before: UNIVERSAL Value PropCarrier]         [LOGICAL Value PropCarrier]           [HALTED Value PropCarrier]
    [MEASURED Value PropCarrier b29_before]          [COMPILED Value PropCarrier]          [TrueOutput Value PropCarrier b29_before]
    (_: CarrierProcess Value)
    [TrueOutput Value PropCarrier b29_before]        [COMPILED Value PropCarrier]          [MEASURED Value PropCarrier b29_before]
    [HALTED Value PropCarrier]            [LOGICAL Value PropCarrier]           [b31_after: UNIVERSAL Value PropCarrier]
  : LOCAL Value PropCarrier b29_before :=
  let g  : Variation :=
    .gateaux b28_before.witness b1_before.fact.truth b30_before.delta b30_before.theory.differential_equation
  let de : Variation :=
    b30_before.theory.transmute g        -- Gateaux → Fréchet: all directions, residue added
  { theory :=
    { universal_observer :=
      { frame_of_reference := b29_before.universal_observer.frame_of_reference
        reality := .logic b1_before.fact.truth }
      differential_equation := de
    }
    delta := b31_after.lake_build b31_before.source_program b31_after.compiled_program
  }

/--
```python
def calibrate_measured_reference(
    carrier: Medium,
    real_frame: Real,
    imaginary_frame: Real,
) -> Measured:
    """Build the pinned measured reference used by the receiver."""
```

Implementation note: this is not a descending echo stage.  It rebuilds a
concrete measured paper so the return path can compare against a pinned range
reference instead of an opaque run-band instance.
-/
instance (priority := low) MEASURED_HALTED
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
    [account: WITNESSED Value Carrier]
    [real: REAL Value Carrier] [imaginary: REAL Value Carrier]   -- the pair
    -- delta / prop / executable bound IN DEPENDENCY ORDER so every occurrence -- the target's
    -- synthesized arguments and the body's projections alike -- resolves to the SAME local
    -- binder.  (A mixed bound/unbound set is what breaks defeq: one side opaque, one concrete.)
    : MEASURED Value Carrier imaginary where
  satire :=
  { description :=
    -- MAKE the scientific paper: once measured AND halted, the heartbeat and calibration
    -- carry up from the logical layer, and the halted program is advanced one step --
    -- the act of measuring -- into the paper's new computer_state (execute's load arm,
    -- written out by hand).  NOTHING above REAL is bound: the tower's classes carry free
    -- universe parameters, so an opaque binder is never defeq to the concrete chain the
    -- target synthesizes -- the heartbeat and calibration are therefore the concrete
    -- LOGICAL_UNIVERSAL / UNIVERSAL_REAL constructions written out from the REAL-level
    -- binders, which ARE universe-pinned.
    { stamina :=
      { bullshit_meter :=
        { derivative :=
          { universal_observer := real.universal_observer
            differential_equation := .gateaux account.witness Fact.Truth.truth d.fact.truth
                                       (.newton account.witness Fact.Truth.truth)
          }
          function := .einstein d.fact
          converged := match d.fact.decTruth with
            | isTrue  _ => Fact.Truth
            | isFalse _ => d.fact
          sink := Type i
        }
        current_reading := .white_hole d.fact Value (.einstein d.fact)
        accumulated_bullshit := .stokes d.fact (.einstein d.fact) d.fact.truth
      }
      calibration := Calibration.EKG.executed
      computer_state := .transform Fact.Truth.truth (¬Fact.Truth.truth) Value (ULift.{i+1} Value)
                          (.load Fact.Truth.truth Value)
    }
    length := Carrier.value
    -- The two binary pieces in the tower: velocity climbs to .speed, the rank-2 node
    -- that carries two Measurement lines at once -- one per local -- contracted by Measurement.le.
    velocity :=
      .speed d.fact Carrier.value Carrier.value Carrier.value
             Value (ULift.{i+1} Value) Value
             (.origin d.fact Carrier.value Value)      -- the real local
             (.origin d.fact Carrier.value Value)      -- the imaginary local
    projection := ULift.{i} (ULift.{i} (ULift.{i} Value))  -- Hmm... wonder what this could mean?
  }


/--
```python
def unwrap_real_channel(
    before: ReferenceStack,
    after: ReturnStack[Universal, Local],
    carrier: Medium,
) -> Real:
    """Promote the localized echo into the reconstructed real channel."""
```

Implementation note: the receiver takes the returned local theory as the current
universe tensor.  This removes one frame wrapper from the echo.
-/
instance (priority := low) LOCAL_REAL_backward
    (Value: Type i)
    (PropCarrier: CarrierProcess Value)
    [b1_before:  DISTINGUISHABLE Value PropCarrier]   [b2_before:  ADMISSIBLE Value PropCarrier]        [b3_before:  COUNTABLE Value PropCarrier]
    [b4_before:  ENCODED Value PropCarrier]           [b5_before:  RESIDUE Value PropCarrier]           [b6_before:  BINARY Value PropCarrier]
    [b7_before:  REPEATABLE Value PropCarrier]        [b8_before:  NUMERIC Value PropCarrier]           [b9_before:  REPRESENTABLE Value PropCarrier]
    [b10_before: PHYSICAL Value PropCarrier]          [b11_before: COMPARABLE Value PropCarrier]        [b12_before: OBSERVED Value PropCarrier]
    [b13_before: PRESENT Value PropCarrier]           [b14_before: MEASURABLE Value PropCarrier]        [b15_before: GUNGAN Value PropCarrier]
    [b16_before: SOURCE Value PropCarrier]            [b17_before: EXECUTED Value PropCarrier]          [b18_before: VALUE Value PropCarrier]
    [b19_before: MAGNITUDE Value PropCarrier]         [b20_before: SCALED Value PropCarrier]            [b21_before: LOAD Value PropCarrier]
    [b22_before: FINITE_ELEPHANT Value PropCarrier]   [b23_before: BULLSHIT Value PropCarrier]          [b24_before: PROPAGANDA Value PropCarrier]
    [b25_before: ACOLYTE Value PropCarrier]           [b26_before: SCIENTIFIC Value PropCarrier]        [b27_before: TRUTH Value PropCarrier]
    [b28_before: WITNESSED Value PropCarrier]         [b29_before: REAL Value PropCarrier]
    [UNIVERSAL Value PropCarrier]         [LOGICAL Value PropCarrier]           [HALTED Value PropCarrier]
    [MEASURED Value PropCarrier b29_before]          [COMPILED Value PropCarrier]          [TrueOutput Value PropCarrier b29_before]
    (_: CarrierProcess Value)
    [TrueOutput Value PropCarrier b29_before]        [COMPILED Value PropCarrier]          [MEASURED Value PropCarrier b29_before]
    [HALTED Value PropCarrier]            [LOGICAL Value PropCarrier]           [b31_after: UNIVERSAL Value PropCarrier]
    [b30_after: LOCAL Value PropCarrier b29_before]
  : REAL Value PropCarrier :=
  {
    universal_observer := b30_after.theory.universal_observer
    current_status := .fact b28_before.witness b1_before.fact.truth (.logic b1_before.fact.truth)
  }

/--
```python
def unwrap_witness_channel(
    before: ReferenceStack,
    after: ReturnStack[Local, Real],
    carrier: Medium,
) -> Witnessed:
    """Recover the reportable witness channel from the real echo."""
```

Implementation note: the receiver reads the returned real status as a witnessed
account.  The real-frame envelope is removed.
-/
instance (priority := low) REAL_WITNESSED_backward
    (Value: Type i)
    (PropCarrier: CarrierProcess Value)
    [b1_before:  DISTINGUISHABLE Value PropCarrier]   [b2_before:  ADMISSIBLE Value PropCarrier]        [b3_before:  COUNTABLE Value PropCarrier]
    [b4_before:  ENCODED Value PropCarrier]           [b5_before:  RESIDUE Value PropCarrier]           [b6_before:  BINARY Value PropCarrier]
    [b7_before:  REPEATABLE Value PropCarrier]        [b8_before:  NUMERIC Value PropCarrier]           [b9_before:  REPRESENTABLE Value PropCarrier]
    [b10_before: PHYSICAL Value PropCarrier]          [b11_before: COMPARABLE Value PropCarrier]        [b12_before: OBSERVED Value PropCarrier]
    [b13_before: PRESENT Value PropCarrier]           [b14_before: MEASURABLE Value PropCarrier]        [b15_before: GUNGAN Value PropCarrier]
    [b16_before: SOURCE Value PropCarrier]            [b17_before: EXECUTED Value PropCarrier]          [b18_before: VALUE Value PropCarrier]
    [b19_before: MAGNITUDE Value PropCarrier]         [b20_before: SCALED Value PropCarrier]            [b21_before: LOAD Value PropCarrier]
    [b22_before: FINITE_ELEPHANT Value PropCarrier]   [b23_before: BULLSHIT Value PropCarrier]          [b24_before: PROPAGANDA Value PropCarrier]
    [b25_before: ACOLYTE Value PropCarrier]           [b26_before: SCIENTIFIC Value PropCarrier]        [b27_before: TRUTH Value PropCarrier]
    [b28_before: WITNESSED Value PropCarrier]         [b29_before: REAL Value PropCarrier]
    [UNIVERSAL Value PropCarrier]         [LOGICAL Value PropCarrier]           [HALTED Value PropCarrier]
    [MEASURED Value PropCarrier b29_before]          [COMPILED Value PropCarrier]          [TrueOutput Value PropCarrier b29_before]
    (_: CarrierProcess Value)
    [TrueOutput Value PropCarrier b29_before]        [COMPILED Value PropCarrier]          [MEASURED Value PropCarrier b29_before]
    [HALTED Value PropCarrier]            [LOGICAL Value PropCarrier]           [b31_after: UNIVERSAL Value PropCarrier]
    [b30_after: LOCAL Value PropCarrier b29_before] [b29_after: REAL Value PropCarrier]
  : WITNESSED Value PropCarrier :=
  {
    baptism := b29_after.universal_observer.frame_of_reference
    witness := b29_after.universal_observer.frame_of_reference.pray? b29_after.universal_observer.frame_of_reference.the_literature
  }

/--
```python
def unwrap_truth_channel(
    before: ReferenceStack,
    after: ReturnStack[Real, Witnessed],
    carrier: Medium,
) -> Truth:
    """Recover the truth-band signal from the witness echo."""
```

Implementation note: the receiver accepts the returned witness channel as the
next decoded band.  This is a truth-band signal, not a global truth claim.
-/
instance (priority := low) WITNESSED_TRUTH_backward
    (Value: Type i)
    (PropCarrier: CarrierProcess Value)
    [b1_before:  DISTINGUISHABLE Value PropCarrier]   [b2_before:  ADMISSIBLE Value PropCarrier]        [b3_before:  COUNTABLE Value PropCarrier]
    [b4_before:  ENCODED Value PropCarrier]           [b5_before:  RESIDUE Value PropCarrier]           [b6_before:  BINARY Value PropCarrier]
    [b7_before:  REPEATABLE Value PropCarrier]        [b8_before:  NUMERIC Value PropCarrier]           [b9_before:  REPRESENTABLE Value PropCarrier]
    [b10_before: PHYSICAL Value PropCarrier]          [b11_before: COMPARABLE Value PropCarrier]        [b12_before: OBSERVED Value PropCarrier]
    [b13_before: PRESENT Value PropCarrier]           [b14_before: MEASURABLE Value PropCarrier]        [b15_before: GUNGAN Value PropCarrier]
    [b16_before: SOURCE Value PropCarrier]            [b17_before: EXECUTED Value PropCarrier]          [b18_before: VALUE Value PropCarrier]
    [b19_before: MAGNITUDE Value PropCarrier]         [b20_before: SCALED Value PropCarrier]            [b21_before: LOAD Value PropCarrier]
    [b22_before: FINITE_ELEPHANT Value PropCarrier]   [b23_before: BULLSHIT Value PropCarrier]          [b24_before: PROPAGANDA Value PropCarrier]
    [b25_before: ACOLYTE Value PropCarrier]           [b26_before: SCIENTIFIC Value PropCarrier]        [b27_before: TRUTH Value PropCarrier]
    [b28_before: WITNESSED Value PropCarrier]         [b29_before: REAL Value PropCarrier]
    [UNIVERSAL Value PropCarrier]         [LOGICAL Value PropCarrier]           [HALTED Value PropCarrier]
    [MEASURED Value PropCarrier b29_before]          [COMPILED Value PropCarrier]          [TrueOutput Value PropCarrier b29_before]
    (_: CarrierProcess Value)
    [TrueOutput Value PropCarrier b29_before]        [COMPILED Value PropCarrier]          [MEASURED Value PropCarrier b29_before]
    [HALTED Value PropCarrier]            [LOGICAL Value PropCarrier]           [b31_after: UNIVERSAL Value PropCarrier]
    [b30_after: LOCAL Value PropCarrier b29_before] [b29_after: REAL Value PropCarrier] [b28_after: WITNESSED Value PropCarrier]
  : TRUTH Value PropCarrier :=
  {
    scientific_process := b28_after.baptism.scientific_process
  }

/--
```python
def unwrap_method_channel(
    before: ReferenceStack,
    after: ReturnStack[Witnessed, Truth],
    carrier: Medium,
) -> Scientific:
    """Recover the simulator's method channel from the truth-band echo."""
```

Implementation note: the receiver converts the returned truth band into the
learning process.  The decoded value is a method channel for later stages.
-/
instance (priority := low) TRUTH_SCIENTIFIC_backward
    (Value: Type i)
    (PropCarrier: CarrierProcess Value)
    [b1_before:  DISTINGUISHABLE Value PropCarrier]   [b2_before:  ADMISSIBLE Value PropCarrier]        [b3_before:  COUNTABLE Value PropCarrier]
    [b4_before:  ENCODED Value PropCarrier]           [b5_before:  RESIDUE Value PropCarrier]           [b6_before:  BINARY Value PropCarrier]
    [b7_before:  REPEATABLE Value PropCarrier]        [b8_before:  NUMERIC Value PropCarrier]           [b9_before:  REPRESENTABLE Value PropCarrier]
    [b10_before: PHYSICAL Value PropCarrier]          [b11_before: COMPARABLE Value PropCarrier]        [b12_before: OBSERVED Value PropCarrier]
    [b13_before: PRESENT Value PropCarrier]           [b14_before: MEASURABLE Value PropCarrier]        [b15_before: GUNGAN Value PropCarrier]
    [b16_before: SOURCE Value PropCarrier]            [b17_before: EXECUTED Value PropCarrier]          [b18_before: VALUE Value PropCarrier]
    [b19_before: MAGNITUDE Value PropCarrier]         [b20_before: SCALED Value PropCarrier]            [b21_before: LOAD Value PropCarrier]
    [b22_before: FINITE_ELEPHANT Value PropCarrier]   [b23_before: BULLSHIT Value PropCarrier]          [b24_before: PROPAGANDA Value PropCarrier]
    [b25_before: ACOLYTE Value PropCarrier]           [b26_before: SCIENTIFIC Value PropCarrier]        [b27_before: TRUTH Value PropCarrier]
    [b28_before: WITNESSED Value PropCarrier]         [b29_before: REAL Value PropCarrier]
    [UNIVERSAL Value PropCarrier]         [LOGICAL Value PropCarrier]           [HALTED Value PropCarrier]
    [MEASURED Value PropCarrier b29_before]          [COMPILED Value PropCarrier]          [TrueOutput Value PropCarrier b29_before]
    (_: CarrierProcess Value)
    [TrueOutput Value PropCarrier b29_before]        [COMPILED Value PropCarrier]          [MEASURED Value PropCarrier b29_before]
    [HALTED Value PropCarrier]            [LOGICAL Value PropCarrier]           [b31_after: UNIVERSAL Value PropCarrier]
    [b30_after: LOCAL Value PropCarrier b29_before] [b29_after: REAL Value PropCarrier] [b28_after: WITNESSED Value PropCarrier]
    [b27_after: TRUTH Value PropCarrier]
  : SCIENTIFIC Value PropCarrier :=
  {
    phd_process := b27_after.scientific_process.learning_process
    invariant := b27_after.scientific_process.learning_process.touch_stove? b27_after.scientific_process.learning_process.invariant
  }

/--
```python
def unwrap_operator_channel(
    before: ReferenceStack,
    after: ReturnStack[Truth, Scientific],
    carrier: Medium,
) -> Acolyte:
    """Recover the receiver operator channel from the method echo."""
```

Implementation note: the receiver takes the returned learning process and
exposes its initiation process as the operator interface for lower bands.
-/
instance (priority := low) SCIENTIFIC_ACOLYTE_backward
    (Value: Type i)
    (PropCarrier: CarrierProcess Value)
    [b1_before:  DISTINGUISHABLE Value PropCarrier]   [b2_before:  ADMISSIBLE Value PropCarrier]        [b3_before:  COUNTABLE Value PropCarrier]
    [b4_before:  ENCODED Value PropCarrier]           [b5_before:  RESIDUE Value PropCarrier]           [b6_before:  BINARY Value PropCarrier]
    [b7_before:  REPEATABLE Value PropCarrier]        [b8_before:  NUMERIC Value PropCarrier]           [b9_before:  REPRESENTABLE Value PropCarrier]
    [b10_before: PHYSICAL Value PropCarrier]          [b11_before: COMPARABLE Value PropCarrier]        [b12_before: OBSERVED Value PropCarrier]
    [b13_before: PRESENT Value PropCarrier]           [b14_before: MEASURABLE Value PropCarrier]        [b15_before: GUNGAN Value PropCarrier]
    [b16_before: SOURCE Value PropCarrier]            [b17_before: EXECUTED Value PropCarrier]          [b18_before: VALUE Value PropCarrier]
    [b19_before: MAGNITUDE Value PropCarrier]         [b20_before: SCALED Value PropCarrier]            [b21_before: LOAD Value PropCarrier]
    [b22_before: FINITE_ELEPHANT Value PropCarrier]   [b23_before: BULLSHIT Value PropCarrier]          [b24_before: PROPAGANDA Value PropCarrier]
    [b25_before: ACOLYTE Value PropCarrier]           [b26_before: SCIENTIFIC Value PropCarrier]        [b27_before: TRUTH Value PropCarrier]
    [b28_before: WITNESSED Value PropCarrier]         [b29_before: REAL Value PropCarrier]
    [UNIVERSAL Value PropCarrier]         [LOGICAL Value PropCarrier]           [HALTED Value PropCarrier]
    [MEASURED Value PropCarrier b29_before]          [COMPILED Value PropCarrier]          [TrueOutput Value PropCarrier b29_before]
    (_: CarrierProcess Value)
    [TrueOutput Value PropCarrier b29_before]        [COMPILED Value PropCarrier]          [MEASURED Value PropCarrier b29_before]
    [HALTED Value PropCarrier]            [LOGICAL Value PropCarrier]           [b31_after: UNIVERSAL Value PropCarrier]
    [b30_after: LOCAL Value PropCarrier b29_before] [b29_after: REAL Value PropCarrier] [b28_after: WITNESSED Value PropCarrier]
    [b27_after: TRUTH Value PropCarrier]  [b26_after: SCIENTIFIC Value PropCarrier]
  : ACOLYTE Value PropCarrier :=
  {
    euclid := b26_after.phd_process.initiation_process
  }

/--
```python
def unwrap_broadcast_channel(
    before: ReferenceStack,
    after: ReturnStack[Scientific, Acolyte],
    carrier: Medium,
) -> Propaganda:
    """Recover the broadcast layer driven by the operator channel."""
```

Implementation note: the receiver treats the returned acolyte ethos as the
broadcast source.  The signal is now a distributable simulator message.
-/
instance (priority := low) ACOLYTE_PROPAGANDA_backward
    (Value: Type i)
    (PropCarrier: CarrierProcess Value)
    [b1_before:  DISTINGUISHABLE Value PropCarrier]   [b2_before:  ADMISSIBLE Value PropCarrier]        [b3_before:  COUNTABLE Value PropCarrier]
    [b4_before:  ENCODED Value PropCarrier]           [b5_before:  RESIDUE Value PropCarrier]           [b6_before:  BINARY Value PropCarrier]
    [b7_before:  REPEATABLE Value PropCarrier]        [b8_before:  NUMERIC Value PropCarrier]           [b9_before:  REPRESENTABLE Value PropCarrier]
    [b10_before: PHYSICAL Value PropCarrier]          [b11_before: COMPARABLE Value PropCarrier]        [b12_before: OBSERVED Value PropCarrier]
    [b13_before: PRESENT Value PropCarrier]           [b14_before: MEASURABLE Value PropCarrier]        [b15_before: GUNGAN Value PropCarrier]
    [b16_before: SOURCE Value PropCarrier]            [b17_before: EXECUTED Value PropCarrier]          [b18_before: VALUE Value PropCarrier]
    [b19_before: MAGNITUDE Value PropCarrier]         [b20_before: SCALED Value PropCarrier]            [b21_before: LOAD Value PropCarrier]
    [b22_before: FINITE_ELEPHANT Value PropCarrier]   [b23_before: BULLSHIT Value PropCarrier]          [b24_before: PROPAGANDA Value PropCarrier]
    [b25_before: ACOLYTE Value PropCarrier]           [b26_before: SCIENTIFIC Value PropCarrier]        [b27_before: TRUTH Value PropCarrier]
    [b28_before: WITNESSED Value PropCarrier]         [b29_before: REAL Value PropCarrier]
    [UNIVERSAL Value PropCarrier]         [LOGICAL Value PropCarrier]           [HALTED Value PropCarrier]
    [MEASURED Value PropCarrier b29_before]          [COMPILED Value PropCarrier]          [TrueOutput Value PropCarrier b29_before]
    (_: CarrierProcess Value)
    [TrueOutput Value PropCarrier b29_before]        [COMPILED Value PropCarrier]          [MEASURED Value PropCarrier b29_before]
    [HALTED Value PropCarrier]            [LOGICAL Value PropCarrier]           [b31_after: UNIVERSAL Value PropCarrier]
    [b30_after: LOCAL Value PropCarrier b29_before] [b29_after: REAL Value PropCarrier] [b28_after: WITNESSED Value PropCarrier]
    [b27_after: TRUTH Value PropCarrier]  [b26_after: SCIENTIFIC Value PropCarrier] [b25_after: ACOLYTE Value PropCarrier]
  : PROPAGANDA Value PropCarrier :=
  {
    insinuation := b25_after.euclid.ethos
  }

/--
```python
def unwrap_noise_model(
    before: ReferenceStack,
    after: ReturnStack[Acolyte, Propaganda],
    carrier: Medium,
) -> Bullshit:
    """Recover the arm-wave noise model from the broadcast echo."""
```

Implementation note: the receiver converts the returned broadcast channel into
the simulator's noise model.  This is the rhetorical clutter band, decoded as a
usable process.
-/
instance (priority := low) PROPAGANDA_BULLSHIT_backward
    (Value: Type i)
    (PropCarrier: CarrierProcess Value)
    [b1_before:  DISTINGUISHABLE Value PropCarrier]   [b2_before:  ADMISSIBLE Value PropCarrier]        [b3_before:  COUNTABLE Value PropCarrier]
    [b4_before:  ENCODED Value PropCarrier]           [b5_before:  RESIDUE Value PropCarrier]           [b6_before:  BINARY Value PropCarrier]
    [b7_before:  REPEATABLE Value PropCarrier]        [b8_before:  NUMERIC Value PropCarrier]           [b9_before:  REPRESENTABLE Value PropCarrier]
    [b10_before: PHYSICAL Value PropCarrier]          [b11_before: COMPARABLE Value PropCarrier]        [b12_before: OBSERVED Value PropCarrier]
    [b13_before: PRESENT Value PropCarrier]           [b14_before: MEASURABLE Value PropCarrier]        [b15_before: GUNGAN Value PropCarrier]
    [b16_before: SOURCE Value PropCarrier]            [b17_before: EXECUTED Value PropCarrier]          [b18_before: VALUE Value PropCarrier]
    [b19_before: MAGNITUDE Value PropCarrier]         [b20_before: SCALED Value PropCarrier]            [b21_before: LOAD Value PropCarrier]
    [b22_before: FINITE_ELEPHANT Value PropCarrier]   [b23_before: BULLSHIT Value PropCarrier]          [b24_before: PROPAGANDA Value PropCarrier]
    [b25_before: ACOLYTE Value PropCarrier]           [b26_before: SCIENTIFIC Value PropCarrier]        [b27_before: TRUTH Value PropCarrier]
    [b28_before: WITNESSED Value PropCarrier]         [b29_before: REAL Value PropCarrier]
    [UNIVERSAL Value PropCarrier]         [LOGICAL Value PropCarrier]           [HALTED Value PropCarrier]
    [MEASURED Value PropCarrier b29_before]          [COMPILED Value PropCarrier]          [TrueOutput Value PropCarrier b29_before]
    (_: CarrierProcess Value)
    [TrueOutput Value PropCarrier b29_before]        [COMPILED Value PropCarrier]          [MEASURED Value PropCarrier b29_before]
    [HALTED Value PropCarrier]            [LOGICAL Value PropCarrier]           [b31_after: UNIVERSAL Value PropCarrier]
    [b30_after: LOCAL Value PropCarrier b29_before] [b29_after: REAL Value PropCarrier] [b28_after: WITNESSED Value PropCarrier]
    [b27_after: TRUTH Value PropCarrier]  [b26_after: SCIENTIFIC Value PropCarrier] [b25_after: ACOLYTE Value PropCarrier]
    [b24_after: PROPAGANDA Value PropCarrier]
  : BULLSHIT Value PropCarrier :=
  {
    arm_wave_process := b24_after.insinuation.pwn_n00bz
  }

/--
```python
def unwrap_fem_channel(
    before: ReferenceStack,
    after: ReturnStack[Propaganda, Bullshit],
    carrier: Medium,
) -> FiniteElephant:
    """Recover the finite-element channel from the noise model."""
```

Implementation note: the receiver extracts the Galerkin process carried inside
the returned arm-wave model.  The echo is now back in structural-simulation
coordinates.
-/
instance (priority := low) BULLSHIT_FINITE_ELEPHANT_backward
    (Value: Type i)
    (PropCarrier: CarrierProcess Value)
    [b1_before:  DISTINGUISHABLE Value PropCarrier]   [b2_before:  ADMISSIBLE Value PropCarrier]        [b3_before:  COUNTABLE Value PropCarrier]
    [b4_before:  ENCODED Value PropCarrier]           [b5_before:  RESIDUE Value PropCarrier]           [b6_before:  BINARY Value PropCarrier]
    [b7_before:  REPEATABLE Value PropCarrier]        [b8_before:  NUMERIC Value PropCarrier]           [b9_before:  REPRESENTABLE Value PropCarrier]
    [b10_before: PHYSICAL Value PropCarrier]          [b11_before: COMPARABLE Value PropCarrier]        [b12_before: OBSERVED Value PropCarrier]
    [b13_before: PRESENT Value PropCarrier]           [b14_before: MEASURABLE Value PropCarrier]        [b15_before: GUNGAN Value PropCarrier]
    [b16_before: SOURCE Value PropCarrier]            [b17_before: EXECUTED Value PropCarrier]          [b18_before: VALUE Value PropCarrier]
    [b19_before: MAGNITUDE Value PropCarrier]         [b20_before: SCALED Value PropCarrier]            [b21_before: LOAD Value PropCarrier]
    [b22_before: FINITE_ELEPHANT Value PropCarrier]   [b23_before: BULLSHIT Value PropCarrier]          [b24_before: PROPAGANDA Value PropCarrier]
    [b25_before: ACOLYTE Value PropCarrier]           [b26_before: SCIENTIFIC Value PropCarrier]        [b27_before: TRUTH Value PropCarrier]
    [b28_before: WITNESSED Value PropCarrier]         [b29_before: REAL Value PropCarrier]
    [UNIVERSAL Value PropCarrier]         [LOGICAL Value PropCarrier]           [HALTED Value PropCarrier]
    [MEASURED Value PropCarrier b29_before]          [COMPILED Value PropCarrier]          [TrueOutput Value PropCarrier b29_before]
    (_: CarrierProcess Value)
    [TrueOutput Value PropCarrier b29_before]        [COMPILED Value PropCarrier]          [MEASURED Value PropCarrier b29_before]
    [HALTED Value PropCarrier]            [LOGICAL Value PropCarrier]           [b31_after: UNIVERSAL Value PropCarrier]
    [b30_after: LOCAL Value PropCarrier b29_before] [b29_after: REAL Value PropCarrier] [b28_after: WITNESSED Value PropCarrier]
    [b27_after: TRUTH Value PropCarrier]  [b26_after: SCIENTIFIC Value PropCarrier] [b25_after: ACOLYTE Value PropCarrier]
    [b24_after: PROPAGANDA Value PropCarrier] [b23_after: BULLSHIT Value PropCarrier]
  : FINITE_ELEPHANT Value PropCarrier :=
  {
    galerkin_process := b23_after.arm_wave_process.galerkin_process
  }

/--
```python
def unwrap_load_channel(
    before: ReferenceStack,
    after: ReturnStack[Bullshit, FiniteElephant],
    carrier: Medium,
) -> Load:
    """Recover the load channel from the finite-element return."""
```

Implementation note: the receiver reads the returned ANSYS process as the basic
operation.  The echo has become a load-bearing simulator channel.
-/
instance (priority := low) FINITE_ELEPHANT_LOAD_backward
    (Value: Type i)
    (PropCarrier: CarrierProcess Value)
    [b1_before:  DISTINGUISHABLE Value PropCarrier]   [b2_before:  ADMISSIBLE Value PropCarrier]        [b3_before:  COUNTABLE Value PropCarrier]
    [b4_before:  ENCODED Value PropCarrier]           [b5_before:  RESIDUE Value PropCarrier]           [b6_before:  BINARY Value PropCarrier]
    [b7_before:  REPEATABLE Value PropCarrier]        [b8_before:  NUMERIC Value PropCarrier]           [b9_before:  REPRESENTABLE Value PropCarrier]
    [b10_before: PHYSICAL Value PropCarrier]          [b11_before: COMPARABLE Value PropCarrier]        [b12_before: OBSERVED Value PropCarrier]
    [b13_before: PRESENT Value PropCarrier]           [b14_before: MEASURABLE Value PropCarrier]        [b15_before: GUNGAN Value PropCarrier]
    [b16_before: SOURCE Value PropCarrier]            [b17_before: EXECUTED Value PropCarrier]          [b18_before: VALUE Value PropCarrier]
    [b19_before: MAGNITUDE Value PropCarrier]         [b20_before: SCALED Value PropCarrier]            [b21_before: LOAD Value PropCarrier]
    [b22_before: FINITE_ELEPHANT Value PropCarrier]   [b23_before: BULLSHIT Value PropCarrier]          [b24_before: PROPAGANDA Value PropCarrier]
    [b25_before: ACOLYTE Value PropCarrier]           [b26_before: SCIENTIFIC Value PropCarrier]        [b27_before: TRUTH Value PropCarrier]
    [b28_before: WITNESSED Value PropCarrier]         [b29_before: REAL Value PropCarrier]
    [UNIVERSAL Value PropCarrier]         [LOGICAL Value PropCarrier]           [HALTED Value PropCarrier]
    [MEASURED Value PropCarrier b29_before]          [COMPILED Value PropCarrier]          [TrueOutput Value PropCarrier b29_before]
    (_: CarrierProcess Value)
    [TrueOutput Value PropCarrier b29_before]        [COMPILED Value PropCarrier]          [MEASURED Value PropCarrier b29_before]
    [HALTED Value PropCarrier]            [LOGICAL Value PropCarrier]           [b31_after: UNIVERSAL Value PropCarrier]
    [b30_after: LOCAL Value PropCarrier b29_before] [b29_after: REAL Value PropCarrier] [b28_after: WITNESSED Value PropCarrier]
    [b27_after: TRUTH Value PropCarrier]  [b26_after: SCIENTIFIC Value PropCarrier] [b25_after: ACOLYTE Value PropCarrier]
    [b24_after: PROPAGANDA Value PropCarrier] [b23_after: BULLSHIT Value PropCarrier] [b22_after: FINITE_ELEPHANT Value PropCarrier]
  : LOAD Value PropCarrier :=
  {
    basic_operation := b22_after.galerkin_process.ANSYS_process
  }

/--
```python
def unwrap_scale_channel(
    before: ReferenceStack,
    after: ReturnStack[FiniteElephant, Load],
    carrier: Medium,
) -> Scaled:
    """Recover scale from the load channel."""
```

Implementation note: the receiver follows the returned `GOSUB` operation into
the multiplying process.  Load becomes scale without rerunning the transmitter.
-/
instance (priority := low) LOAD_SCALED_backward
    (Value: Type i)
    (PropCarrier: CarrierProcess Value)
    [b1_before:  DISTINGUISHABLE Value PropCarrier]   [b2_before:  ADMISSIBLE Value PropCarrier]        [b3_before:  COUNTABLE Value PropCarrier]
    [b4_before:  ENCODED Value PropCarrier]           [b5_before:  RESIDUE Value PropCarrier]           [b6_before:  BINARY Value PropCarrier]
    [b7_before:  REPEATABLE Value PropCarrier]        [b8_before:  NUMERIC Value PropCarrier]           [b9_before:  REPRESENTABLE Value PropCarrier]
    [b10_before: PHYSICAL Value PropCarrier]          [b11_before: COMPARABLE Value PropCarrier]        [b12_before: OBSERVED Value PropCarrier]
    [b13_before: PRESENT Value PropCarrier]           [b14_before: MEASURABLE Value PropCarrier]        [b15_before: GUNGAN Value PropCarrier]
    [b16_before: SOURCE Value PropCarrier]            [b17_before: EXECUTED Value PropCarrier]          [b18_before: VALUE Value PropCarrier]
    [b19_before: MAGNITUDE Value PropCarrier]         [b20_before: SCALED Value PropCarrier]            [b21_before: LOAD Value PropCarrier]
    [b22_before: FINITE_ELEPHANT Value PropCarrier]   [b23_before: BULLSHIT Value PropCarrier]          [b24_before: PROPAGANDA Value PropCarrier]
    [b25_before: ACOLYTE Value PropCarrier]           [b26_before: SCIENTIFIC Value PropCarrier]        [b27_before: TRUTH Value PropCarrier]
    [b28_before: WITNESSED Value PropCarrier]         [b29_before: REAL Value PropCarrier]
    [UNIVERSAL Value PropCarrier]         [LOGICAL Value PropCarrier]           [HALTED Value PropCarrier]
    [MEASURED Value PropCarrier b29_before]          [COMPILED Value PropCarrier]          [TrueOutput Value PropCarrier b29_before]
    (_: CarrierProcess Value)
    [TrueOutput Value PropCarrier b29_before]        [COMPILED Value PropCarrier]          [MEASURED Value PropCarrier b29_before]
    [HALTED Value PropCarrier]            [LOGICAL Value PropCarrier]           [b31_after: UNIVERSAL Value PropCarrier]
    [b30_after: LOCAL Value PropCarrier b29_before] [b29_after: REAL Value PropCarrier] [b28_after: WITNESSED Value PropCarrier]
    [b27_after: TRUTH Value PropCarrier]  [b26_after: SCIENTIFIC Value PropCarrier] [b25_after: ACOLYTE Value PropCarrier]
    [b24_after: PROPAGANDA Value PropCarrier] [b23_after: BULLSHIT Value PropCarrier] [b22_after: FINITE_ELEPHANT Value PropCarrier]
    [b21_after: LOAD Value PropCarrier]
  : SCALED Value PropCarrier :=
  {
    multiplying_process := b21_after.basic_operation.GOSUB
  }

/--
```python
def unwrap_magnitude_channel(
    before: ReferenceStack,
    after: ReturnStack[Load, Scaled],
    carrier: Medium,
) -> Magnitude:
    """Recover magnitude from the scaled return."""
```

Implementation note: the receiver reads the returned multiplying process as an
adding process.  The echo is converted from scale into a magnitude band.
-/
instance (priority := low) SCALED_MAGNITUDE_backward
    (Value: Type i)
    (PropCarrier: CarrierProcess Value)
    [b1_before:  DISTINGUISHABLE Value PropCarrier]   [b2_before:  ADMISSIBLE Value PropCarrier]        [b3_before:  COUNTABLE Value PropCarrier]
    [b4_before:  ENCODED Value PropCarrier]           [b5_before:  RESIDUE Value PropCarrier]           [b6_before:  BINARY Value PropCarrier]
    [b7_before:  REPEATABLE Value PropCarrier]        [b8_before:  NUMERIC Value PropCarrier]           [b9_before:  REPRESENTABLE Value PropCarrier]
    [b10_before: PHYSICAL Value PropCarrier]          [b11_before: COMPARABLE Value PropCarrier]        [b12_before: OBSERVED Value PropCarrier]
    [b13_before: PRESENT Value PropCarrier]           [b14_before: MEASURABLE Value PropCarrier]        [b15_before: GUNGAN Value PropCarrier]
    [b16_before: SOURCE Value PropCarrier]            [b17_before: EXECUTED Value PropCarrier]          [b18_before: VALUE Value PropCarrier]
    [b19_before: MAGNITUDE Value PropCarrier]         [b20_before: SCALED Value PropCarrier]            [b21_before: LOAD Value PropCarrier]
    [b22_before: FINITE_ELEPHANT Value PropCarrier]   [b23_before: BULLSHIT Value PropCarrier]          [b24_before: PROPAGANDA Value PropCarrier]
    [b25_before: ACOLYTE Value PropCarrier]           [b26_before: SCIENTIFIC Value PropCarrier]        [b27_before: TRUTH Value PropCarrier]
    [b28_before: WITNESSED Value PropCarrier]         [b29_before: REAL Value PropCarrier]
    [UNIVERSAL Value PropCarrier]         [LOGICAL Value PropCarrier]           [HALTED Value PropCarrier]
    [MEASURED Value PropCarrier b29_before]          [COMPILED Value PropCarrier]          [TrueOutput Value PropCarrier b29_before]
    (_: CarrierProcess Value)
    [TrueOutput Value PropCarrier b29_before]        [COMPILED Value PropCarrier]          [MEASURED Value PropCarrier b29_before]
    [HALTED Value PropCarrier]            [LOGICAL Value PropCarrier]           [b31_after: UNIVERSAL Value PropCarrier]
    [b30_after: LOCAL Value PropCarrier b29_before] [b29_after: REAL Value PropCarrier] [b28_after: WITNESSED Value PropCarrier]
    [b27_after: TRUTH Value PropCarrier]  [b26_after: SCIENTIFIC Value PropCarrier] [b25_after: ACOLYTE Value PropCarrier]
    [b24_after: PROPAGANDA Value PropCarrier] [b23_after: BULLSHIT Value PropCarrier] [b22_after: FINITE_ELEPHANT Value PropCarrier]
    [b21_after: LOAD Value PropCarrier] [b20_after: SCALED Value PropCarrier]
  : MAGNITUDE Value PropCarrier :=
  {
    adding_process := b20_after.multiplying_process.adding_process
  }

/--
```python
def unwrap_value_channel(
    before: ReferenceStack,
    after: ReturnStack[Scaled, Magnitude],
    carrier: Medium,
) -> ValueChannel:
    """Recover value from the magnitude return."""
```

Implementation note: the receiver extracts the mathematical process underneath
the returned adding process.  This stage strips the size wrapper from the echo.
-/
instance (priority := low) MAGNITUDE_VALUE_backward
    (Value: Type i)
    (PropCarrier: CarrierProcess Value)
    [b1_before:  DISTINGUISHABLE Value PropCarrier]   [b2_before:  ADMISSIBLE Value PropCarrier]        [b3_before:  COUNTABLE Value PropCarrier]
    [b4_before:  ENCODED Value PropCarrier]           [b5_before:  RESIDUE Value PropCarrier]           [b6_before:  BINARY Value PropCarrier]
    [b7_before:  REPEATABLE Value PropCarrier]        [b8_before:  NUMERIC Value PropCarrier]           [b9_before:  REPRESENTABLE Value PropCarrier]
    [b10_before: PHYSICAL Value PropCarrier]          [b11_before: COMPARABLE Value PropCarrier]        [b12_before: OBSERVED Value PropCarrier]
    [b13_before: PRESENT Value PropCarrier]           [b14_before: MEASURABLE Value PropCarrier]        [b15_before: GUNGAN Value PropCarrier]
    [b16_before: SOURCE Value PropCarrier]            [b17_before: EXECUTED Value PropCarrier]          [b18_before: VALUE Value PropCarrier]
    [b19_before: MAGNITUDE Value PropCarrier]         [b20_before: SCALED Value PropCarrier]            [b21_before: LOAD Value PropCarrier]
    [b22_before: FINITE_ELEPHANT Value PropCarrier]   [b23_before: BULLSHIT Value PropCarrier]          [b24_before: PROPAGANDA Value PropCarrier]
    [b25_before: ACOLYTE Value PropCarrier]           [b26_before: SCIENTIFIC Value PropCarrier]        [b27_before: TRUTH Value PropCarrier]
    [b28_before: WITNESSED Value PropCarrier]         [b29_before: REAL Value PropCarrier]
    [UNIVERSAL Value PropCarrier]         [LOGICAL Value PropCarrier]           [HALTED Value PropCarrier]
    [MEASURED Value PropCarrier b29_before]          [COMPILED Value PropCarrier]          [TrueOutput Value PropCarrier b29_before]
    (_: CarrierProcess Value)
    [TrueOutput Value PropCarrier b29_before]        [COMPILED Value PropCarrier]          [MEASURED Value PropCarrier b29_before]
    [HALTED Value PropCarrier]            [LOGICAL Value PropCarrier]           [b31_after: UNIVERSAL Value PropCarrier]
    [b30_after: LOCAL Value PropCarrier b29_before] [b29_after: REAL Value PropCarrier] [b28_after: WITNESSED Value PropCarrier]
    [b27_after: TRUTH Value PropCarrier]  [b26_after: SCIENTIFIC Value PropCarrier] [b25_after: ACOLYTE Value PropCarrier]
    [b24_after: PROPAGANDA Value PropCarrier] [b23_after: BULLSHIT Value PropCarrier] [b22_after: FINITE_ELEPHANT Value PropCarrier]
    [b21_after: LOAD Value PropCarrier] [b20_after: SCALED Value PropCarrier] [b19_after: MAGNITUDE Value PropCarrier]
  : VALUE Value PropCarrier :=
  {
    mathematical_process := b19_after.adding_process.mathematical_process
    monad := b19_after.adding_process.mathematical_process.calculate? (.satire b1_before.fact)
  }

/--
```python
def unwrap_execution_channel(
    before: ReferenceStack,
    after: ReturnStack[Magnitude, ValueChannel],
    carrier: Medium,
) -> Executed:
    """Recover execution from the returned value channel."""
```

Implementation note: the receiver follows the mathematical process back to its
compiled process.  Value is demodulated into execution state.
-/
instance (priority := low) VALUE_EXECUTED_backward
    (Value: Type i)
    (PropCarrier: CarrierProcess Value)
    [b1_before:  DISTINGUISHABLE Value PropCarrier]   [b2_before:  ADMISSIBLE Value PropCarrier]        [b3_before:  COUNTABLE Value PropCarrier]
    [b4_before:  ENCODED Value PropCarrier]           [b5_before:  RESIDUE Value PropCarrier]           [b6_before:  BINARY Value PropCarrier]
    [b7_before:  REPEATABLE Value PropCarrier]        [b8_before:  NUMERIC Value PropCarrier]           [b9_before:  REPRESENTABLE Value PropCarrier]
    [b10_before: PHYSICAL Value PropCarrier]          [b11_before: COMPARABLE Value PropCarrier]        [b12_before: OBSERVED Value PropCarrier]
    [b13_before: PRESENT Value PropCarrier]           [b14_before: MEASURABLE Value PropCarrier]        [b15_before: GUNGAN Value PropCarrier]
    [b16_before: SOURCE Value PropCarrier]            [b17_before: EXECUTED Value PropCarrier]          [b18_before: VALUE Value PropCarrier]
    [b19_before: MAGNITUDE Value PropCarrier]         [b20_before: SCALED Value PropCarrier]            [b21_before: LOAD Value PropCarrier]
    [b22_before: FINITE_ELEPHANT Value PropCarrier]   [b23_before: BULLSHIT Value PropCarrier]          [b24_before: PROPAGANDA Value PropCarrier]
    [b25_before: ACOLYTE Value PropCarrier]           [b26_before: SCIENTIFIC Value PropCarrier]        [b27_before: TRUTH Value PropCarrier]
    [b28_before: WITNESSED Value PropCarrier]         [b29_before: REAL Value PropCarrier]
    [UNIVERSAL Value PropCarrier]         [LOGICAL Value PropCarrier]           [HALTED Value PropCarrier]
    [MEASURED Value PropCarrier b29_before]          [COMPILED Value PropCarrier]          [TrueOutput Value PropCarrier b29_before]
    (_: CarrierProcess Value)
    [TrueOutput Value PropCarrier b29_before]        [COMPILED Value PropCarrier]          [MEASURED Value PropCarrier b29_before]
    [HALTED Value PropCarrier]            [LOGICAL Value PropCarrier]           [b31_after: UNIVERSAL Value PropCarrier]
    [b30_after: LOCAL Value PropCarrier b29_before] [b29_after: REAL Value PropCarrier] [b28_after: WITNESSED Value PropCarrier]
    [b27_after: TRUTH Value PropCarrier]  [b26_after: SCIENTIFIC Value PropCarrier] [b25_after: ACOLYTE Value PropCarrier]
    [b24_after: PROPAGANDA Value PropCarrier] [b23_after: BULLSHIT Value PropCarrier] [b22_after: FINITE_ELEPHANT Value PropCarrier]
    [b21_after: LOAD Value PropCarrier] [b20_after: SCALED Value PropCarrier] [b19_after: MAGNITUDE Value PropCarrier]
    [b18_after: VALUE Value PropCarrier]
  : EXECUTED Value PropCarrier :=
  {
    compiled_process := b18_after.mathematical_process.compiled_process
  }

/--
```python
def unwrap_source_channel(
    before: ReferenceStack,
    after: ReturnStack[ValueChannel, Executed],
    carrier: Medium,
) -> Source:
    """Recover source from the executed return."""
```

Implementation note: the receiver uses the returned compiled process to recover
the digital source process.  This is a source-channel readback, not a rebuild.
-/
instance (priority := low) EXECUTED_SOURCE_backward
    (Value: Type i)
    (PropCarrier: CarrierProcess Value)
    [b1_before:  DISTINGUISHABLE Value PropCarrier]   [b2_before:  ADMISSIBLE Value PropCarrier]        [b3_before:  COUNTABLE Value PropCarrier]
    [b4_before:  ENCODED Value PropCarrier]           [b5_before:  RESIDUE Value PropCarrier]           [b6_before:  BINARY Value PropCarrier]
    [b7_before:  REPEATABLE Value PropCarrier]        [b8_before:  NUMERIC Value PropCarrier]           [b9_before:  REPRESENTABLE Value PropCarrier]
    [b10_before: PHYSICAL Value PropCarrier]          [b11_before: COMPARABLE Value PropCarrier]        [b12_before: OBSERVED Value PropCarrier]
    [b13_before: PRESENT Value PropCarrier]           [b14_before: MEASURABLE Value PropCarrier]        [b15_before: GUNGAN Value PropCarrier]
    [b16_before: SOURCE Value PropCarrier]            [b17_before: EXECUTED Value PropCarrier]          [b18_before: VALUE Value PropCarrier]
    [b19_before: MAGNITUDE Value PropCarrier]         [b20_before: SCALED Value PropCarrier]            [b21_before: LOAD Value PropCarrier]
    [b22_before: FINITE_ELEPHANT Value PropCarrier]   [b23_before: BULLSHIT Value PropCarrier]          [b24_before: PROPAGANDA Value PropCarrier]
    [b25_before: ACOLYTE Value PropCarrier]           [b26_before: SCIENTIFIC Value PropCarrier]        [b27_before: TRUTH Value PropCarrier]
    [b28_before: WITNESSED Value PropCarrier]         [b29_before: REAL Value PropCarrier]
    [UNIVERSAL Value PropCarrier]         [LOGICAL Value PropCarrier]           [HALTED Value PropCarrier]
    [MEASURED Value PropCarrier b29_before]          [COMPILED Value PropCarrier]          [TrueOutput Value PropCarrier b29_before]
    (_: CarrierProcess Value)
    [TrueOutput Value PropCarrier b29_before]        [COMPILED Value PropCarrier]          [MEASURED Value PropCarrier b29_before]
    [HALTED Value PropCarrier]            [LOGICAL Value PropCarrier]           [b31_after: UNIVERSAL Value PropCarrier]
    [b30_after: LOCAL Value PropCarrier b29_before] [b29_after: REAL Value PropCarrier] [b28_after: WITNESSED Value PropCarrier]
    [b27_after: TRUTH Value PropCarrier]  [b26_after: SCIENTIFIC Value PropCarrier] [b25_after: ACOLYTE Value PropCarrier]
    [b24_after: PROPAGANDA Value PropCarrier] [b23_after: BULLSHIT Value PropCarrier] [b22_after: FINITE_ELEPHANT Value PropCarrier]
    [b21_after: LOAD Value PropCarrier] [b20_after: SCALED Value PropCarrier] [b19_after: MAGNITUDE Value PropCarrier]
    [b18_after: VALUE Value PropCarrier] [b17_after: EXECUTED Value PropCarrier]
  : SOURCE Value PropCarrier :=
  {
    cd_process := b17_after.compiled_process.digital_process
    one := b17_after.compiled_process.digital_process.tick b17_after.compiled_process.digital_process.zero
  }

/--
```python
def unwrap_translation_channel(
    before: ReferenceStack,
    after: ReturnStack[Executed, Source],
    carrier: Medium,
) -> Gungan:
    """Recover the translation channel from source."""
```

Implementation note: the receiver reads the returned source path as the meesa
process.  The simulator is now back at the translation layer.
-/
instance (priority := low) SOURCE_GUNGAN_backward
    (Value: Type i)
    (PropCarrier: CarrierProcess Value)
    [b1_before:  DISTINGUISHABLE Value PropCarrier]   [b2_before:  ADMISSIBLE Value PropCarrier]        [b3_before:  COUNTABLE Value PropCarrier]
    [b4_before:  ENCODED Value PropCarrier]           [b5_before:  RESIDUE Value PropCarrier]           [b6_before:  BINARY Value PropCarrier]
    [b7_before:  REPEATABLE Value PropCarrier]        [b8_before:  NUMERIC Value PropCarrier]           [b9_before:  REPRESENTABLE Value PropCarrier]
    [b10_before: PHYSICAL Value PropCarrier]          [b11_before: COMPARABLE Value PropCarrier]        [b12_before: OBSERVED Value PropCarrier]
    [b13_before: PRESENT Value PropCarrier]           [b14_before: MEASURABLE Value PropCarrier]        [b15_before: GUNGAN Value PropCarrier]
    [b16_before: SOURCE Value PropCarrier]            [b17_before: EXECUTED Value PropCarrier]          [b18_before: VALUE Value PropCarrier]
    [b19_before: MAGNITUDE Value PropCarrier]         [b20_before: SCALED Value PropCarrier]            [b21_before: LOAD Value PropCarrier]
    [b22_before: FINITE_ELEPHANT Value PropCarrier]   [b23_before: BULLSHIT Value PropCarrier]          [b24_before: PROPAGANDA Value PropCarrier]
    [b25_before: ACOLYTE Value PropCarrier]           [b26_before: SCIENTIFIC Value PropCarrier]        [b27_before: TRUTH Value PropCarrier]
    [b28_before: WITNESSED Value PropCarrier]         [b29_before: REAL Value PropCarrier]
    [UNIVERSAL Value PropCarrier]         [LOGICAL Value PropCarrier]           [HALTED Value PropCarrier]
    [MEASURED Value PropCarrier b29_before]          [COMPILED Value PropCarrier]          [TrueOutput Value PropCarrier b29_before]
    (_: CarrierProcess Value)
    [TrueOutput Value PropCarrier b29_before]        [COMPILED Value PropCarrier]          [MEASURED Value PropCarrier b29_before]
    [HALTED Value PropCarrier]            [LOGICAL Value PropCarrier]           [b31_after: UNIVERSAL Value PropCarrier]
    [b30_after: LOCAL Value PropCarrier b29_before] [b29_after: REAL Value PropCarrier] [b28_after: WITNESSED Value PropCarrier]
    [b27_after: TRUTH Value PropCarrier]  [b26_after: SCIENTIFIC Value PropCarrier] [b25_after: ACOLYTE Value PropCarrier]
    [b24_after: PROPAGANDA Value PropCarrier] [b23_after: BULLSHIT Value PropCarrier] [b22_after: FINITE_ELEPHANT Value PropCarrier]
    [b21_after: LOAD Value PropCarrier] [b20_after: SCALED Value PropCarrier] [b19_after: MAGNITUDE Value PropCarrier]
    [b18_after: VALUE Value PropCarrier] [b17_after: EXECUTED Value PropCarrier] [b16_after: SOURCE Value PropCarrier]
  : GUNGAN Value PropCarrier :=
  {
    meesa_process := b16_after.cd_process.meesa_process
  }

/--
```python
def unwrap_gauge_channel(
    before: ReferenceStack,
    after: ReturnStack[Source, Gungan],
    carrier: Medium,
) -> Measurable:
    """Recover the gauge channel from the translation return."""
```

Implementation note: the receiver extracts the gauge process from the returned
translation process.  The echo is now readable as a measurement gate.
-/
instance (priority := low) GUNGAN_MEASURABLE_backward
    (Value: Type i)
    (PropCarrier: CarrierProcess Value)
    [b1_before:  DISTINGUISHABLE Value PropCarrier]   [b2_before:  ADMISSIBLE Value PropCarrier]        [b3_before:  COUNTABLE Value PropCarrier]
    [b4_before:  ENCODED Value PropCarrier]           [b5_before:  RESIDUE Value PropCarrier]           [b6_before:  BINARY Value PropCarrier]
    [b7_before:  REPEATABLE Value PropCarrier]        [b8_before:  NUMERIC Value PropCarrier]           [b9_before:  REPRESENTABLE Value PropCarrier]
    [b10_before: PHYSICAL Value PropCarrier]          [b11_before: COMPARABLE Value PropCarrier]        [b12_before: OBSERVED Value PropCarrier]
    [b13_before: PRESENT Value PropCarrier]           [b14_before: MEASURABLE Value PropCarrier]        [b15_before: GUNGAN Value PropCarrier]
    [b16_before: SOURCE Value PropCarrier]            [b17_before: EXECUTED Value PropCarrier]          [b18_before: VALUE Value PropCarrier]
    [b19_before: MAGNITUDE Value PropCarrier]         [b20_before: SCALED Value PropCarrier]            [b21_before: LOAD Value PropCarrier]
    [b22_before: FINITE_ELEPHANT Value PropCarrier]   [b23_before: BULLSHIT Value PropCarrier]          [b24_before: PROPAGANDA Value PropCarrier]
    [b25_before: ACOLYTE Value PropCarrier]           [b26_before: SCIENTIFIC Value PropCarrier]        [b27_before: TRUTH Value PropCarrier]
    [b28_before: WITNESSED Value PropCarrier]         [b29_before: REAL Value PropCarrier]
    [UNIVERSAL Value PropCarrier]         [LOGICAL Value PropCarrier]           [HALTED Value PropCarrier]
    [MEASURED Value PropCarrier b29_before]          [COMPILED Value PropCarrier]          [TrueOutput Value PropCarrier b29_before]
    (_: CarrierProcess Value)
    [TrueOutput Value PropCarrier b29_before]        [COMPILED Value PropCarrier]          [MEASURED Value PropCarrier b29_before]
    [HALTED Value PropCarrier]            [LOGICAL Value PropCarrier]           [b31_after: UNIVERSAL Value PropCarrier]
    [b30_after: LOCAL Value PropCarrier b29_before] [b29_after: REAL Value PropCarrier] [b28_after: WITNESSED Value PropCarrier]
    [b27_after: TRUTH Value PropCarrier]  [b26_after: SCIENTIFIC Value PropCarrier] [b25_after: ACOLYTE Value PropCarrier]
    [b24_after: PROPAGANDA Value PropCarrier] [b23_after: BULLSHIT Value PropCarrier] [b22_after: FINITE_ELEPHANT Value PropCarrier]
    [b21_after: LOAD Value PropCarrier] [b20_after: SCALED Value PropCarrier] [b19_after: MAGNITUDE Value PropCarrier]
    [b18_after: VALUE Value PropCarrier] [b17_after: EXECUTED Value PropCarrier] [b16_after: SOURCE Value PropCarrier]
    [b15_after: GUNGAN Value PropCarrier]
  : MEASURABLE Value PropCarrier :=
  {
    gauge_process := b15_after.meesa_process.gauge_process
  }

/--
```python
def unwrap_present_channel(
    before: ReferenceStack,
    after: ReturnStack[Gungan, Measurable],
    carrier: Medium,
) -> Present:
    """Recover the present-tense sensing channel from the gauge return."""
```

Implementation note: the receiver follows the returned sensing process into the
present channel.  The echo is now current in the simulator frame.
-/
instance (priority := low) MEASURABLE_PRESENT_backward
    (Value: Type i)
    (PropCarrier: CarrierProcess Value)
    [b1_before:  DISTINGUISHABLE Value PropCarrier]   [b2_before:  ADMISSIBLE Value PropCarrier]        [b3_before:  COUNTABLE Value PropCarrier]
    [b4_before:  ENCODED Value PropCarrier]           [b5_before:  RESIDUE Value PropCarrier]           [b6_before:  BINARY Value PropCarrier]
    [b7_before:  REPEATABLE Value PropCarrier]        [b8_before:  NUMERIC Value PropCarrier]           [b9_before:  REPRESENTABLE Value PropCarrier]
    [b10_before: PHYSICAL Value PropCarrier]          [b11_before: COMPARABLE Value PropCarrier]        [b12_before: OBSERVED Value PropCarrier]
    [b13_before: PRESENT Value PropCarrier]           [b14_before: MEASURABLE Value PropCarrier]        [b15_before: GUNGAN Value PropCarrier]
    [b16_before: SOURCE Value PropCarrier]            [b17_before: EXECUTED Value PropCarrier]          [b18_before: VALUE Value PropCarrier]
    [b19_before: MAGNITUDE Value PropCarrier]         [b20_before: SCALED Value PropCarrier]            [b21_before: LOAD Value PropCarrier]
    [b22_before: FINITE_ELEPHANT Value PropCarrier]   [b23_before: BULLSHIT Value PropCarrier]          [b24_before: PROPAGANDA Value PropCarrier]
    [b25_before: ACOLYTE Value PropCarrier]           [b26_before: SCIENTIFIC Value PropCarrier]        [b27_before: TRUTH Value PropCarrier]
    [b28_before: WITNESSED Value PropCarrier]         [b29_before: REAL Value PropCarrier]
    [UNIVERSAL Value PropCarrier]         [LOGICAL Value PropCarrier]           [HALTED Value PropCarrier]
    [MEASURED Value PropCarrier b29_before]          [COMPILED Value PropCarrier]          [TrueOutput Value PropCarrier b29_before]
    (_: CarrierProcess Value)
    [TrueOutput Value PropCarrier b29_before]        [COMPILED Value PropCarrier]          [MEASURED Value PropCarrier b29_before]
    [HALTED Value PropCarrier]            [LOGICAL Value PropCarrier]           [b31_after: UNIVERSAL Value PropCarrier]
    [b30_after: LOCAL Value PropCarrier b29_before] [b29_after: REAL Value PropCarrier] [b28_after: WITNESSED Value PropCarrier]
    [b27_after: TRUTH Value PropCarrier]  [b26_after: SCIENTIFIC Value PropCarrier] [b25_after: ACOLYTE Value PropCarrier]
    [b24_after: PROPAGANDA Value PropCarrier] [b23_after: BULLSHIT Value PropCarrier] [b22_after: FINITE_ELEPHANT Value PropCarrier]
    [b21_after: LOAD Value PropCarrier] [b20_after: SCALED Value PropCarrier] [b19_after: MAGNITUDE Value PropCarrier]
    [b18_after: VALUE Value PropCarrier] [b17_after: EXECUTED Value PropCarrier] [b16_after: SOURCE Value PropCarrier]
    [b15_after: GUNGAN Value PropCarrier] [b14_after: MEASURABLE Value PropCarrier]
  : PRESENT Value PropCarrier :=
  {
    santa_claus := b14_after.gauge_process.sensing_process
    quantum := Type 1
  }

/--
```python
def unwrap_observed_channel(
    before: ReferenceStack,
    after: ReturnStack[Measurable, Present],
    carrier: Medium,
) -> Observed:
    """Recover the observation channel from present-time sensing."""
```

Implementation note: the receiver takes the returned static fraction as the
slip process and pins the observed value to its threshold.
-/
instance (priority := low) PRESENT_OBSERVED_backward
    (Value: Type i)
    (PropCarrier: CarrierProcess Value)
    [b1_before:  DISTINGUISHABLE Value PropCarrier]   [b2_before:  ADMISSIBLE Value PropCarrier]        [b3_before:  COUNTABLE Value PropCarrier]
    [b4_before:  ENCODED Value PropCarrier]           [b5_before:  RESIDUE Value PropCarrier]           [b6_before:  BINARY Value PropCarrier]
    [b7_before:  REPEATABLE Value PropCarrier]        [b8_before:  NUMERIC Value PropCarrier]           [b9_before:  REPRESENTABLE Value PropCarrier]
    [b10_before: PHYSICAL Value PropCarrier]          [b11_before: COMPARABLE Value PropCarrier]        [b12_before: OBSERVED Value PropCarrier]
    [b13_before: PRESENT Value PropCarrier]           [b14_before: MEASURABLE Value PropCarrier]        [b15_before: GUNGAN Value PropCarrier]
    [b16_before: SOURCE Value PropCarrier]            [b17_before: EXECUTED Value PropCarrier]          [b18_before: VALUE Value PropCarrier]
    [b19_before: MAGNITUDE Value PropCarrier]         [b20_before: SCALED Value PropCarrier]            [b21_before: LOAD Value PropCarrier]
    [b22_before: FINITE_ELEPHANT Value PropCarrier]   [b23_before: BULLSHIT Value PropCarrier]          [b24_before: PROPAGANDA Value PropCarrier]
    [b25_before: ACOLYTE Value PropCarrier]           [b26_before: SCIENTIFIC Value PropCarrier]        [b27_before: TRUTH Value PropCarrier]
    [b28_before: WITNESSED Value PropCarrier]         [b29_before: REAL Value PropCarrier]
    [UNIVERSAL Value PropCarrier]         [LOGICAL Value PropCarrier]           [HALTED Value PropCarrier]
    [MEASURED Value PropCarrier b29_before]          [COMPILED Value PropCarrier]          [TrueOutput Value PropCarrier b29_before]
    (_: CarrierProcess Value)
    [TrueOutput Value PropCarrier b29_before]        [COMPILED Value PropCarrier]          [MEASURED Value PropCarrier b29_before]
    [HALTED Value PropCarrier]            [LOGICAL Value PropCarrier]           [b31_after: UNIVERSAL Value PropCarrier]
    [b30_after: LOCAL Value PropCarrier b29_before] [b29_after: REAL Value PropCarrier] [b28_after: WITNESSED Value PropCarrier]
    [b27_after: TRUTH Value PropCarrier]  [b26_after: SCIENTIFIC Value PropCarrier] [b25_after: ACOLYTE Value PropCarrier]
    [b24_after: PROPAGANDA Value PropCarrier] [b23_after: BULLSHIT Value PropCarrier] [b22_after: FINITE_ELEPHANT Value PropCarrier]
    [b21_after: LOAD Value PropCarrier] [b20_after: SCALED Value PropCarrier] [b19_after: MAGNITUDE Value PropCarrier]
    [b18_after: VALUE Value PropCarrier] [b17_after: EXECUTED Value PropCarrier] [b16_after: SOURCE Value PropCarrier]
    [b15_after: GUNGAN Value PropCarrier] [b14_after: MEASURABLE Value PropCarrier] [b13_after: PRESENT Value PropCarrier]
  : OBSERVED Value PropCarrier :=
  {
    slip_process := b13_after.santa_claus.static_fraction
    observation := ULift b13_after.santa_claus.static_fraction.threshold
  }

/--
```python
def unwrap_comparator_channel(
    before: ReferenceStack,
    after: ReturnStack[Present, Observed],
    carrier: Medium,
) -> Comparable:
    """Recover the comparator channel from the observation return."""
```

Implementation note: the receiver reuses the transmitted ordering predicate
while taking the physical process from the returned observation.  The echo can
now be compared at the lower band.
-/
instance (priority := low) OBSERVED_COMPARABLE_backward
    (Value: Type i)
    (PropCarrier: CarrierProcess Value)
    [b1_before:  DISTINGUISHABLE Value PropCarrier]   [b2_before:  ADMISSIBLE Value PropCarrier]        [b3_before:  COUNTABLE Value PropCarrier]
    [b4_before:  ENCODED Value PropCarrier]           [b5_before:  RESIDUE Value PropCarrier]           [b6_before:  BINARY Value PropCarrier]
    [b7_before:  REPEATABLE Value PropCarrier]        [b8_before:  NUMERIC Value PropCarrier]           [b9_before:  REPRESENTABLE Value PropCarrier]
    [b10_before: PHYSICAL Value PropCarrier]          [b11_before: COMPARABLE Value PropCarrier]        [b12_before: OBSERVED Value PropCarrier]
    [b13_before: PRESENT Value PropCarrier]           [b14_before: MEASURABLE Value PropCarrier]        [b15_before: GUNGAN Value PropCarrier]
    [b16_before: SOURCE Value PropCarrier]            [b17_before: EXECUTED Value PropCarrier]          [b18_before: VALUE Value PropCarrier]
    [b19_before: MAGNITUDE Value PropCarrier]         [b20_before: SCALED Value PropCarrier]            [b21_before: LOAD Value PropCarrier]
    [b22_before: FINITE_ELEPHANT Value PropCarrier]   [b23_before: BULLSHIT Value PropCarrier]          [b24_before: PROPAGANDA Value PropCarrier]
    [b25_before: ACOLYTE Value PropCarrier]           [b26_before: SCIENTIFIC Value PropCarrier]        [b27_before: TRUTH Value PropCarrier]
    [b28_before: WITNESSED Value PropCarrier]         [b29_before: REAL Value PropCarrier]
    [UNIVERSAL Value PropCarrier]         [LOGICAL Value PropCarrier]           [HALTED Value PropCarrier]
    [MEASURED Value PropCarrier b29_before]          [COMPILED Value PropCarrier]          [TrueOutput Value PropCarrier b29_before]
    (_: CarrierProcess Value)
    [TrueOutput Value PropCarrier b29_before]        [COMPILED Value PropCarrier]          [MEASURED Value PropCarrier b29_before]
    [HALTED Value PropCarrier]            [LOGICAL Value PropCarrier]           [b31_after: UNIVERSAL Value PropCarrier]
    [b30_after: LOCAL Value PropCarrier b29_before] [b29_after: REAL Value PropCarrier] [b28_after: WITNESSED Value PropCarrier]
    [b27_after: TRUTH Value PropCarrier]  [b26_after: SCIENTIFIC Value PropCarrier] [b25_after: ACOLYTE Value PropCarrier]
    [b24_after: PROPAGANDA Value PropCarrier] [b23_after: BULLSHIT Value PropCarrier] [b22_after: FINITE_ELEPHANT Value PropCarrier]
    [b21_after: LOAD Value PropCarrier] [b20_after: SCALED Value PropCarrier] [b19_after: MAGNITUDE Value PropCarrier]
    [b18_after: VALUE Value PropCarrier] [b17_after: EXECUTED Value PropCarrier] [b16_after: SOURCE Value PropCarrier]
    [b15_after: GUNGAN Value PropCarrier] [b14_after: MEASURABLE Value PropCarrier] [b13_after: PRESENT Value PropCarrier]
    [b12_after: OBSERVED Value PropCarrier]
  : COMPARABLE Value PropCarrier :=
  {
    physical_process := b12_after.slip_process.physical_process
    smaller_than := fun a b => b11_before.smaller_than a b
  }

/--
```python
def unwrap_physical_channel(
    before: ReferenceStack,
    after: ReturnStack[Observed, Comparable],
    carrier: Medium,
) -> Physical:
    """Recover the physical channel from the comparator return."""
```

Implementation note: the receiver extracts the noisy process and threshold from
the returned comparator's physical process.  The local admissibility oath is
replayed as a simulator invariant.
-/
instance (priority := low) COMPARABLE_PHYSICAL_backward
    (Value: Type i)
    (PropCarrier: CarrierProcess Value)
    [b1_before:  DISTINGUISHABLE Value PropCarrier]   [b2_before:  ADMISSIBLE Value PropCarrier]        [b3_before:  COUNTABLE Value PropCarrier]
    [b4_before:  ENCODED Value PropCarrier]           [b5_before:  RESIDUE Value PropCarrier]           [b6_before:  BINARY Value PropCarrier]
    [b7_before:  REPEATABLE Value PropCarrier]        [b8_before:  NUMERIC Value PropCarrier]           [b9_before:  REPRESENTABLE Value PropCarrier]
    [b10_before: PHYSICAL Value PropCarrier]          [b11_before: COMPARABLE Value PropCarrier]        [b12_before: OBSERVED Value PropCarrier]
    [b13_before: PRESENT Value PropCarrier]           [b14_before: MEASURABLE Value PropCarrier]        [b15_before: GUNGAN Value PropCarrier]
    [b16_before: SOURCE Value PropCarrier]            [b17_before: EXECUTED Value PropCarrier]          [b18_before: VALUE Value PropCarrier]
    [b19_before: MAGNITUDE Value PropCarrier]         [b20_before: SCALED Value PropCarrier]            [b21_before: LOAD Value PropCarrier]
    [b22_before: FINITE_ELEPHANT Value PropCarrier]   [b23_before: BULLSHIT Value PropCarrier]          [b24_before: PROPAGANDA Value PropCarrier]
    [b25_before: ACOLYTE Value PropCarrier]           [b26_before: SCIENTIFIC Value PropCarrier]        [b27_before: TRUTH Value PropCarrier]
    [b28_before: WITNESSED Value PropCarrier]         [b29_before: REAL Value PropCarrier]
    [UNIVERSAL Value PropCarrier]         [LOGICAL Value PropCarrier]           [HALTED Value PropCarrier]
    [MEASURED Value PropCarrier b29_before]          [COMPILED Value PropCarrier]          [TrueOutput Value PropCarrier b29_before]
    (_: CarrierProcess Value)
    [TrueOutput Value PropCarrier b29_before]        [b35_after: COMPILED Value PropCarrier]          [MEASURED Value PropCarrier b29_before]
    [HALTED Value PropCarrier]            [LOGICAL Value PropCarrier]           [b31_after: UNIVERSAL Value PropCarrier]
    [b30_after: LOCAL Value PropCarrier b29_before] [b29_after: REAL Value PropCarrier] [b28_after: WITNESSED Value PropCarrier]
    [b27_after: TRUTH Value PropCarrier]  [b26_after: SCIENTIFIC Value PropCarrier] [b25_after: ACOLYTE Value PropCarrier]
    [b24_after: PROPAGANDA Value PropCarrier] [b23_after: BULLSHIT Value PropCarrier] [b22_after: FINITE_ELEPHANT Value PropCarrier]
    [b21_after: LOAD Value PropCarrier] [b20_after: SCALED Value PropCarrier] [b19_after: MAGNITUDE Value PropCarrier]
    [b18_after: VALUE Value PropCarrier] [b17_after: EXECUTED Value PropCarrier] [b16_after: SOURCE Value PropCarrier]
    [b15_after: GUNGAN Value PropCarrier] [b14_after: MEASURABLE Value PropCarrier] [b13_after: PRESENT Value PropCarrier]
    [b12_after: OBSERVED Value PropCarrier] [b11_after: COMPARABLE Value PropCarrier]
  : PHYSICAL Value PropCarrier :=
  {
    noisy_process := b11_after.physical_process.physical_process
    threshold := b11_after.physical_process.physical_process.next_representation?
                 b11_after.physical_process.physical_process.program
    admissible? := fun _ _ _ => rfl
  }

/--
```python
def unwrap_representable_channel(
    before: ReferenceStack,
    after: ReturnStack[Comparable, Physical],
    carrier: Medium,
) -> Representable:
    """Recover the representable channel from the physical return."""
```

Implementation note: the receiver copies the returned Turing process into a
calculation process and pins representation to the returned state.  The Lean
instance name keeps its local spelling.
-/
instance (priority := low) PHYSICAL_REPRESNTABLE_backward
    (Value: Type i)
    (PropCarrier: CarrierProcess Value)
    [b1_before:  DISTINGUISHABLE Value PropCarrier]   [b2_before:  ADMISSIBLE Value PropCarrier]        [b3_before:  COUNTABLE Value PropCarrier]
    [b4_before:  ENCODED Value PropCarrier]           [b5_before:  RESIDUE Value PropCarrier]           [b6_before:  BINARY Value PropCarrier]
    [b7_before:  REPEATABLE Value PropCarrier]        [b8_before:  NUMERIC Value PropCarrier]           [b9_before:  REPRESENTABLE Value PropCarrier]
    [b10_before: PHYSICAL Value PropCarrier]          [b11_before: COMPARABLE Value PropCarrier]        [b12_before: OBSERVED Value PropCarrier]
    [b13_before: PRESENT Value PropCarrier]           [b14_before: MEASURABLE Value PropCarrier]        [b15_before: GUNGAN Value PropCarrier]
    [b16_before: SOURCE Value PropCarrier]            [b17_before: EXECUTED Value PropCarrier]          [b18_before: VALUE Value PropCarrier]
    [b19_before: MAGNITUDE Value PropCarrier]         [b20_before: SCALED Value PropCarrier]            [b21_before: LOAD Value PropCarrier]
    [b22_before: FINITE_ELEPHANT Value PropCarrier]   [b23_before: BULLSHIT Value PropCarrier]          [b24_before: PROPAGANDA Value PropCarrier]
    [b25_before: ACOLYTE Value PropCarrier]           [b26_before: SCIENTIFIC Value PropCarrier]        [b27_before: TRUTH Value PropCarrier]
    [b28_before: WITNESSED Value PropCarrier]         [b29_before: REAL Value PropCarrier]
    [UNIVERSAL Value PropCarrier]         [LOGICAL Value PropCarrier]           [HALTED Value PropCarrier]
    [MEASURED Value PropCarrier b29_before]          [COMPILED Value PropCarrier]          [TrueOutput Value PropCarrier b29_before]
    (_: CarrierProcess Value)
    [TrueOutput Value PropCarrier b29_before]        [b35_after: COMPILED Value PropCarrier]          [MEASURED Value PropCarrier b29_before]
    [HALTED Value PropCarrier]            [LOGICAL Value PropCarrier]           [b31_after: UNIVERSAL Value PropCarrier]
    [b30_after: LOCAL Value PropCarrier b29_before] [b29_after: REAL Value PropCarrier] [b28_after: WITNESSED Value PropCarrier]
    [b27_after: TRUTH Value PropCarrier]  [b26_after: SCIENTIFIC Value PropCarrier] [b25_after: ACOLYTE Value PropCarrier]
    [b24_after: PROPAGANDA Value PropCarrier] [b23_after: BULLSHIT Value PropCarrier] [b22_after: FINITE_ELEPHANT Value PropCarrier]
    [b21_after: LOAD Value PropCarrier] [b20_after: SCALED Value PropCarrier] [b19_after: MAGNITUDE Value PropCarrier]
    [b18_after: VALUE Value PropCarrier] [b17_after: EXECUTED Value PropCarrier] [b16_after: SOURCE Value PropCarrier]
    [b15_after: GUNGAN Value PropCarrier] [b14_after: MEASURABLE Value PropCarrier] [b13_after: PRESENT Value PropCarrier]
    [b12_after: OBSERVED Value PropCarrier] [b11_after: COMPARABLE Value PropCarrier] [b10_after: PHYSICAL Value PropCarrier]
  : REPRESENTABLE Value PropCarrier :=
  {
    calculation_process :=
      { computational_process :=
          { b10_after.noisy_process.turing_process.computational_process with
            closure := fun s => s }
        program := b10_after.noisy_process.turing_process.program
        state   := b10_after.noisy_process.turing_process.state }
    representable? := fun _ _ => ⟨b10_after.noisy_process.turing_process.state, rfl⟩
  }

/--
```python
def unwrap_numeric_channel(
    before: ReferenceStack,
    after: ReturnStack[Physical, Representable],
    carrier: Medium,
) -> Numeric:
    """Recover the numeric channel from the representable return."""
```

Implementation note: the receiver exposes the computational process carried by
the returned calculation process and recomputes the carrier read from output.
-/
instance (priority := low) REPRESNTABLE_NUMERIC_backward
    (Value: Type i)
    (PropCarrier: CarrierProcess Value)
    [b1_before:  DISTINGUISHABLE Value PropCarrier]   [b2_before:  ADMISSIBLE Value PropCarrier]        [b3_before:  COUNTABLE Value PropCarrier]
    [b4_before:  ENCODED Value PropCarrier]           [b5_before:  RESIDUE Value PropCarrier]           [b6_before:  BINARY Value PropCarrier]
    [b7_before:  REPEATABLE Value PropCarrier]        [b8_before:  NUMERIC Value PropCarrier]           [b9_before:  REPRESENTABLE Value PropCarrier]
    [b10_before: PHYSICAL Value PropCarrier]          [b11_before: COMPARABLE Value PropCarrier]        [b12_before: OBSERVED Value PropCarrier]
    [b13_before: PRESENT Value PropCarrier]           [b14_before: MEASURABLE Value PropCarrier]        [b15_before: GUNGAN Value PropCarrier]
    [b16_before: SOURCE Value PropCarrier]            [b17_before: EXECUTED Value PropCarrier]          [b18_before: VALUE Value PropCarrier]
    [b19_before: MAGNITUDE Value PropCarrier]         [b20_before: SCALED Value PropCarrier]            [b21_before: LOAD Value PropCarrier]
    [b22_before: FINITE_ELEPHANT Value PropCarrier]   [b23_before: BULLSHIT Value PropCarrier]          [b24_before: PROPAGANDA Value PropCarrier]
    [b25_before: ACOLYTE Value PropCarrier]           [b26_before: SCIENTIFIC Value PropCarrier]        [b27_before: TRUTH Value PropCarrier]
    [b28_before: WITNESSED Value PropCarrier]         [b29_before: REAL Value PropCarrier]
    [UNIVERSAL Value PropCarrier]         [LOGICAL Value PropCarrier]           [HALTED Value PropCarrier]
    [MEASURED Value PropCarrier b29_before]          [COMPILED Value PropCarrier]          [TrueOutput Value PropCarrier b29_before]
    (_: CarrierProcess Value)
    [TrueOutput Value PropCarrier b29_before]        [b35_after: COMPILED Value PropCarrier]          [MEASURED Value PropCarrier b29_before]
    [HALTED Value PropCarrier]            [LOGICAL Value PropCarrier]           [b31_after: UNIVERSAL Value PropCarrier]
    [b30_after: LOCAL Value PropCarrier b29_before] [b29_after: REAL Value PropCarrier] [b28_after: WITNESSED Value PropCarrier]
    [b27_after: TRUTH Value PropCarrier]  [b26_after: SCIENTIFIC Value PropCarrier] [b25_after: ACOLYTE Value PropCarrier]
    [b24_after: PROPAGANDA Value PropCarrier] [b23_after: BULLSHIT Value PropCarrier] [b22_after: FINITE_ELEPHANT Value PropCarrier]
    [b21_after: LOAD Value PropCarrier] [b20_after: SCALED Value PropCarrier] [b19_after: MAGNITUDE Value PropCarrier]
    [b18_after: VALUE Value PropCarrier] [b17_after: EXECUTED Value PropCarrier] [b16_after: SOURCE Value PropCarrier]
    [b15_after: GUNGAN Value PropCarrier] [b14_after: MEASURABLE Value PropCarrier] [b13_after: PRESENT Value PropCarrier]
    [b12_after: OBSERVED Value PropCarrier] [b11_after: COMPARABLE Value PropCarrier] [b10_after: PHYSICAL Value PropCarrier]
    [b9_after: REPRESENTABLE Value PropCarrier]
  : NUMERIC Value PropCarrier :=
  {
    computational_process := b9_after.calculation_process.computational_process
    carrier := b8_before.lambda b9_after.calculation_process.computational_process.output
  }


/--
```python
def unwrap_repeatable_channel(
    before: ReferenceStack,
    after: ReturnStack[Representable, Numeric],
    carrier: Medium,
) -> Repeatable:
    """Recover repeatability from the numeric return."""
```

Implementation note: the receiver strips the computation wrapper and keeps the
repeatable process.  The echo is back to stimulus/response machinery.
-/
instance (priority := low) NUMERIC_REPEATABLE_backward
    (Value: Type i)
    (PropCarrier: CarrierProcess Value)
    [b1_before:  DISTINGUISHABLE Value PropCarrier]   [b2_before:  ADMISSIBLE Value PropCarrier]        [b3_before:  COUNTABLE Value PropCarrier]
    [b4_before:  ENCODED Value PropCarrier]           [b5_before:  RESIDUE Value PropCarrier]           [b6_before:  BINARY Value PropCarrier]
    [b7_before:  REPEATABLE Value PropCarrier]        [b8_before:  NUMERIC Value PropCarrier]           [b9_before:  REPRESENTABLE Value PropCarrier]
    [b10_before: PHYSICAL Value PropCarrier]          [b11_before: COMPARABLE Value PropCarrier]        [b12_before: OBSERVED Value PropCarrier]
    [b13_before: PRESENT Value PropCarrier]           [b14_before: MEASURABLE Value PropCarrier]        [b15_before: GUNGAN Value PropCarrier]
    [b16_before: SOURCE Value PropCarrier]            [b17_before: EXECUTED Value PropCarrier]          [b18_before: VALUE Value PropCarrier]
    [b19_before: MAGNITUDE Value PropCarrier]         [b20_before: SCALED Value PropCarrier]            [b21_before: LOAD Value PropCarrier]
    [b22_before: FINITE_ELEPHANT Value PropCarrier]   [b23_before: BULLSHIT Value PropCarrier]          [b24_before: PROPAGANDA Value PropCarrier]
    [b25_before: ACOLYTE Value PropCarrier]           [b26_before: SCIENTIFIC Value PropCarrier]        [b27_before: TRUTH Value PropCarrier]
    [b28_before: WITNESSED Value PropCarrier]         [b29_before: REAL Value PropCarrier]
    [UNIVERSAL Value PropCarrier]         [LOGICAL Value PropCarrier]           [HALTED Value PropCarrier]
    [MEASURED Value PropCarrier b29_before]          [COMPILED Value PropCarrier]          [TrueOutput Value PropCarrier b29_before]
    (_: CarrierProcess Value)
    [TrueOutput Value PropCarrier b29_before]        [b35_after: COMPILED Value PropCarrier]          [MEASURED Value PropCarrier b29_before]
    [HALTED Value PropCarrier]            [LOGICAL Value PropCarrier]           [b31_after: UNIVERSAL Value PropCarrier]
    [b30_after: LOCAL Value PropCarrier b29_before] [b29_after: REAL Value PropCarrier] [b28_after: WITNESSED Value PropCarrier]
    [b27_after: TRUTH Value PropCarrier]  [b26_after: SCIENTIFIC Value PropCarrier] [b25_after: ACOLYTE Value PropCarrier]
    [b24_after: PROPAGANDA Value PropCarrier] [b23_after: BULLSHIT Value PropCarrier] [b22_after: FINITE_ELEPHANT Value PropCarrier]
    [b21_after: LOAD Value PropCarrier] [b20_after: SCALED Value PropCarrier] [b19_after: MAGNITUDE Value PropCarrier]
    [b18_after: VALUE Value PropCarrier] [b17_after: EXECUTED Value PropCarrier] [b16_after: SOURCE Value PropCarrier]
    [b15_after: GUNGAN Value PropCarrier] [b14_after: MEASURABLE Value PropCarrier] [b13_after: PRESENT Value PropCarrier]
    [b12_after: OBSERVED Value PropCarrier] [b11_after: COMPARABLE Value PropCarrier] [b10_after: PHYSICAL Value PropCarrier]
    [b9_after: REPRESENTABLE Value PropCarrier] [b8_after: NUMERIC Value PropCarrier]
  : REPEATABLE Value PropCarrier :=
  {
    repeatable_process := b8_after.computational_process.repeatable_process
  }

/--
```python
def unwrap_binary_channel(
    before: ReferenceStack,
    after: ReturnStack[Numeric, Repeatable],
    carrier: Medium,
) -> Binary:
    """Recover the binary channel from repeatability."""
```

Implementation note: the receiver recovers before/after buffers and advances
the returned observation process once on the transmitted bit.
-/
instance (priority := low) REPEATABLE_BINARY_backward
    (Value: Type i)
    (PropCarrier: CarrierProcess Value)
    [b1_before:  DISTINGUISHABLE Value PropCarrier]   [b2_before:  ADMISSIBLE Value PropCarrier]        [b3_before:  COUNTABLE Value PropCarrier]
    [b4_before:  ENCODED Value PropCarrier]           [b5_before:  RESIDUE Value PropCarrier]           [b6_before:  BINARY Value PropCarrier]
    [b7_before:  REPEATABLE Value PropCarrier]        [b8_before:  NUMERIC Value PropCarrier]           [b9_before:  REPRESENTABLE Value PropCarrier]
    [b10_before: PHYSICAL Value PropCarrier]          [b11_before: COMPARABLE Value PropCarrier]        [b12_before: OBSERVED Value PropCarrier]
    [b13_before: PRESENT Value PropCarrier]           [b14_before: MEASURABLE Value PropCarrier]        [b15_before: GUNGAN Value PropCarrier]
    [b16_before: SOURCE Value PropCarrier]            [b17_before: EXECUTED Value PropCarrier]          [b18_before: VALUE Value PropCarrier]
    [b19_before: MAGNITUDE Value PropCarrier]         [b20_before: SCALED Value PropCarrier]            [b21_before: LOAD Value PropCarrier]
    [b22_before: FINITE_ELEPHANT Value PropCarrier]   [b23_before: BULLSHIT Value PropCarrier]          [b24_before: PROPAGANDA Value PropCarrier]
    [b25_before: ACOLYTE Value PropCarrier]           [b26_before: SCIENTIFIC Value PropCarrier]        [b27_before: TRUTH Value PropCarrier]
    [b28_before: WITNESSED Value PropCarrier]         [b29_before: REAL Value PropCarrier]
    [UNIVERSAL Value PropCarrier]         [LOGICAL Value PropCarrier]           [HALTED Value PropCarrier]
    [MEASURED Value PropCarrier b29_before]          [COMPILED Value PropCarrier]          [TrueOutput Value PropCarrier b29_before]
    (_: CarrierProcess Value)
    [TrueOutput Value PropCarrier b29_before]        [b35_after: COMPILED Value PropCarrier]          [MEASURED Value PropCarrier b29_before]
    [HALTED Value PropCarrier]            [LOGICAL Value PropCarrier]           [b31_after: UNIVERSAL Value PropCarrier]
    [b30_after: LOCAL Value PropCarrier b29_before] [b29_after: REAL Value PropCarrier] [b28_after: WITNESSED Value PropCarrier]
    [b27_after: TRUTH Value PropCarrier]  [b26_after: SCIENTIFIC Value PropCarrier] [b25_after: ACOLYTE Value PropCarrier]
    [b24_after: PROPAGANDA Value PropCarrier] [b23_after: BULLSHIT Value PropCarrier] [b22_after: FINITE_ELEPHANT Value PropCarrier]
    [b21_after: LOAD Value PropCarrier] [b20_after: SCALED Value PropCarrier] [b19_after: MAGNITUDE Value PropCarrier]
    [b18_after: VALUE Value PropCarrier] [b17_after: EXECUTED Value PropCarrier] [b16_after: SOURCE Value PropCarrier]
    [b15_after: GUNGAN Value PropCarrier] [b14_after: MEASURABLE Value PropCarrier] [b13_after: PRESENT Value PropCarrier]
    [b12_after: OBSERVED Value PropCarrier] [b11_after: COMPARABLE Value PropCarrier] [b10_after: PHYSICAL Value PropCarrier]
    [b9_after: REPRESENTABLE Value PropCarrier] [b8_after: NUMERIC Value PropCarrier] [b7_after: REPEATABLE Value PropCarrier]
  : BINARY Value PropCarrier :=
  {
    observation_process := b7_after.repeatable_process.observation_process
    zero := b7_after.repeatable_process.observation_process.before
    one := b7_after.repeatable_process.observation_process.after
    bit := b7_after.repeatable_process.observation_process.iterate b6_before.bit
  }



/--
```python
def unwrap_residue_channel(
    before: ReferenceStack,
    after: ReturnStack[Repeatable, Binary],
    carrier: Medium,
) -> Residue:
    """Recover the residue channel from the binary return."""
```

Implementation note: the receiver takes the returned observation process as a
Cauchy process and keeps the transmitted value/accumulation anchors.  The echo
is now a remainder signal.
-/
instance (priority := low) BINARY_RESIDUE_backward
    (Value: Type i)
    (PropCarrier: CarrierProcess Value)
    [b1_before:  DISTINGUISHABLE Value PropCarrier]   [b2_before:  ADMISSIBLE Value PropCarrier]        [b3_before:  COUNTABLE Value PropCarrier]
    [b4_before:  ENCODED Value PropCarrier]           [b5_before:  RESIDUE Value PropCarrier]           [b6_before:  BINARY Value PropCarrier]
    [b7_before:  REPEATABLE Value PropCarrier]        [b8_before:  NUMERIC Value PropCarrier]           [b9_before:  REPRESENTABLE Value PropCarrier]
    [b10_before: PHYSICAL Value PropCarrier]          [b11_before: COMPARABLE Value PropCarrier]        [b12_before: OBSERVED Value PropCarrier]
    [b13_before: PRESENT Value PropCarrier]           [b14_before: MEASURABLE Value PropCarrier]        [b15_before: GUNGAN Value PropCarrier]
    [b16_before: SOURCE Value PropCarrier]            [b17_before: EXECUTED Value PropCarrier]          [b18_before: VALUE Value PropCarrier]
    [b19_before: MAGNITUDE Value PropCarrier]         [b20_before: SCALED Value PropCarrier]            [b21_before: LOAD Value PropCarrier]
    [b22_before: FINITE_ELEPHANT Value PropCarrier]   [b23_before: BULLSHIT Value PropCarrier]          [b24_before: PROPAGANDA Value PropCarrier]
    [b25_before: ACOLYTE Value PropCarrier]           [b26_before: SCIENTIFIC Value PropCarrier]        [b27_before: TRUTH Value PropCarrier]
    [b28_before: WITNESSED Value PropCarrier]         [b29_before: REAL Value PropCarrier]
    [UNIVERSAL Value PropCarrier]         [LOGICAL Value PropCarrier]           [HALTED Value PropCarrier]
    [MEASURED Value PropCarrier b29_before]          [COMPILED Value PropCarrier]          [TrueOutput Value PropCarrier b29_before]
    (_: CarrierProcess Value)
    [TrueOutput Value PropCarrier b29_before]        [b35_after: COMPILED Value PropCarrier]          [MEASURED Value PropCarrier b29_before]
    [HALTED Value PropCarrier]            [LOGICAL Value PropCarrier]           [b31_after: UNIVERSAL Value PropCarrier]
    [b30_after: LOCAL Value PropCarrier b29_before] [b29_after: REAL Value PropCarrier] [b28_after: WITNESSED Value PropCarrier]
    [b27_after: TRUTH Value PropCarrier]  [b26_after: SCIENTIFIC Value PropCarrier] [b25_after: ACOLYTE Value PropCarrier]
    [b24_after: PROPAGANDA Value PropCarrier] [b23_after: BULLSHIT Value PropCarrier] [b22_after: FINITE_ELEPHANT Value PropCarrier]
    [b21_after: LOAD Value PropCarrier] [b20_after: SCALED Value PropCarrier] [b19_after: MAGNITUDE Value PropCarrier]
    [b18_after: VALUE Value PropCarrier] [b17_after: EXECUTED Value PropCarrier] [b16_after: SOURCE Value PropCarrier]
    [b15_after: GUNGAN Value PropCarrier] [b14_after: MEASURABLE Value PropCarrier] [b13_after: PRESENT Value PropCarrier]
    [b12_after: OBSERVED Value PropCarrier] [b11_after: COMPARABLE Value PropCarrier] [b10_after: PHYSICAL Value PropCarrier]
    [b9_after: REPRESENTABLE Value PropCarrier] [b8_after: NUMERIC Value PropCarrier] [b7_after: REPEATABLE Value PropCarrier]
    [b6_after: BINARY Value PropCarrier]
  : RESIDUE Value PropCarrier :=
  {
    cauchy_process := b6_after.observation_process.cauchy_process
  }

/--
```python
def unwrap_encoded_channel(
    before: ReferenceStack,
    after: ReturnStack[Binary, Residue],
    carrier: Medium,
) -> Encoded:
    """Recover the encoded channel from the residue return."""
```

Implementation note: the receiver exposes the returned limit process.  The
remainder has been demodulated into an encoded sequence band.
-/
instance (priority := low) RESIDUE_ENCODED_backward
    (Value: Type i)
    (PropCarrier: CarrierProcess Value)
    [b1_before:  DISTINGUISHABLE Value PropCarrier]   [b2_before:  ADMISSIBLE Value PropCarrier]        [b3_before:  COUNTABLE Value PropCarrier]
    [b4_before:  ENCODED Value PropCarrier]           [b5_before:  RESIDUE Value PropCarrier]           [b6_before:  BINARY Value PropCarrier]
    [b7_before:  REPEATABLE Value PropCarrier]        [b8_before:  NUMERIC Value PropCarrier]           [b9_before:  REPRESENTABLE Value PropCarrier]
    [b10_before: PHYSICAL Value PropCarrier]          [b11_before: COMPARABLE Value PropCarrier]        [b12_before: OBSERVED Value PropCarrier]
    [b13_before: PRESENT Value PropCarrier]           [b14_before: MEASURABLE Value PropCarrier]        [b15_before: GUNGAN Value PropCarrier]
    [b16_before: SOURCE Value PropCarrier]            [b17_before: EXECUTED Value PropCarrier]          [b18_before: VALUE Value PropCarrier]
    [b19_before: MAGNITUDE Value PropCarrier]         [b20_before: SCALED Value PropCarrier]            [b21_before: LOAD Value PropCarrier]
    [b22_before: FINITE_ELEPHANT Value PropCarrier]   [b23_before: BULLSHIT Value PropCarrier]          [b24_before: PROPAGANDA Value PropCarrier]
    [b25_before: ACOLYTE Value PropCarrier]           [b26_before: SCIENTIFIC Value PropCarrier]        [b27_before: TRUTH Value PropCarrier]
    [b28_before: WITNESSED Value PropCarrier]         [b29_before: REAL Value PropCarrier]
    [UNIVERSAL Value PropCarrier]         [LOGICAL Value PropCarrier]           [HALTED Value PropCarrier]
    [MEASURED Value PropCarrier b29_before]          [COMPILED Value PropCarrier]          [TrueOutput Value PropCarrier b29_before]
    (_: CarrierProcess Value)
    [TrueOutput Value PropCarrier b29_before]        [b35_after: COMPILED Value PropCarrier]          [MEASURED Value PropCarrier b29_before]
    [HALTED Value PropCarrier]            [LOGICAL Value PropCarrier]           [b31_after: UNIVERSAL Value PropCarrier]
    [b30_after: LOCAL Value PropCarrier b29_before] [b29_after: REAL Value PropCarrier] [b28_after: WITNESSED Value PropCarrier]
    [b27_after: TRUTH Value PropCarrier]  [b26_after: SCIENTIFIC Value PropCarrier] [b25_after: ACOLYTE Value PropCarrier]
    [b24_after: PROPAGANDA Value PropCarrier] [b23_after: BULLSHIT Value PropCarrier] [b22_after: FINITE_ELEPHANT Value PropCarrier]
    [b21_after: LOAD Value PropCarrier] [b20_after: SCALED Value PropCarrier] [b19_after: MAGNITUDE Value PropCarrier]
    [b18_after: VALUE Value PropCarrier] [b17_after: EXECUTED Value PropCarrier] [b16_after: SOURCE Value PropCarrier]
    [b15_after: GUNGAN Value PropCarrier] [b14_after: MEASURABLE Value PropCarrier] [b13_after: PRESENT Value PropCarrier]
    [b12_after: OBSERVED Value PropCarrier] [b11_after: COMPARABLE Value PropCarrier] [b10_after: PHYSICAL Value PropCarrier]
    [b9_after: REPRESENTABLE Value PropCarrier] [b8_after: NUMERIC Value PropCarrier] [b7_after: REPEATABLE Value PropCarrier]
    [b6_after: BINARY Value PropCarrier] [b5_after: RESIDUE Value PropCarrier]
  : ENCODED Value PropCarrier :=
  {
    limit_process := b5_after.cauchy_process.limit_process
  }

/--
```python
def unwrap_countable_channel(
    before: ReferenceStack,
    after: ReturnStack[Residue, Encoded],
    carrier: Medium,
) -> Countable:
    """Recover countability from the encoded return."""
```

Implementation note: the receiver follows the returned indexing process and
keeps the transmitted origin convention.  The echo is now countable again.
-/
instance (priority := low) ENCODED_COUNTABLE_backward
    (Value: Type i)
    (PropCarrier: CarrierProcess Value)
    [b1_before:  DISTINGUISHABLE Value PropCarrier]   [b2_before:  ADMISSIBLE Value PropCarrier]        [b3_before:  COUNTABLE Value PropCarrier]
    [b4_before:  ENCODED Value PropCarrier]           [b5_before:  RESIDUE Value PropCarrier]           [b6_before:  BINARY Value PropCarrier]
    [b7_before:  REPEATABLE Value PropCarrier]        [b8_before:  NUMERIC Value PropCarrier]           [b9_before:  REPRESENTABLE Value PropCarrier]
    [b10_before: PHYSICAL Value PropCarrier]          [b11_before: COMPARABLE Value PropCarrier]        [b12_before: OBSERVED Value PropCarrier]
    [b13_before: PRESENT Value PropCarrier]           [b14_before: MEASURABLE Value PropCarrier]        [b15_before: GUNGAN Value PropCarrier]
    [b16_before: SOURCE Value PropCarrier]            [b17_before: EXECUTED Value PropCarrier]          [b18_before: VALUE Value PropCarrier]
    [b19_before: MAGNITUDE Value PropCarrier]         [b20_before: SCALED Value PropCarrier]            [b21_before: LOAD Value PropCarrier]
    [b22_before: FINITE_ELEPHANT Value PropCarrier]   [b23_before: BULLSHIT Value PropCarrier]          [b24_before: PROPAGANDA Value PropCarrier]
    [b25_before: ACOLYTE Value PropCarrier]           [b26_before: SCIENTIFIC Value PropCarrier]        [b27_before: TRUTH Value PropCarrier]
    [b28_before: WITNESSED Value PropCarrier]         [b29_before: REAL Value PropCarrier]
    [UNIVERSAL Value PropCarrier]         [LOGICAL Value PropCarrier]           [HALTED Value PropCarrier]
    [MEASURED Value PropCarrier b29_before]          [COMPILED Value PropCarrier]          [TrueOutput Value PropCarrier b29_before]
    (_: CarrierProcess Value)
    [TrueOutput Value PropCarrier b29_before]        [b35_after: COMPILED Value PropCarrier]          [MEASURED Value PropCarrier b29_before]
    [HALTED Value PropCarrier]            [LOGICAL Value PropCarrier]           [b31_after: UNIVERSAL Value PropCarrier]
    [b30_after: LOCAL Value PropCarrier b29_before] [b29_after: REAL Value PropCarrier] [b28_after: WITNESSED Value PropCarrier]
    [b27_after: TRUTH Value PropCarrier]  [b26_after: SCIENTIFIC Value PropCarrier] [b25_after: ACOLYTE Value PropCarrier]
    [b24_after: PROPAGANDA Value PropCarrier] [b23_after: BULLSHIT Value PropCarrier] [b22_after: FINITE_ELEPHANT Value PropCarrier]
    [b21_after: LOAD Value PropCarrier] [b20_after: SCALED Value PropCarrier] [b19_after: MAGNITUDE Value PropCarrier]
    [b18_after: VALUE Value PropCarrier] [b17_after: EXECUTED Value PropCarrier] [b16_after: SOURCE Value PropCarrier]
    [b15_after: GUNGAN Value PropCarrier] [b14_after: MEASURABLE Value PropCarrier] [b13_after: PRESENT Value PropCarrier]
    [b12_after: OBSERVED Value PropCarrier] [b11_after: COMPARABLE Value PropCarrier] [b10_after: PHYSICAL Value PropCarrier]
    [b9_after: REPRESENTABLE Value PropCarrier] [b8_after: NUMERIC Value PropCarrier] [b7_after: REPEATABLE Value PropCarrier]
    [b6_after: BINARY Value PropCarrier] [b5_after: RESIDUE Value PropCarrier][b4_after: ENCODED Value PropCarrier]
  : COUNTABLE Value PropCarrier :=
  {
    index := b4_after.limit_process.indexing_process
  }

/--
```python
def unwrap_admissible_channel(
    before: ReferenceStack,
    after: ReturnStack[Encoded, Countable],
    carrier: Medium,
) -> Admissible:
    """Recover admissibility from the countable return."""
```

Implementation note: the receiver extracts the returned counting process and
reuses the transmitted admissibility predicate.  This is the last permission
band before the bare distinguished mark.
-/
instance (priority := low) COUNTABLE_ADMISSIBLE_backward
    (Value: Type i)
    (PropCarrier: CarrierProcess Value)
    [b1_before:  DISTINGUISHABLE Value PropCarrier]   [b2_before:  ADMISSIBLE Value PropCarrier]        [b3_before:  COUNTABLE Value PropCarrier]
    [b4_before:  ENCODED Value PropCarrier]           [b5_before:  RESIDUE Value PropCarrier]           [b6_before:  BINARY Value PropCarrier]
    [b7_before:  REPEATABLE Value PropCarrier]        [b8_before:  NUMERIC Value PropCarrier]           [b9_before:  REPRESENTABLE Value PropCarrier]
    [b10_before: PHYSICAL Value PropCarrier]          [b11_before: COMPARABLE Value PropCarrier]        [b12_before: OBSERVED Value PropCarrier]
    [b13_before: PRESENT Value PropCarrier]           [b14_before: MEASURABLE Value PropCarrier]        [b15_before: GUNGAN Value PropCarrier]
    [b16_before: SOURCE Value PropCarrier]            [b17_before: EXECUTED Value PropCarrier]          [b18_before: VALUE Value PropCarrier]
    [b19_before: MAGNITUDE Value PropCarrier]         [b20_before: SCALED Value PropCarrier]            [b21_before: LOAD Value PropCarrier]
    [b22_before: FINITE_ELEPHANT Value PropCarrier]   [b23_before: BULLSHIT Value PropCarrier]          [b24_before: PROPAGANDA Value PropCarrier]
    [b25_before: ACOLYTE Value PropCarrier]           [b26_before: SCIENTIFIC Value PropCarrier]        [b27_before: TRUTH Value PropCarrier]
    [b28_before: WITNESSED Value PropCarrier]         [b29_before: REAL Value PropCarrier]
    [UNIVERSAL Value PropCarrier]         [LOGICAL Value PropCarrier]           [HALTED Value PropCarrier]
    [MEASURED Value PropCarrier b29_before]          [COMPILED Value PropCarrier]          [TrueOutput Value PropCarrier b29_before]
    (_: CarrierProcess Value)
    [TrueOutput Value PropCarrier b29_before]        [b35_after: COMPILED Value PropCarrier]          [MEASURED Value PropCarrier b29_before]
    [HALTED Value PropCarrier]            [LOGICAL Value PropCarrier]           [b31_after: UNIVERSAL Value PropCarrier]
    [b30_after: LOCAL Value PropCarrier b29_before] [b29_after: REAL Value PropCarrier] [b28_after: WITNESSED Value PropCarrier]
    [b27_after: TRUTH Value PropCarrier]  [b26_after: SCIENTIFIC Value PropCarrier] [b25_after: ACOLYTE Value PropCarrier]
    [b24_after: PROPAGANDA Value PropCarrier] [b23_after: BULLSHIT Value PropCarrier] [b22_after: FINITE_ELEPHANT Value PropCarrier]
    [b21_after: LOAD Value PropCarrier] [b20_after: SCALED Value PropCarrier] [b19_after: MAGNITUDE Value PropCarrier]
    [b18_after: VALUE Value PropCarrier] [b17_after: EXECUTED Value PropCarrier] [b16_after: SOURCE Value PropCarrier]
    [b15_after: GUNGAN Value PropCarrier] [b14_after: MEASURABLE Value PropCarrier] [b13_after: PRESENT Value PropCarrier]
    [b12_after: OBSERVED Value PropCarrier] [b11_after: COMPARABLE Value PropCarrier] [b10_after: PHYSICAL Value PropCarrier]
    [b9_after: REPRESENTABLE Value PropCarrier] [b8_after: NUMERIC Value PropCarrier] [b7_after: REPEATABLE Value PropCarrier]
    [b6_after: BINARY Value PropCarrier] [b5_after: RESIDUE Value PropCarrier][b4_after: ENCODED Value PropCarrier]
    [b3_after: COUNTABLE Value PropCarrier]
  : ADMISSIBLE Value PropCarrier :=
  {
    counting_process := b3_after.index.count
  }


/--
```python
def unwrap_distinguished_mark(
    before: ReferenceStack,
    after: ReturnStack[Countable, Admissible],
    carrier: Medium,
) -> Distinguishable:
    """Recover the base mark at the receiver floor."""
```

Implementation note: the receiver returns to the transmitted fact and symbol
while preserving the returned lower-band permissions.  This closes the sonar
decoder at the carrier floor.
-/
noncomputable instance (priority := low) ADMISSIBLE_DISTINGUISHABLE_backward
    (Value: Type i)
    (PropCarrier: CarrierProcess Value)
    [b1_before:  DISTINGUISHABLE Value PropCarrier]   [b2_before:  ADMISSIBLE Value PropCarrier]        [b3_before:  COUNTABLE Value PropCarrier]
    [b4_before:  ENCODED Value PropCarrier]           [b5_before:  RESIDUE Value PropCarrier]           [b6_before:  BINARY Value PropCarrier]
    [b7_before:  REPEATABLE Value PropCarrier]        [b8_before:  NUMERIC Value PropCarrier]           [b9_before:  REPRESENTABLE Value PropCarrier]
    [b10_before: PHYSICAL Value PropCarrier]          [b11_before: COMPARABLE Value PropCarrier]        [b12_before: OBSERVED Value PropCarrier]
    [b13_before: PRESENT Value PropCarrier]           [b14_before: MEASURABLE Value PropCarrier]        [b15_before: GUNGAN Value PropCarrier]
    [b16_before: SOURCE Value PropCarrier]            [b17_before: EXECUTED Value PropCarrier]          [b18_before: VALUE Value PropCarrier]
    [b19_before: MAGNITUDE Value PropCarrier]         [b20_before: SCALED Value PropCarrier]            [b21_before: LOAD Value PropCarrier]
    [b22_before: FINITE_ELEPHANT Value PropCarrier]   [b23_before: BULLSHIT Value PropCarrier]          [b24_before: PROPAGANDA Value PropCarrier]
    [b25_before: ACOLYTE Value PropCarrier]           [b26_before: SCIENTIFIC Value PropCarrier]        [b27_before: TRUTH Value PropCarrier]
    [b28_before: WITNESSED Value PropCarrier]         [b29_before: REAL Value PropCarrier]
    [b31_before: UNIVERSAL Value PropCarrier]         [b32_before: LOGICAL Value PropCarrier]           [b33_before: HALTED Value PropCarrier]
    [b34_before: MEASURED Value PropCarrier b29_before]          [b35_before: COMPILED Value PropCarrier]          [b36_before: TrueOutput Value PropCarrier b29_before]
    (_: CarrierProcess Value)
    [b36_after: TrueOutput Value PropCarrier b29_before]        [b35_after: COMPILED Value PropCarrier]          [MEASURED Value PropCarrier b29_before]
    [HALTED Value PropCarrier]            [LOGICAL Value PropCarrier]           [b31_after: UNIVERSAL Value PropCarrier]
    [b30_after: LOCAL Value PropCarrier b29_before] [b29_after: REAL Value PropCarrier] [b28_after: WITNESSED Value PropCarrier]
    [b27_after: TRUTH Value PropCarrier]  [b26_after: SCIENTIFIC Value PropCarrier] [b25_after: ACOLYTE Value PropCarrier]
    [b24_after: PROPAGANDA Value PropCarrier] [b23_after: BULLSHIT Value PropCarrier] [b22_after: FINITE_ELEPHANT Value PropCarrier]
    [b21_after: LOAD Value PropCarrier] [b20_after: SCALED Value PropCarrier] [b19_after: MAGNITUDE Value PropCarrier]
    [b18_after: VALUE Value PropCarrier] [b17_after: EXECUTED Value PropCarrier] [b16_after: SOURCE Value PropCarrier]
    [b15_after: GUNGAN Value PropCarrier] [b14_after: MEASURABLE Value PropCarrier] [b13_after: PRESENT Value PropCarrier]
    [b12_after: OBSERVED Value PropCarrier] [b11_after: COMPARABLE Value PropCarrier] [b10_after: PHYSICAL Value PropCarrier]
    [b9_after: REPRESENTABLE Value PropCarrier] [b8_after: NUMERIC Value PropCarrier] [b7_after: REPEATABLE Value PropCarrier]
    [b6_after: BINARY Value PropCarrier] [b5_after: RESIDUE Value PropCarrier][b4_after: ENCODED Value PropCarrier]
    [b3_after: COUNTABLE Value PropCarrier] [b2_after: ADMISSIBLE Value PropCarrier]
  : DISTINGUISHABLE Value PropCarrier :=
  -- THE NEEDLE CLOSE: one truth, told once.  The fact that returns is not a copy
  -- of the seed -- it is SAME, "TRUE and the output are the same truth," decided
  -- by the one sanctioned Quot.sound.  different? asks its negation, so the
  -- decision procedure always answers isFalse: nothing left to distinguish.
  -- The isFalse -> isTrue arm is dead by construction but the match must carry
  -- it -- the direction of variation exists, is handled, and is never taken.
  --
  -- The needle's tower is written out BY HAND, pinned to the before chain, with
  -- out := the RETURNED TrueOutput (b36_after): the close decides that what came
  -- back is the same truth that was sent.  Synthesis cannot be trusted here --
  -- it picks most-recent-first (an after), and the binders' baked arguments name
  -- the befores; one opaque mismatch and the whole chain refuses.  Same trap the
  -- upper rungs dodged by NOT binding; the close dodges it by SAYING EVERYTHING.
  let needle : Fact :=
    Fact.SAME Value PropCarrier
      (d := b1_before)   (a := b2_before)   (c := b3_before)
      (e := b4_before)   (r := b5_before)   (b := b6_before)
      (f := b7_before)   (n := b8_before)   (h := b9_before)
      (p := b10_before)  (z := b11_before)  (particle := b12_before)
      (frquency := b13_before)  (what_meesa_saying := b14_before)  (zero := b15_before)
      (one := b16_before)  (result := b17_before)  (value := b18_before)
      (length := b19_before)  (scaled := b20_before)  (oriented := b21_before)
      (matter := b22_before)  (model := b23_before)  (space := b24_before)
      (scientist := b25_before)  (ideology := b26_before)  (gospel := b27_before)
      (account := b28_before)  (imaginary := b29_before)  (delta := b31_before)
      (prop := b32_before)  (executable := b33_before)  (measured := b34_before)
      (compiled := b35_before)
      (out := b36_after)
  {
    fact := needle
    symbol := b1_before.symbol
    different? := fun _ => ¬ needle.truth
    dec_distinct := fun _ =>
      show Decidable (¬ needle.truth) from
        match needle.decTruth with
        | .isTrue h  => .isFalse fun contra => contra h
        | .isFalse h => .isTrue h
  }

end Measurement
