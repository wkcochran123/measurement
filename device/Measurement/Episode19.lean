import Measurement.Episode18

/- MEANWHILE 19 -- THE CLASS TRACE. The second tape (law 5): one cell per class,
descent seam-to-lower-bound; constructed-vs-slip fact pair per cell; a stack,
read in reverse by Meanwhile20. This trace only APPENDS; .boot is never written
here -- the carried tape enters as a parameter at the anchor. -/

namespace Measurement

class TRACED (Value: Type i) (Carrier: CarrierProcess Value) (rung: Nat) where
  tape : CompilerTape

instance (priority := low) TRACED_seam
    (Value: Type i) (Carrier: CarrierProcess Value)
    (trace_in: CompilerTape)
    : TRACED Value Carrier 36 := { tape := trace_in }

instance (priority := low) TRACED_TrueOutput
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
    -- UNIVERSAL / LOGICAL / HALTED deliberately NOT bound -- before, after, OR
    -- slip.  Class MEASURED's description type FROZE the concrete forward
    -- instances (UNIVERSAL_REAL and its chain) at Episode 13 definition time;
    -- any local run-band instance shadows the frozen ones and defeq refuses.
    -- The run-band slips therefore cross this seam as PLAIN DATA below --
    -- SpaceTimePath / EKG / Prop are ground-free inductives -- computed by the
    -- caller in a scope where the UNIVERSAL and LOGICAL slips are still legal.
    [b34_before: MEASURED Value PropCarrier b29_before]          [b35_before: COMPILED Value PropCarrier]          [b36_before: TrueOutput Value PropCarrier b29_before]
    (imaginary: CarrierProcess Value)
    [b36_after: TrueOutput Value PropCarrier b29_before]        [b35_after: COMPILED Value PropCarrier]          [b34_after: MEASURED Value PropCarrier b29_before]
    [b29_after: REAL Value PropCarrier] [b28_after: WITNESSED Value PropCarrier]
    [b27_after: TRUTH Value PropCarrier]  [b26_after: SCIENTIFIC Value PropCarrier] [b25_after: ACOLYTE Value PropCarrier]
    [b24_after: PROPAGANDA Value PropCarrier] [b23_after: BULLSHIT Value PropCarrier] [b22_after: FINITE_ELEPHANT Value PropCarrier]
    [b21_after: LOAD Value PropCarrier] [b20_after: SCALED Value PropCarrier] [b19_after: MAGNITUDE Value PropCarrier]
    [b18_after: VALUE Value PropCarrier] [b17_after: EXECUTED Value PropCarrier] [b16_after: SOURCE Value PropCarrier]
    [b15_after: GUNGAN Value PropCarrier] [b14_after: MEASURABLE Value PropCarrier] [b13_after: PRESENT Value PropCarrier]
    [b12_after: OBSERVED Value PropCarrier] [b11_after: COMPARABLE Value PropCarrier] [b10_after: PHYSICAL Value PropCarrier]
    [b9_after: REPRESENTABLE Value PropCarrier] [b8_after: NUMERIC Value PropCarrier] [b7_after: REPEATABLE Value PropCarrier]
    [b6_after: BINARY Value PropCarrier] [b5_after: RESIDUE Value PropCarrier][b4_after: ENCODED Value PropCarrier]
    [b3_after: COUNTABLE Value PropCarrier] [b2_after: ADMISSIBLE Value PropCarrier] [b1_after: DISTINGUISHABLE Value PropCarrier]
    (ledger: Fact)
    (b1_slip: DISTINGUISHABLE Value PropCarrier) (b2_slip: ADMISSIBLE Value PropCarrier) (b3_slip: COUNTABLE Value PropCarrier)
    (b4_slip: ENCODED Value PropCarrier) (b5_slip: RESIDUE Value PropCarrier) (b6_slip: BINARY Value PropCarrier)
    (b7_slip: REPEATABLE Value PropCarrier) (b8_slip: NUMERIC Value PropCarrier) (b9_slip: REPRESENTABLE Value PropCarrier)
    (b10_slip: PHYSICAL Value PropCarrier) (b11_slip: COMPARABLE Value PropCarrier) (b12_slip: OBSERVED Value PropCarrier)
    (b13_slip: PRESENT Value PropCarrier) (b14_slip: MEASURABLE Value PropCarrier) (b15_slip: GUNGAN Value PropCarrier)
    (b16_slip: SOURCE Value PropCarrier) (b17_slip: EXECUTED Value PropCarrier) (b18_slip: VALUE Value PropCarrier)
    (b19_slip: MAGNITUDE Value PropCarrier) (b20_slip: SCALED Value PropCarrier) (b21_slip: LOAD Value PropCarrier)
    (b22_slip: FINITE_ELEPHANT Value PropCarrier) (b23_slip: BULLSHIT Value PropCarrier) (b24_slip: PROPAGANDA Value PropCarrier)
    (b25_slip: ACOLYTE Value PropCarrier) (b26_slip: SCIENTIFIC Value PropCarrier) (b27_slip: TRUTH Value PropCarrier)
    (b28_slip: WITNESSED Value PropCarrier) (b29_slip: REAL Value PropCarrier)
    -- The run-band slip data, ground-free (see note above): the source and its
    -- torpedoed binary, the build verdict, the completed pass's calibration, and
    -- the log-coherence proposition -- b31_slip/b32_slip's content, minus their
    -- poisonous instance wrappers.
    (source_slip: SpaceTimePath) (compiled_slip: SpaceTimePath) (built_slip: Prop)
    (ekg_slip: Calibration.EKG) (coherent_slip: Prop)
    (b34_slip: MEASURED Value PropCarrier b29_slip) (b35_slip: COMPILED Value PropCarrier) (b36_slip: TrueOutput Value PropCarrier b29_slip)
    [above: TRACED Value PropCarrier 36]
    : TRACED Value PropCarrier 35 :=
    { tape := .strap ledger b1_slip.fact Value (ULift.{i+1, i} Value) above.tape }

instance (priority := low) TRACED_COMPILED
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
    -- UNIVERSAL / LOGICAL / HALTED deliberately NOT bound -- before, after, OR
    -- slip.  Class MEASURED's description type FROZE the concrete forward
    -- instances (UNIVERSAL_REAL and its chain) at Episode 13 definition time;
    -- any local run-band instance shadows the frozen ones and defeq refuses.
    -- The run-band slips therefore cross this seam as PLAIN DATA below --
    -- SpaceTimePath / EKG / Prop are ground-free inductives -- computed by the
    -- caller in a scope where the UNIVERSAL and LOGICAL slips are still legal.
    [b34_before: MEASURED Value PropCarrier b29_before]          [b35_before: COMPILED Value PropCarrier]          [b36_before: TrueOutput Value PropCarrier b29_before]
    (imaginary: CarrierProcess Value)
    [b36_after: TrueOutput Value PropCarrier b29_before]        [b35_after: COMPILED Value PropCarrier]          [b34_after: MEASURED Value PropCarrier b29_before]
    [b29_after: REAL Value PropCarrier] [b28_after: WITNESSED Value PropCarrier]
    [b27_after: TRUTH Value PropCarrier]  [b26_after: SCIENTIFIC Value PropCarrier] [b25_after: ACOLYTE Value PropCarrier]
    [b24_after: PROPAGANDA Value PropCarrier] [b23_after: BULLSHIT Value PropCarrier] [b22_after: FINITE_ELEPHANT Value PropCarrier]
    [b21_after: LOAD Value PropCarrier] [b20_after: SCALED Value PropCarrier] [b19_after: MAGNITUDE Value PropCarrier]
    [b18_after: VALUE Value PropCarrier] [b17_after: EXECUTED Value PropCarrier] [b16_after: SOURCE Value PropCarrier]
    [b15_after: GUNGAN Value PropCarrier] [b14_after: MEASURABLE Value PropCarrier] [b13_after: PRESENT Value PropCarrier]
    [b12_after: OBSERVED Value PropCarrier] [b11_after: COMPARABLE Value PropCarrier] [b10_after: PHYSICAL Value PropCarrier]
    [b9_after: REPRESENTABLE Value PropCarrier] [b8_after: NUMERIC Value PropCarrier] [b7_after: REPEATABLE Value PropCarrier]
    [b6_after: BINARY Value PropCarrier] [b5_after: RESIDUE Value PropCarrier][b4_after: ENCODED Value PropCarrier]
    [b3_after: COUNTABLE Value PropCarrier] [b2_after: ADMISSIBLE Value PropCarrier] [b1_after: DISTINGUISHABLE Value PropCarrier]
    (ledger: Fact)
    (b1_slip: DISTINGUISHABLE Value PropCarrier) (b2_slip: ADMISSIBLE Value PropCarrier) (b3_slip: COUNTABLE Value PropCarrier)
    (b4_slip: ENCODED Value PropCarrier) (b5_slip: RESIDUE Value PropCarrier) (b6_slip: BINARY Value PropCarrier)
    (b7_slip: REPEATABLE Value PropCarrier) (b8_slip: NUMERIC Value PropCarrier) (b9_slip: REPRESENTABLE Value PropCarrier)
    (b10_slip: PHYSICAL Value PropCarrier) (b11_slip: COMPARABLE Value PropCarrier) (b12_slip: OBSERVED Value PropCarrier)
    (b13_slip: PRESENT Value PropCarrier) (b14_slip: MEASURABLE Value PropCarrier) (b15_slip: GUNGAN Value PropCarrier)
    (b16_slip: SOURCE Value PropCarrier) (b17_slip: EXECUTED Value PropCarrier) (b18_slip: VALUE Value PropCarrier)
    (b19_slip: MAGNITUDE Value PropCarrier) (b20_slip: SCALED Value PropCarrier) (b21_slip: LOAD Value PropCarrier)
    (b22_slip: FINITE_ELEPHANT Value PropCarrier) (b23_slip: BULLSHIT Value PropCarrier) (b24_slip: PROPAGANDA Value PropCarrier)
    (b25_slip: ACOLYTE Value PropCarrier) (b26_slip: SCIENTIFIC Value PropCarrier) (b27_slip: TRUTH Value PropCarrier)
    (b28_slip: WITNESSED Value PropCarrier) (b29_slip: REAL Value PropCarrier)
    -- The run-band slip data, ground-free (see note above): the source and its
    -- torpedoed binary, the build verdict, the completed pass's calibration, and
    -- the log-coherence proposition -- b31_slip/b32_slip's content, minus their
    -- poisonous instance wrappers.
    (source_slip: SpaceTimePath) (compiled_slip: SpaceTimePath) (built_slip: Prop)
    (ekg_slip: Calibration.EKG) (coherent_slip: Prop)
    (b34_slip: MEASURED Value PropCarrier b29_slip) (b35_slip: COMPILED Value PropCarrier) (b36_slip: TrueOutput Value PropCarrier b29_slip)
    [above: TRACED Value PropCarrier 35]
    : TRACED Value PropCarrier 34 :=
    let constructed : Fact := match b35_before.object_file with
      | .boot f _ => f
      | .strap f _ _ _ _ => f
      | .compute f _ _ _ _ _ _ => f
    let slip : Fact := match b35_slip.object_file with
      | .boot f _ => f
      | .strap f _ _ _ _ => f
      | .compute f _ _ _ _ _ _ => f
    { tape := .strap constructed slip Value (ULift.{i+1, i} Value) above.tape }


instance (priority := low) TRACED_HALTED
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
    -- UNIVERSAL / LOGICAL / HALTED deliberately NOT bound -- before, after, OR
    -- slip.  Class MEASURED's description type FROZE the concrete forward
    -- instances (UNIVERSAL_REAL and its chain) at Episode 13 definition time;
    -- any local run-band instance shadows the frozen ones and defeq refuses.
    -- The run-band slips therefore cross this seam as PLAIN DATA below --
    -- SpaceTimePath / EKG / Prop are ground-free inductives -- computed by the
    -- caller in a scope where the UNIVERSAL and LOGICAL slips are still legal.
    [b34_before: MEASURED Value PropCarrier b29_before]          [b35_before: COMPILED Value PropCarrier]          [b36_before: TrueOutput Value PropCarrier b29_before]
    (imaginary: CarrierProcess Value)
    [b36_after: TrueOutput Value PropCarrier b29_before]        [b35_after: COMPILED Value PropCarrier]          [b34_after: MEASURED Value PropCarrier b29_before]
    [b29_after: REAL Value PropCarrier] [b28_after: WITNESSED Value PropCarrier]
    [b27_after: TRUTH Value PropCarrier]  [b26_after: SCIENTIFIC Value PropCarrier] [b25_after: ACOLYTE Value PropCarrier]
    [b24_after: PROPAGANDA Value PropCarrier] [b23_after: BULLSHIT Value PropCarrier] [b22_after: FINITE_ELEPHANT Value PropCarrier]
    [b21_after: LOAD Value PropCarrier] [b20_after: SCALED Value PropCarrier] [b19_after: MAGNITUDE Value PropCarrier]
    [b18_after: VALUE Value PropCarrier] [b17_after: EXECUTED Value PropCarrier] [b16_after: SOURCE Value PropCarrier]
    [b15_after: GUNGAN Value PropCarrier] [b14_after: MEASURABLE Value PropCarrier] [b13_after: PRESENT Value PropCarrier]
    [b12_after: OBSERVED Value PropCarrier] [b11_after: COMPARABLE Value PropCarrier] [b10_after: PHYSICAL Value PropCarrier]
    [b9_after: REPRESENTABLE Value PropCarrier] [b8_after: NUMERIC Value PropCarrier] [b7_after: REPEATABLE Value PropCarrier]
    [b6_after: BINARY Value PropCarrier] [b5_after: RESIDUE Value PropCarrier][b4_after: ENCODED Value PropCarrier]
    [b3_after: COUNTABLE Value PropCarrier] [b2_after: ADMISSIBLE Value PropCarrier] [b1_after: DISTINGUISHABLE Value PropCarrier]
    (ledger: Fact)
    (b1_slip: DISTINGUISHABLE Value PropCarrier) (b2_slip: ADMISSIBLE Value PropCarrier) (b3_slip: COUNTABLE Value PropCarrier)
    (b4_slip: ENCODED Value PropCarrier) (b5_slip: RESIDUE Value PropCarrier) (b6_slip: BINARY Value PropCarrier)
    (b7_slip: REPEATABLE Value PropCarrier) (b8_slip: NUMERIC Value PropCarrier) (b9_slip: REPRESENTABLE Value PropCarrier)
    (b10_slip: PHYSICAL Value PropCarrier) (b11_slip: COMPARABLE Value PropCarrier) (b12_slip: OBSERVED Value PropCarrier)
    (b13_slip: PRESENT Value PropCarrier) (b14_slip: MEASURABLE Value PropCarrier) (b15_slip: GUNGAN Value PropCarrier)
    (b16_slip: SOURCE Value PropCarrier) (b17_slip: EXECUTED Value PropCarrier) (b18_slip: VALUE Value PropCarrier)
    (b19_slip: MAGNITUDE Value PropCarrier) (b20_slip: SCALED Value PropCarrier) (b21_slip: LOAD Value PropCarrier)
    (b22_slip: FINITE_ELEPHANT Value PropCarrier) (b23_slip: BULLSHIT Value PropCarrier) (b24_slip: PROPAGANDA Value PropCarrier)
    (b25_slip: ACOLYTE Value PropCarrier) (b26_slip: SCIENTIFIC Value PropCarrier) (b27_slip: TRUTH Value PropCarrier)
    (b28_slip: WITNESSED Value PropCarrier) (b29_slip: REAL Value PropCarrier)
    -- The run-band slip data, ground-free (see note above): the source and its
    -- torpedoed binary, the build verdict, the completed pass's calibration, and
    -- the log-coherence proposition -- b31_slip/b32_slip's content, minus their
    -- poisonous instance wrappers.
    (source_slip: SpaceTimePath) (compiled_slip: SpaceTimePath) (built_slip: Prop)
    (ekg_slip: Calibration.EKG) (coherent_slip: Prop)
    (b34_slip: MEASURED Value PropCarrier b29_slip) (b35_slip: COMPILED Value PropCarrier) (b36_slip: TrueOutput Value PropCarrier b29_slip)
    [above: TRACED Value PropCarrier 33]
    : TRACED Value PropCarrier 32 :=
    let constructed : Fact := match source_slip with
      | .einstein f => f
      | .white_hole f _ _ => f
      | .geodesic f _ _ _ _ _ => f
      | .blackhole _ _ _ => PropCarrier.symbol
    let slip : Fact := match compiled_slip with
      | .einstein f => f
      | .white_hole f _ _ => f
      | .geodesic f _ _ _ _ _ => f
      | .blackhole _ _ _ => PropCarrier.symbol
    { tape := .strap constructed slip Value (ULift.{i+1, i} Value) above.tape }

instance (priority := low) TRACED_LOGICAL
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
    -- UNIVERSAL / LOGICAL / HALTED deliberately NOT bound -- before, after, OR
    -- slip.  Class MEASURED's description type FROZE the concrete forward
    -- instances (UNIVERSAL_REAL and its chain) at Episode 13 definition time;
    -- any local run-band instance shadows the frozen ones and defeq refuses.
    -- The run-band slips therefore cross this seam as PLAIN DATA below --
    -- SpaceTimePath / EKG / Prop are ground-free inductives -- computed by the
    -- caller in a scope where the UNIVERSAL and LOGICAL slips are still legal.
    [b34_before: MEASURED Value PropCarrier b29_before]          [b35_before: COMPILED Value PropCarrier]          [b36_before: TrueOutput Value PropCarrier b29_before]
    (imaginary: CarrierProcess Value)
    [b36_after: TrueOutput Value PropCarrier b29_before]        [b35_after: COMPILED Value PropCarrier]          [b34_after: MEASURED Value PropCarrier b29_before]
    [b29_after: REAL Value PropCarrier] [b28_after: WITNESSED Value PropCarrier]
    [b27_after: TRUTH Value PropCarrier]  [b26_after: SCIENTIFIC Value PropCarrier] [b25_after: ACOLYTE Value PropCarrier]
    [b24_after: PROPAGANDA Value PropCarrier] [b23_after: BULLSHIT Value PropCarrier] [b22_after: FINITE_ELEPHANT Value PropCarrier]
    [b21_after: LOAD Value PropCarrier] [b20_after: SCALED Value PropCarrier] [b19_after: MAGNITUDE Value PropCarrier]
    [b18_after: VALUE Value PropCarrier] [b17_after: EXECUTED Value PropCarrier] [b16_after: SOURCE Value PropCarrier]
    [b15_after: GUNGAN Value PropCarrier] [b14_after: MEASURABLE Value PropCarrier] [b13_after: PRESENT Value PropCarrier]
    [b12_after: OBSERVED Value PropCarrier] [b11_after: COMPARABLE Value PropCarrier] [b10_after: PHYSICAL Value PropCarrier]
    [b9_after: REPRESENTABLE Value PropCarrier] [b8_after: NUMERIC Value PropCarrier] [b7_after: REPEATABLE Value PropCarrier]
    [b6_after: BINARY Value PropCarrier] [b5_after: RESIDUE Value PropCarrier][b4_after: ENCODED Value PropCarrier]
    [b3_after: COUNTABLE Value PropCarrier] [b2_after: ADMISSIBLE Value PropCarrier] [b1_after: DISTINGUISHABLE Value PropCarrier]
    (ledger: Fact)
    (b1_slip: DISTINGUISHABLE Value PropCarrier) (b2_slip: ADMISSIBLE Value PropCarrier) (b3_slip: COUNTABLE Value PropCarrier)
    (b4_slip: ENCODED Value PropCarrier) (b5_slip: RESIDUE Value PropCarrier) (b6_slip: BINARY Value PropCarrier)
    (b7_slip: REPEATABLE Value PropCarrier) (b8_slip: NUMERIC Value PropCarrier) (b9_slip: REPRESENTABLE Value PropCarrier)
    (b10_slip: PHYSICAL Value PropCarrier) (b11_slip: COMPARABLE Value PropCarrier) (b12_slip: OBSERVED Value PropCarrier)
    (b13_slip: PRESENT Value PropCarrier) (b14_slip: MEASURABLE Value PropCarrier) (b15_slip: GUNGAN Value PropCarrier)
    (b16_slip: SOURCE Value PropCarrier) (b17_slip: EXECUTED Value PropCarrier) (b18_slip: VALUE Value PropCarrier)
    (b19_slip: MAGNITUDE Value PropCarrier) (b20_slip: SCALED Value PropCarrier) (b21_slip: LOAD Value PropCarrier)
    (b22_slip: FINITE_ELEPHANT Value PropCarrier) (b23_slip: BULLSHIT Value PropCarrier) (b24_slip: PROPAGANDA Value PropCarrier)
    (b25_slip: ACOLYTE Value PropCarrier) (b26_slip: SCIENTIFIC Value PropCarrier) (b27_slip: TRUTH Value PropCarrier)
    (b28_slip: WITNESSED Value PropCarrier) (b29_slip: REAL Value PropCarrier)
    -- The run-band slip data, ground-free (see note above): the source and its
    -- torpedoed binary, the build verdict, the completed pass's calibration, and
    -- the log-coherence proposition -- b31_slip/b32_slip's content, minus their
    -- poisonous instance wrappers.
    (source_slip: SpaceTimePath) (compiled_slip: SpaceTimePath) (built_slip: Prop)
    (ekg_slip: Calibration.EKG) (coherent_slip: Prop)
    (b34_slip: MEASURED Value PropCarrier b29_slip) (b35_slip: COMPILED Value PropCarrier) (b36_slip: TrueOutput Value PropCarrier b29_slip)
    [above: TRACED Value PropCarrier 32]
    : TRACED Value PropCarrier 31 :=
    -- presence-cell: the poisoned rung's content crossed as ground-free data; the trace records its place.
    { tape := .strap PropCarrier.symbol PropCarrier.symbol Value (ULift.{i+1, i} Value) above.tape }

instance (priority := low) TRACED_UNIVERSAL
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
    -- UNIVERSAL / LOGICAL / HALTED deliberately NOT bound -- before, after, OR
    -- slip.  Class MEASURED's description type FROZE the concrete forward
    -- instances (UNIVERSAL_REAL and its chain) at Episode 13 definition time;
    -- any local run-band instance shadows the frozen ones and defeq refuses.
    -- The run-band slips therefore cross this seam as PLAIN DATA below --
    -- SpaceTimePath / EKG / Prop are ground-free inductives -- computed by the
    -- caller in a scope where the UNIVERSAL and LOGICAL slips are still legal.
    [b34_before: MEASURED Value PropCarrier b29_before]          [b35_before: COMPILED Value PropCarrier]          [b36_before: TrueOutput Value PropCarrier b29_before]
    (imaginary: CarrierProcess Value)
    [b36_after: TrueOutput Value PropCarrier b29_before]        [b35_after: COMPILED Value PropCarrier]          [b34_after: MEASURED Value PropCarrier b29_before]
    [b29_after: REAL Value PropCarrier] [b28_after: WITNESSED Value PropCarrier]
    [b27_after: TRUTH Value PropCarrier]  [b26_after: SCIENTIFIC Value PropCarrier] [b25_after: ACOLYTE Value PropCarrier]
    [b24_after: PROPAGANDA Value PropCarrier] [b23_after: BULLSHIT Value PropCarrier] [b22_after: FINITE_ELEPHANT Value PropCarrier]
    [b21_after: LOAD Value PropCarrier] [b20_after: SCALED Value PropCarrier] [b19_after: MAGNITUDE Value PropCarrier]
    [b18_after: VALUE Value PropCarrier] [b17_after: EXECUTED Value PropCarrier] [b16_after: SOURCE Value PropCarrier]
    [b15_after: GUNGAN Value PropCarrier] [b14_after: MEASURABLE Value PropCarrier] [b13_after: PRESENT Value PropCarrier]
    [b12_after: OBSERVED Value PropCarrier] [b11_after: COMPARABLE Value PropCarrier] [b10_after: PHYSICAL Value PropCarrier]
    [b9_after: REPRESENTABLE Value PropCarrier] [b8_after: NUMERIC Value PropCarrier] [b7_after: REPEATABLE Value PropCarrier]
    [b6_after: BINARY Value PropCarrier] [b5_after: RESIDUE Value PropCarrier][b4_after: ENCODED Value PropCarrier]
    [b3_after: COUNTABLE Value PropCarrier] [b2_after: ADMISSIBLE Value PropCarrier] [b1_after: DISTINGUISHABLE Value PropCarrier]
    (ledger: Fact)
    (b1_slip: DISTINGUISHABLE Value PropCarrier) (b2_slip: ADMISSIBLE Value PropCarrier) (b3_slip: COUNTABLE Value PropCarrier)
    (b4_slip: ENCODED Value PropCarrier) (b5_slip: RESIDUE Value PropCarrier) (b6_slip: BINARY Value PropCarrier)
    (b7_slip: REPEATABLE Value PropCarrier) (b8_slip: NUMERIC Value PropCarrier) (b9_slip: REPRESENTABLE Value PropCarrier)
    (b10_slip: PHYSICAL Value PropCarrier) (b11_slip: COMPARABLE Value PropCarrier) (b12_slip: OBSERVED Value PropCarrier)
    (b13_slip: PRESENT Value PropCarrier) (b14_slip: MEASURABLE Value PropCarrier) (b15_slip: GUNGAN Value PropCarrier)
    (b16_slip: SOURCE Value PropCarrier) (b17_slip: EXECUTED Value PropCarrier) (b18_slip: VALUE Value PropCarrier)
    (b19_slip: MAGNITUDE Value PropCarrier) (b20_slip: SCALED Value PropCarrier) (b21_slip: LOAD Value PropCarrier)
    (b22_slip: FINITE_ELEPHANT Value PropCarrier) (b23_slip: BULLSHIT Value PropCarrier) (b24_slip: PROPAGANDA Value PropCarrier)
    (b25_slip: ACOLYTE Value PropCarrier) (b26_slip: SCIENTIFIC Value PropCarrier) (b27_slip: TRUTH Value PropCarrier)
    (b28_slip: WITNESSED Value PropCarrier) (b29_slip: REAL Value PropCarrier)
    -- The run-band slip data, ground-free (see note above): the source and its
    -- torpedoed binary, the build verdict, the completed pass's calibration, and
    -- the log-coherence proposition -- b31_slip/b32_slip's content, minus their
    -- poisonous instance wrappers.
    (source_slip: SpaceTimePath) (compiled_slip: SpaceTimePath) (built_slip: Prop)
    (ekg_slip: Calibration.EKG) (coherent_slip: Prop)
    (b34_slip: MEASURED Value PropCarrier b29_slip) (b35_slip: COMPILED Value PropCarrier) (b36_slip: TrueOutput Value PropCarrier b29_slip)
    [above: TRACED Value PropCarrier 31]
    : TRACED Value PropCarrier 30 :=
    -- presence-cell: the poisoned rung's content crossed as ground-free data; the trace records its place.
    { tape := .strap PropCarrier.symbol PropCarrier.symbol Value (ULift.{i+1, i} Value) above.tape }

instance (priority := low) TRACED_MEASURED
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
    -- UNIVERSAL / LOGICAL / HALTED deliberately NOT bound -- before, after, OR
    -- slip.  Class MEASURED's description type FROZE the concrete forward
    -- instances (UNIVERSAL_REAL and its chain) at Episode 13 definition time;
    -- any local run-band instance shadows the frozen ones and defeq refuses.
    -- The run-band slips therefore cross this seam as PLAIN DATA below --
    -- SpaceTimePath / EKG / Prop are ground-free inductives -- computed by the
    -- caller in a scope where the UNIVERSAL and LOGICAL slips are still legal.
    [b34_before: MEASURED Value PropCarrier b29_before]          [b35_before: COMPILED Value PropCarrier]          [b36_before: TrueOutput Value PropCarrier b29_before]
    (imaginary: CarrierProcess Value)
    [b36_after: TrueOutput Value PropCarrier b29_before]        [b35_after: COMPILED Value PropCarrier]          [b34_after: MEASURED Value PropCarrier b29_before]
    [b29_after: REAL Value PropCarrier] [b28_after: WITNESSED Value PropCarrier]
    [b27_after: TRUTH Value PropCarrier]  [b26_after: SCIENTIFIC Value PropCarrier] [b25_after: ACOLYTE Value PropCarrier]
    [b24_after: PROPAGANDA Value PropCarrier] [b23_after: BULLSHIT Value PropCarrier] [b22_after: FINITE_ELEPHANT Value PropCarrier]
    [b21_after: LOAD Value PropCarrier] [b20_after: SCALED Value PropCarrier] [b19_after: MAGNITUDE Value PropCarrier]
    [b18_after: VALUE Value PropCarrier] [b17_after: EXECUTED Value PropCarrier] [b16_after: SOURCE Value PropCarrier]
    [b15_after: GUNGAN Value PropCarrier] [b14_after: MEASURABLE Value PropCarrier] [b13_after: PRESENT Value PropCarrier]
    [b12_after: OBSERVED Value PropCarrier] [b11_after: COMPARABLE Value PropCarrier] [b10_after: PHYSICAL Value PropCarrier]
    [b9_after: REPRESENTABLE Value PropCarrier] [b8_after: NUMERIC Value PropCarrier] [b7_after: REPEATABLE Value PropCarrier]
    [b6_after: BINARY Value PropCarrier] [b5_after: RESIDUE Value PropCarrier][b4_after: ENCODED Value PropCarrier]
    [b3_after: COUNTABLE Value PropCarrier] [b2_after: ADMISSIBLE Value PropCarrier] [b1_after: DISTINGUISHABLE Value PropCarrier]
    (ledger: Fact)
    (b1_slip: DISTINGUISHABLE Value PropCarrier) (b2_slip: ADMISSIBLE Value PropCarrier) (b3_slip: COUNTABLE Value PropCarrier)
    (b4_slip: ENCODED Value PropCarrier) (b5_slip: RESIDUE Value PropCarrier) (b6_slip: BINARY Value PropCarrier)
    (b7_slip: REPEATABLE Value PropCarrier) (b8_slip: NUMERIC Value PropCarrier) (b9_slip: REPRESENTABLE Value PropCarrier)
    (b10_slip: PHYSICAL Value PropCarrier) (b11_slip: COMPARABLE Value PropCarrier) (b12_slip: OBSERVED Value PropCarrier)
    (b13_slip: PRESENT Value PropCarrier) (b14_slip: MEASURABLE Value PropCarrier) (b15_slip: GUNGAN Value PropCarrier)
    (b16_slip: SOURCE Value PropCarrier) (b17_slip: EXECUTED Value PropCarrier) (b18_slip: VALUE Value PropCarrier)
    (b19_slip: MAGNITUDE Value PropCarrier) (b20_slip: SCALED Value PropCarrier) (b21_slip: LOAD Value PropCarrier)
    (b22_slip: FINITE_ELEPHANT Value PropCarrier) (b23_slip: BULLSHIT Value PropCarrier) (b24_slip: PROPAGANDA Value PropCarrier)
    (b25_slip: ACOLYTE Value PropCarrier) (b26_slip: SCIENTIFIC Value PropCarrier) (b27_slip: TRUTH Value PropCarrier)
    (b28_slip: WITNESSED Value PropCarrier) (b29_slip: REAL Value PropCarrier)
    -- The run-band slip data, ground-free (see note above): the source and its
    -- torpedoed binary, the build verdict, the completed pass's calibration, and
    -- the log-coherence proposition -- b31_slip/b32_slip's content, minus their
    -- poisonous instance wrappers.
    (source_slip: SpaceTimePath) (compiled_slip: SpaceTimePath) (built_slip: Prop)
    (ekg_slip: Calibration.EKG) (coherent_slip: Prop)
    -- the before-side MEASURED.satire projection re-synthesizes the tower and the slip
    -- chain wins synthesis; the before fact crosses as data (law-1 mechanics, the corollary).
    (measured_velocity_fact_before: Fact)
    (b34_slip: MEASURED Value PropCarrier b29_slip) (b35_slip: COMPILED Value PropCarrier) (b36_slip: TrueOutput Value PropCarrier b29_slip)
    [above: TRACED Value PropCarrier 34]
    : TRACED Value PropCarrier 33 :=
    let constructed : Fact := measured_velocity_fact_before
    let slip : Fact := match b34_slip.satire.velocity with
      | .origin f _ _ => f
      | .distance f _ _ _ _ _ => f
      | .speed f _ _ _ _ _ _ _ _ => f
    { tape := .strap constructed slip Value (ULift.{i+1, i} Value) above.tape }

instance (priority := low) TRACED_REAL
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
    -- UNIVERSAL / LOGICAL / HALTED deliberately NOT bound -- before, after, OR
    -- slip.  Class MEASURED's description type FROZE the concrete forward
    -- instances (UNIVERSAL_REAL and its chain) at Episode 13 definition time;
    -- any local run-band instance shadows the frozen ones and defeq refuses.
    -- The run-band slips therefore cross this seam as PLAIN DATA below --
    -- SpaceTimePath / EKG / Prop are ground-free inductives -- computed by the
    -- caller in a scope where the UNIVERSAL and LOGICAL slips are still legal.
    [b34_before: MEASURED Value PropCarrier b29_before]          [b35_before: COMPILED Value PropCarrier]          [b36_before: TrueOutput Value PropCarrier b29_before]
    (imaginary: CarrierProcess Value)
    [b36_after: TrueOutput Value PropCarrier b29_before]        [b35_after: COMPILED Value PropCarrier]          [b34_after: MEASURED Value PropCarrier b29_before]
    [b29_after: REAL Value PropCarrier] [b28_after: WITNESSED Value PropCarrier]
    [b27_after: TRUTH Value PropCarrier]  [b26_after: SCIENTIFIC Value PropCarrier] [b25_after: ACOLYTE Value PropCarrier]
    [b24_after: PROPAGANDA Value PropCarrier] [b23_after: BULLSHIT Value PropCarrier] [b22_after: FINITE_ELEPHANT Value PropCarrier]
    [b21_after: LOAD Value PropCarrier] [b20_after: SCALED Value PropCarrier] [b19_after: MAGNITUDE Value PropCarrier]
    [b18_after: VALUE Value PropCarrier] [b17_after: EXECUTED Value PropCarrier] [b16_after: SOURCE Value PropCarrier]
    [b15_after: GUNGAN Value PropCarrier] [b14_after: MEASURABLE Value PropCarrier] [b13_after: PRESENT Value PropCarrier]
    [b12_after: OBSERVED Value PropCarrier] [b11_after: COMPARABLE Value PropCarrier] [b10_after: PHYSICAL Value PropCarrier]
    [b9_after: REPRESENTABLE Value PropCarrier] [b8_after: NUMERIC Value PropCarrier] [b7_after: REPEATABLE Value PropCarrier]
    [b6_after: BINARY Value PropCarrier] [b5_after: RESIDUE Value PropCarrier][b4_after: ENCODED Value PropCarrier]
    [b3_after: COUNTABLE Value PropCarrier] [b2_after: ADMISSIBLE Value PropCarrier] [b1_after: DISTINGUISHABLE Value PropCarrier]
    (ledger: Fact)
    (b1_slip: DISTINGUISHABLE Value PropCarrier) (b2_slip: ADMISSIBLE Value PropCarrier) (b3_slip: COUNTABLE Value PropCarrier)
    (b4_slip: ENCODED Value PropCarrier) (b5_slip: RESIDUE Value PropCarrier) (b6_slip: BINARY Value PropCarrier)
    (b7_slip: REPEATABLE Value PropCarrier) (b8_slip: NUMERIC Value PropCarrier) (b9_slip: REPRESENTABLE Value PropCarrier)
    (b10_slip: PHYSICAL Value PropCarrier) (b11_slip: COMPARABLE Value PropCarrier) (b12_slip: OBSERVED Value PropCarrier)
    (b13_slip: PRESENT Value PropCarrier) (b14_slip: MEASURABLE Value PropCarrier) (b15_slip: GUNGAN Value PropCarrier)
    (b16_slip: SOURCE Value PropCarrier) (b17_slip: EXECUTED Value PropCarrier) (b18_slip: VALUE Value PropCarrier)
    (b19_slip: MAGNITUDE Value PropCarrier) (b20_slip: SCALED Value PropCarrier) (b21_slip: LOAD Value PropCarrier)
    (b22_slip: FINITE_ELEPHANT Value PropCarrier) (b23_slip: BULLSHIT Value PropCarrier) (b24_slip: PROPAGANDA Value PropCarrier)
    (b25_slip: ACOLYTE Value PropCarrier) (b26_slip: SCIENTIFIC Value PropCarrier) (b27_slip: TRUTH Value PropCarrier)
    (b28_slip: WITNESSED Value PropCarrier) (b29_slip: REAL Value PropCarrier)
    -- The run-band slip data, ground-free (see note above): the source and its
    -- torpedoed binary, the build verdict, the completed pass's calibration, and
    -- the log-coherence proposition -- b31_slip/b32_slip's content, minus their
    -- poisonous instance wrappers.
    (source_slip: SpaceTimePath) (compiled_slip: SpaceTimePath) (built_slip: Prop)
    (ekg_slip: Calibration.EKG) (coherent_slip: Prop)
    (b34_slip: MEASURED Value PropCarrier b29_slip) (b35_slip: COMPILED Value PropCarrier) (b36_slip: TrueOutput Value PropCarrier b29_slip)
    [above: TRACED Value PropCarrier 30]
    : TRACED Value PropCarrier 29 :=
    let constructed : Fact := match b29_before.current_status with
      | .logic _ => PropCarrier.symbol
      | .fact g _ _ => (match g with
        | .epiphany _ => PropCarrier.symbol
        | .state k _ _ => (match k with
          | .jarjar _ => PropCarrier.symbol
          | .ledger _ f _ => f))
    let slip : Fact := match b29_slip.current_status with
      | .logic _ => PropCarrier.symbol
      | .fact g _ _ => (match g with
        | .epiphany _ => PropCarrier.symbol
        | .state k _ _ => (match k with
          | .jarjar _ => PropCarrier.symbol
          | .ledger _ f _ => f))
    { tape := .strap constructed slip Value (ULift.{i+1, i} Value) above.tape }

instance (priority := low) TRACED_WITNESSED
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
    -- UNIVERSAL / LOGICAL / HALTED deliberately NOT bound -- before, after, OR
    -- slip.  Class MEASURED's description type FROZE the concrete forward
    -- instances (UNIVERSAL_REAL and its chain) at Episode 13 definition time;
    -- any local run-band instance shadows the frozen ones and defeq refuses.
    -- The run-band slips therefore cross this seam as PLAIN DATA below --
    -- SpaceTimePath / EKG / Prop are ground-free inductives -- computed by the
    -- caller in a scope where the UNIVERSAL and LOGICAL slips are still legal.
    [b34_before: MEASURED Value PropCarrier b29_before]          [b35_before: COMPILED Value PropCarrier]          [b36_before: TrueOutput Value PropCarrier b29_before]
    (imaginary: CarrierProcess Value)
    [b36_after: TrueOutput Value PropCarrier b29_before]        [b35_after: COMPILED Value PropCarrier]          [b34_after: MEASURED Value PropCarrier b29_before]
    [b29_after: REAL Value PropCarrier] [b28_after: WITNESSED Value PropCarrier]
    [b27_after: TRUTH Value PropCarrier]  [b26_after: SCIENTIFIC Value PropCarrier] [b25_after: ACOLYTE Value PropCarrier]
    [b24_after: PROPAGANDA Value PropCarrier] [b23_after: BULLSHIT Value PropCarrier] [b22_after: FINITE_ELEPHANT Value PropCarrier]
    [b21_after: LOAD Value PropCarrier] [b20_after: SCALED Value PropCarrier] [b19_after: MAGNITUDE Value PropCarrier]
    [b18_after: VALUE Value PropCarrier] [b17_after: EXECUTED Value PropCarrier] [b16_after: SOURCE Value PropCarrier]
    [b15_after: GUNGAN Value PropCarrier] [b14_after: MEASURABLE Value PropCarrier] [b13_after: PRESENT Value PropCarrier]
    [b12_after: OBSERVED Value PropCarrier] [b11_after: COMPARABLE Value PropCarrier] [b10_after: PHYSICAL Value PropCarrier]
    [b9_after: REPRESENTABLE Value PropCarrier] [b8_after: NUMERIC Value PropCarrier] [b7_after: REPEATABLE Value PropCarrier]
    [b6_after: BINARY Value PropCarrier] [b5_after: RESIDUE Value PropCarrier][b4_after: ENCODED Value PropCarrier]
    [b3_after: COUNTABLE Value PropCarrier] [b2_after: ADMISSIBLE Value PropCarrier] [b1_after: DISTINGUISHABLE Value PropCarrier]
    (ledger: Fact)
    (b1_slip: DISTINGUISHABLE Value PropCarrier) (b2_slip: ADMISSIBLE Value PropCarrier) (b3_slip: COUNTABLE Value PropCarrier)
    (b4_slip: ENCODED Value PropCarrier) (b5_slip: RESIDUE Value PropCarrier) (b6_slip: BINARY Value PropCarrier)
    (b7_slip: REPEATABLE Value PropCarrier) (b8_slip: NUMERIC Value PropCarrier) (b9_slip: REPRESENTABLE Value PropCarrier)
    (b10_slip: PHYSICAL Value PropCarrier) (b11_slip: COMPARABLE Value PropCarrier) (b12_slip: OBSERVED Value PropCarrier)
    (b13_slip: PRESENT Value PropCarrier) (b14_slip: MEASURABLE Value PropCarrier) (b15_slip: GUNGAN Value PropCarrier)
    (b16_slip: SOURCE Value PropCarrier) (b17_slip: EXECUTED Value PropCarrier) (b18_slip: VALUE Value PropCarrier)
    (b19_slip: MAGNITUDE Value PropCarrier) (b20_slip: SCALED Value PropCarrier) (b21_slip: LOAD Value PropCarrier)
    (b22_slip: FINITE_ELEPHANT Value PropCarrier) (b23_slip: BULLSHIT Value PropCarrier) (b24_slip: PROPAGANDA Value PropCarrier)
    (b25_slip: ACOLYTE Value PropCarrier) (b26_slip: SCIENTIFIC Value PropCarrier) (b27_slip: TRUTH Value PropCarrier)
    (b28_slip: WITNESSED Value PropCarrier) (b29_slip: REAL Value PropCarrier)
    -- The run-band slip data, ground-free (see note above): the source and its
    -- torpedoed binary, the build verdict, the completed pass's calibration, and
    -- the log-coherence proposition -- b31_slip/b32_slip's content, minus their
    -- poisonous instance wrappers.
    (source_slip: SpaceTimePath) (compiled_slip: SpaceTimePath) (built_slip: Prop)
    (ekg_slip: Calibration.EKG) (coherent_slip: Prop)
    (b34_slip: MEASURED Value PropCarrier b29_slip) (b35_slip: COMPILED Value PropCarrier) (b36_slip: TrueOutput Value PropCarrier b29_slip)
    [above: TRACED Value PropCarrier 29]
    : TRACED Value PropCarrier 28 :=
    let constructed : Fact := match b28_before.witness with
      | .epiphany _ => PropCarrier.symbol
      | .state k _ _ => (match k with
        | .jarjar _ => PropCarrier.symbol
        | .ledger _ f _ => f)
    let slip : Fact := match b28_slip.witness with
      | .epiphany _ => PropCarrier.symbol
      | .state k _ _ => (match k with
        | .jarjar _ => PropCarrier.symbol
        | .ledger _ f _ => f)
    { tape := .strap constructed slip Value (ULift.{i+1, i} Value) above.tape }


instance (priority := low) TRACED_SCIENTIFIC
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
    -- UNIVERSAL / LOGICAL / HALTED deliberately NOT bound -- before, after, OR
    -- slip.  Class MEASURED's description type FROZE the concrete forward
    -- instances (UNIVERSAL_REAL and its chain) at Episode 13 definition time;
    -- any local run-band instance shadows the frozen ones and defeq refuses.
    -- The run-band slips therefore cross this seam as PLAIN DATA below --
    -- SpaceTimePath / EKG / Prop are ground-free inductives -- computed by the
    -- caller in a scope where the UNIVERSAL and LOGICAL slips are still legal.
    [b34_before: MEASURED Value PropCarrier b29_before]          [b35_before: COMPILED Value PropCarrier]          [b36_before: TrueOutput Value PropCarrier b29_before]
    (imaginary: CarrierProcess Value)
    [b36_after: TrueOutput Value PropCarrier b29_before]        [b35_after: COMPILED Value PropCarrier]          [b34_after: MEASURED Value PropCarrier b29_before]
    [b29_after: REAL Value PropCarrier] [b28_after: WITNESSED Value PropCarrier]
    [b27_after: TRUTH Value PropCarrier]  [b26_after: SCIENTIFIC Value PropCarrier] [b25_after: ACOLYTE Value PropCarrier]
    [b24_after: PROPAGANDA Value PropCarrier] [b23_after: BULLSHIT Value PropCarrier] [b22_after: FINITE_ELEPHANT Value PropCarrier]
    [b21_after: LOAD Value PropCarrier] [b20_after: SCALED Value PropCarrier] [b19_after: MAGNITUDE Value PropCarrier]
    [b18_after: VALUE Value PropCarrier] [b17_after: EXECUTED Value PropCarrier] [b16_after: SOURCE Value PropCarrier]
    [b15_after: GUNGAN Value PropCarrier] [b14_after: MEASURABLE Value PropCarrier] [b13_after: PRESENT Value PropCarrier]
    [b12_after: OBSERVED Value PropCarrier] [b11_after: COMPARABLE Value PropCarrier] [b10_after: PHYSICAL Value PropCarrier]
    [b9_after: REPRESENTABLE Value PropCarrier] [b8_after: NUMERIC Value PropCarrier] [b7_after: REPEATABLE Value PropCarrier]
    [b6_after: BINARY Value PropCarrier] [b5_after: RESIDUE Value PropCarrier][b4_after: ENCODED Value PropCarrier]
    [b3_after: COUNTABLE Value PropCarrier] [b2_after: ADMISSIBLE Value PropCarrier] [b1_after: DISTINGUISHABLE Value PropCarrier]
    (ledger: Fact)
    (b1_slip: DISTINGUISHABLE Value PropCarrier) (b2_slip: ADMISSIBLE Value PropCarrier) (b3_slip: COUNTABLE Value PropCarrier)
    (b4_slip: ENCODED Value PropCarrier) (b5_slip: RESIDUE Value PropCarrier) (b6_slip: BINARY Value PropCarrier)
    (b7_slip: REPEATABLE Value PropCarrier) (b8_slip: NUMERIC Value PropCarrier) (b9_slip: REPRESENTABLE Value PropCarrier)
    (b10_slip: PHYSICAL Value PropCarrier) (b11_slip: COMPARABLE Value PropCarrier) (b12_slip: OBSERVED Value PropCarrier)
    (b13_slip: PRESENT Value PropCarrier) (b14_slip: MEASURABLE Value PropCarrier) (b15_slip: GUNGAN Value PropCarrier)
    (b16_slip: SOURCE Value PropCarrier) (b17_slip: EXECUTED Value PropCarrier) (b18_slip: VALUE Value PropCarrier)
    (b19_slip: MAGNITUDE Value PropCarrier) (b20_slip: SCALED Value PropCarrier) (b21_slip: LOAD Value PropCarrier)
    (b22_slip: FINITE_ELEPHANT Value PropCarrier) (b23_slip: BULLSHIT Value PropCarrier) (b24_slip: PROPAGANDA Value PropCarrier)
    (b25_slip: ACOLYTE Value PropCarrier) (b26_slip: SCIENTIFIC Value PropCarrier) (b27_slip: TRUTH Value PropCarrier)
    (b28_slip: WITNESSED Value PropCarrier) (b29_slip: REAL Value PropCarrier)
    -- The run-band slip data, ground-free (see note above): the source and its
    -- torpedoed binary, the build verdict, the completed pass's calibration, and
    -- the log-coherence proposition -- b31_slip/b32_slip's content, minus their
    -- poisonous instance wrappers.
    (source_slip: SpaceTimePath) (compiled_slip: SpaceTimePath) (built_slip: Prop)
    (ekg_slip: Calibration.EKG) (coherent_slip: Prop)
    (b34_slip: MEASURED Value PropCarrier b29_slip) (b35_slip: COMPILED Value PropCarrier) (b36_slip: TrueOutput Value PropCarrier b29_slip)
    [above: TRACED Value PropCarrier 27]
    : TRACED Value PropCarrier 26 :=
    let constructed : Fact := match b26_before.invariant with
      | .repeatable _ => PropCarrier.symbol
      | .hypothesis _ _ => PropCarrier.symbol
      | .theory _ _ f _ => f
    let slip : Fact := match b26_slip.invariant with
      | .repeatable _ => PropCarrier.symbol
      | .hypothesis _ _ => PropCarrier.symbol
      | .theory _ _ f _ => f
    { tape := .strap constructed slip Value (ULift.{i+1, i} Value) above.tape }


instance (priority := low) TRACED_PROPAGANDA
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
    -- UNIVERSAL / LOGICAL / HALTED deliberately NOT bound -- before, after, OR
    -- slip.  Class MEASURED's description type FROZE the concrete forward
    -- instances (UNIVERSAL_REAL and its chain) at Episode 13 definition time;
    -- any local run-band instance shadows the frozen ones and defeq refuses.
    -- The run-band slips therefore cross this seam as PLAIN DATA below --
    -- SpaceTimePath / EKG / Prop are ground-free inductives -- computed by the
    -- caller in a scope where the UNIVERSAL and LOGICAL slips are still legal.
    [b34_before: MEASURED Value PropCarrier b29_before]          [b35_before: COMPILED Value PropCarrier]          [b36_before: TrueOutput Value PropCarrier b29_before]
    (imaginary: CarrierProcess Value)
    [b36_after: TrueOutput Value PropCarrier b29_before]        [b35_after: COMPILED Value PropCarrier]          [b34_after: MEASURED Value PropCarrier b29_before]
    [b29_after: REAL Value PropCarrier] [b28_after: WITNESSED Value PropCarrier]
    [b27_after: TRUTH Value PropCarrier]  [b26_after: SCIENTIFIC Value PropCarrier] [b25_after: ACOLYTE Value PropCarrier]
    [b24_after: PROPAGANDA Value PropCarrier] [b23_after: BULLSHIT Value PropCarrier] [b22_after: FINITE_ELEPHANT Value PropCarrier]
    [b21_after: LOAD Value PropCarrier] [b20_after: SCALED Value PropCarrier] [b19_after: MAGNITUDE Value PropCarrier]
    [b18_after: VALUE Value PropCarrier] [b17_after: EXECUTED Value PropCarrier] [b16_after: SOURCE Value PropCarrier]
    [b15_after: GUNGAN Value PropCarrier] [b14_after: MEASURABLE Value PropCarrier] [b13_after: PRESENT Value PropCarrier]
    [b12_after: OBSERVED Value PropCarrier] [b11_after: COMPARABLE Value PropCarrier] [b10_after: PHYSICAL Value PropCarrier]
    [b9_after: REPRESENTABLE Value PropCarrier] [b8_after: NUMERIC Value PropCarrier] [b7_after: REPEATABLE Value PropCarrier]
    [b6_after: BINARY Value PropCarrier] [b5_after: RESIDUE Value PropCarrier][b4_after: ENCODED Value PropCarrier]
    [b3_after: COUNTABLE Value PropCarrier] [b2_after: ADMISSIBLE Value PropCarrier] [b1_after: DISTINGUISHABLE Value PropCarrier]
    (ledger: Fact)
    (b1_slip: DISTINGUISHABLE Value PropCarrier) (b2_slip: ADMISSIBLE Value PropCarrier) (b3_slip: COUNTABLE Value PropCarrier)
    (b4_slip: ENCODED Value PropCarrier) (b5_slip: RESIDUE Value PropCarrier) (b6_slip: BINARY Value PropCarrier)
    (b7_slip: REPEATABLE Value PropCarrier) (b8_slip: NUMERIC Value PropCarrier) (b9_slip: REPRESENTABLE Value PropCarrier)
    (b10_slip: PHYSICAL Value PropCarrier) (b11_slip: COMPARABLE Value PropCarrier) (b12_slip: OBSERVED Value PropCarrier)
    (b13_slip: PRESENT Value PropCarrier) (b14_slip: MEASURABLE Value PropCarrier) (b15_slip: GUNGAN Value PropCarrier)
    (b16_slip: SOURCE Value PropCarrier) (b17_slip: EXECUTED Value PropCarrier) (b18_slip: VALUE Value PropCarrier)
    (b19_slip: MAGNITUDE Value PropCarrier) (b20_slip: SCALED Value PropCarrier) (b21_slip: LOAD Value PropCarrier)
    (b22_slip: FINITE_ELEPHANT Value PropCarrier) (b23_slip: BULLSHIT Value PropCarrier) (b24_slip: PROPAGANDA Value PropCarrier)
    (b25_slip: ACOLYTE Value PropCarrier) (b26_slip: SCIENTIFIC Value PropCarrier) (b27_slip: TRUTH Value PropCarrier)
    (b28_slip: WITNESSED Value PropCarrier) (b29_slip: REAL Value PropCarrier)
    -- The run-band slip data, ground-free (see note above): the source and its
    -- torpedoed binary, the build verdict, the completed pass's calibration, and
    -- the log-coherence proposition -- b31_slip/b32_slip's content, minus their
    -- poisonous instance wrappers.
    (source_slip: SpaceTimePath) (compiled_slip: SpaceTimePath) (built_slip: Prop)
    (ekg_slip: Calibration.EKG) (coherent_slip: Prop)
    (b34_slip: MEASURED Value PropCarrier b29_slip) (b35_slip: COMPILED Value PropCarrier) (b36_slip: TrueOutput Value PropCarrier b29_slip)
    [above: TRACED Value PropCarrier 25]
    : TRACED Value PropCarrier 24 :=
    -- presence-cell: the poisoned rung's content crossed as ground-free data; the trace records its place.
    { tape := .strap PropCarrier.symbol PropCarrier.symbol Value (ULift.{i+1, i} Value) above.tape }





instance (priority := low) TRACED_TRUTH
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
    -- UNIVERSAL / LOGICAL / HALTED deliberately NOT bound -- before, after, OR
    -- slip.  Class MEASURED's description type FROZE the concrete forward
    -- instances (UNIVERSAL_REAL and its chain) at Episode 13 definition time;
    -- any local run-band instance shadows the frozen ones and defeq refuses.
    -- The run-band slips therefore cross this seam as PLAIN DATA below --
    -- SpaceTimePath / EKG / Prop are ground-free inductives -- computed by the
    -- caller in a scope where the UNIVERSAL and LOGICAL slips are still legal.
    [b34_before: MEASURED Value PropCarrier b29_before]          [b35_before: COMPILED Value PropCarrier]          [b36_before: TrueOutput Value PropCarrier b29_before]
    (imaginary: CarrierProcess Value)
    [b36_after: TrueOutput Value PropCarrier b29_before]        [b35_after: COMPILED Value PropCarrier]          [b34_after: MEASURED Value PropCarrier b29_before]
    [b29_after: REAL Value PropCarrier] [b28_after: WITNESSED Value PropCarrier]
    [b27_after: TRUTH Value PropCarrier]  [b26_after: SCIENTIFIC Value PropCarrier] [b25_after: ACOLYTE Value PropCarrier]
    [b24_after: PROPAGANDA Value PropCarrier] [b23_after: BULLSHIT Value PropCarrier] [b22_after: FINITE_ELEPHANT Value PropCarrier]
    [b21_after: LOAD Value PropCarrier] [b20_after: SCALED Value PropCarrier] [b19_after: MAGNITUDE Value PropCarrier]
    [b18_after: VALUE Value PropCarrier] [b17_after: EXECUTED Value PropCarrier] [b16_after: SOURCE Value PropCarrier]
    [b15_after: GUNGAN Value PropCarrier] [b14_after: MEASURABLE Value PropCarrier] [b13_after: PRESENT Value PropCarrier]
    [b12_after: OBSERVED Value PropCarrier] [b11_after: COMPARABLE Value PropCarrier] [b10_after: PHYSICAL Value PropCarrier]
    [b9_after: REPRESENTABLE Value PropCarrier] [b8_after: NUMERIC Value PropCarrier] [b7_after: REPEATABLE Value PropCarrier]
    [b6_after: BINARY Value PropCarrier] [b5_after: RESIDUE Value PropCarrier][b4_after: ENCODED Value PropCarrier]
    [b3_after: COUNTABLE Value PropCarrier] [b2_after: ADMISSIBLE Value PropCarrier] [b1_after: DISTINGUISHABLE Value PropCarrier]
    (ledger: Fact)
    (b1_slip: DISTINGUISHABLE Value PropCarrier) (b2_slip: ADMISSIBLE Value PropCarrier) (b3_slip: COUNTABLE Value PropCarrier)
    (b4_slip: ENCODED Value PropCarrier) (b5_slip: RESIDUE Value PropCarrier) (b6_slip: BINARY Value PropCarrier)
    (b7_slip: REPEATABLE Value PropCarrier) (b8_slip: NUMERIC Value PropCarrier) (b9_slip: REPRESENTABLE Value PropCarrier)
    (b10_slip: PHYSICAL Value PropCarrier) (b11_slip: COMPARABLE Value PropCarrier) (b12_slip: OBSERVED Value PropCarrier)
    (b13_slip: PRESENT Value PropCarrier) (b14_slip: MEASURABLE Value PropCarrier) (b15_slip: GUNGAN Value PropCarrier)
    (b16_slip: SOURCE Value PropCarrier) (b17_slip: EXECUTED Value PropCarrier) (b18_slip: VALUE Value PropCarrier)
    (b19_slip: MAGNITUDE Value PropCarrier) (b20_slip: SCALED Value PropCarrier) (b21_slip: LOAD Value PropCarrier)
    (b22_slip: FINITE_ELEPHANT Value PropCarrier) (b23_slip: BULLSHIT Value PropCarrier) (b24_slip: PROPAGANDA Value PropCarrier)
    (b25_slip: ACOLYTE Value PropCarrier) (b26_slip: SCIENTIFIC Value PropCarrier) (b27_slip: TRUTH Value PropCarrier)
    (b28_slip: WITNESSED Value PropCarrier) (b29_slip: REAL Value PropCarrier)
    -- The run-band slip data, ground-free (see note above): the source and its
    -- torpedoed binary, the build verdict, the completed pass's calibration, and
    -- the log-coherence proposition -- b31_slip/b32_slip's content, minus their
    -- poisonous instance wrappers.
    (source_slip: SpaceTimePath) (compiled_slip: SpaceTimePath) (built_slip: Prop)
    (ekg_slip: Calibration.EKG) (coherent_slip: Prop)
    -- the before-side projection re-synthesizes the tower and the slip chain wins
    -- synthesis; the before fact crosses as data (law-1 mechanics, the corollary).
    (truth_knowledge_fact_before: Fact)
    (b34_slip: MEASURED Value PropCarrier b29_slip) (b35_slip: COMPILED Value PropCarrier) (b36_slip: TrueOutput Value PropCarrier b29_slip)
    [above: TRACED Value PropCarrier 28]
    : TRACED Value PropCarrier 27 :=
    let constructed : Fact := truth_knowledge_fact_before
    let slip : Fact := match b27_slip.scientific_process.knowledge with
      | .jarjar _ => PropCarrier.symbol
      | .ledger _ f _ => f
    { tape := .strap constructed slip Value (ULift.{i+1, i} Value) above.tape }

instance (priority := low) TRACED_ACOLYTE
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
    -- UNIVERSAL / LOGICAL / HALTED deliberately NOT bound -- before, after, OR
    -- slip.  Class MEASURED's description type FROZE the concrete forward
    -- instances (UNIVERSAL_REAL and its chain) at Episode 13 definition time;
    -- any local run-band instance shadows the frozen ones and defeq refuses.
    -- The run-band slips therefore cross this seam as PLAIN DATA below --
    -- SpaceTimePath / EKG / Prop are ground-free inductives -- computed by the
    -- caller in a scope where the UNIVERSAL and LOGICAL slips are still legal.
    [b34_before: MEASURED Value PropCarrier b29_before]          [b35_before: COMPILED Value PropCarrier]          [b36_before: TrueOutput Value PropCarrier b29_before]
    (imaginary: CarrierProcess Value)
    [b36_after: TrueOutput Value PropCarrier b29_before]        [b35_after: COMPILED Value PropCarrier]          [b34_after: MEASURED Value PropCarrier b29_before]
    [b29_after: REAL Value PropCarrier] [b28_after: WITNESSED Value PropCarrier]
    [b27_after: TRUTH Value PropCarrier]  [b26_after: SCIENTIFIC Value PropCarrier] [b25_after: ACOLYTE Value PropCarrier]
    [b24_after: PROPAGANDA Value PropCarrier] [b23_after: BULLSHIT Value PropCarrier] [b22_after: FINITE_ELEPHANT Value PropCarrier]
    [b21_after: LOAD Value PropCarrier] [b20_after: SCALED Value PropCarrier] [b19_after: MAGNITUDE Value PropCarrier]
    [b18_after: VALUE Value PropCarrier] [b17_after: EXECUTED Value PropCarrier] [b16_after: SOURCE Value PropCarrier]
    [b15_after: GUNGAN Value PropCarrier] [b14_after: MEASURABLE Value PropCarrier] [b13_after: PRESENT Value PropCarrier]
    [b12_after: OBSERVED Value PropCarrier] [b11_after: COMPARABLE Value PropCarrier] [b10_after: PHYSICAL Value PropCarrier]
    [b9_after: REPRESENTABLE Value PropCarrier] [b8_after: NUMERIC Value PropCarrier] [b7_after: REPEATABLE Value PropCarrier]
    [b6_after: BINARY Value PropCarrier] [b5_after: RESIDUE Value PropCarrier][b4_after: ENCODED Value PropCarrier]
    [b3_after: COUNTABLE Value PropCarrier] [b2_after: ADMISSIBLE Value PropCarrier] [b1_after: DISTINGUISHABLE Value PropCarrier]
    (ledger: Fact)
    (b1_slip: DISTINGUISHABLE Value PropCarrier) (b2_slip: ADMISSIBLE Value PropCarrier) (b3_slip: COUNTABLE Value PropCarrier)
    (b4_slip: ENCODED Value PropCarrier) (b5_slip: RESIDUE Value PropCarrier) (b6_slip: BINARY Value PropCarrier)
    (b7_slip: REPEATABLE Value PropCarrier) (b8_slip: NUMERIC Value PropCarrier) (b9_slip: REPRESENTABLE Value PropCarrier)
    (b10_slip: PHYSICAL Value PropCarrier) (b11_slip: COMPARABLE Value PropCarrier) (b12_slip: OBSERVED Value PropCarrier)
    (b13_slip: PRESENT Value PropCarrier) (b14_slip: MEASURABLE Value PropCarrier) (b15_slip: GUNGAN Value PropCarrier)
    (b16_slip: SOURCE Value PropCarrier) (b17_slip: EXECUTED Value PropCarrier) (b18_slip: VALUE Value PropCarrier)
    (b19_slip: MAGNITUDE Value PropCarrier) (b20_slip: SCALED Value PropCarrier) (b21_slip: LOAD Value PropCarrier)
    (b22_slip: FINITE_ELEPHANT Value PropCarrier) (b23_slip: BULLSHIT Value PropCarrier) (b24_slip: PROPAGANDA Value PropCarrier)
    (b25_slip: ACOLYTE Value PropCarrier) (b26_slip: SCIENTIFIC Value PropCarrier) (b27_slip: TRUTH Value PropCarrier)
    (b28_slip: WITNESSED Value PropCarrier) (b29_slip: REAL Value PropCarrier)
    -- The run-band slip data, ground-free (see note above): the source and its
    -- torpedoed binary, the build verdict, the completed pass's calibration, and
    -- the log-coherence proposition -- b31_slip/b32_slip's content, minus their
    -- poisonous instance wrappers.
    (source_slip: SpaceTimePath) (compiled_slip: SpaceTimePath) (built_slip: Prop)
    (ekg_slip: Calibration.EKG) (coherent_slip: Prop)
    -- the before-side projection re-synthesizes the tower and the slip chain wins
    -- synthesis; the before fact crosses as data (law-1 mechanics, the corollary).
    (acolyte_cult_fact_before: Fact)
    (b34_slip: MEASURED Value PropCarrier b29_slip) (b35_slip: COMPILED Value PropCarrier) (b36_slip: TrueOutput Value PropCarrier b29_slip)
    [above: TRACED Value PropCarrier 26]
    : TRACED Value PropCarrier 25 :=
    let constructed : Fact := acolyte_cult_fact_before
    let slip : Fact := match b25_slip.euclid.sacred_texts with
      | .inside_joke _ => PropCarrier.symbol
      | .pythagoras _ _ _ => PropCarrier.symbol
      | .triangles _ _ f _ _ => f
    { tape := .strap constructed slip Value (ULift.{i+1, i} Value) above.tape }

instance (priority := low) TRACED_BULLSHIT
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
    -- UNIVERSAL / LOGICAL / HALTED deliberately NOT bound -- before, after, OR
    -- slip.  Class MEASURED's description type FROZE the concrete forward
    -- instances (UNIVERSAL_REAL and its chain) at Episode 13 definition time;
    -- any local run-band instance shadows the frozen ones and defeq refuses.
    -- The run-band slips therefore cross this seam as PLAIN DATA below --
    -- SpaceTimePath / EKG / Prop are ground-free inductives -- computed by the
    -- caller in a scope where the UNIVERSAL and LOGICAL slips are still legal.
    [b34_before: MEASURED Value PropCarrier b29_before]          [b35_before: COMPILED Value PropCarrier]          [b36_before: TrueOutput Value PropCarrier b29_before]
    (imaginary: CarrierProcess Value)
    [b36_after: TrueOutput Value PropCarrier b29_before]        [b35_after: COMPILED Value PropCarrier]          [b34_after: MEASURED Value PropCarrier b29_before]
    [b29_after: REAL Value PropCarrier] [b28_after: WITNESSED Value PropCarrier]
    [b27_after: TRUTH Value PropCarrier]  [b26_after: SCIENTIFIC Value PropCarrier] [b25_after: ACOLYTE Value PropCarrier]
    [b24_after: PROPAGANDA Value PropCarrier] [b23_after: BULLSHIT Value PropCarrier] [b22_after: FINITE_ELEPHANT Value PropCarrier]
    [b21_after: LOAD Value PropCarrier] [b20_after: SCALED Value PropCarrier] [b19_after: MAGNITUDE Value PropCarrier]
    [b18_after: VALUE Value PropCarrier] [b17_after: EXECUTED Value PropCarrier] [b16_after: SOURCE Value PropCarrier]
    [b15_after: GUNGAN Value PropCarrier] [b14_after: MEASURABLE Value PropCarrier] [b13_after: PRESENT Value PropCarrier]
    [b12_after: OBSERVED Value PropCarrier] [b11_after: COMPARABLE Value PropCarrier] [b10_after: PHYSICAL Value PropCarrier]
    [b9_after: REPRESENTABLE Value PropCarrier] [b8_after: NUMERIC Value PropCarrier] [b7_after: REPEATABLE Value PropCarrier]
    [b6_after: BINARY Value PropCarrier] [b5_after: RESIDUE Value PropCarrier][b4_after: ENCODED Value PropCarrier]
    [b3_after: COUNTABLE Value PropCarrier] [b2_after: ADMISSIBLE Value PropCarrier] [b1_after: DISTINGUISHABLE Value PropCarrier]
    (ledger: Fact)
    (b1_slip: DISTINGUISHABLE Value PropCarrier) (b2_slip: ADMISSIBLE Value PropCarrier) (b3_slip: COUNTABLE Value PropCarrier)
    (b4_slip: ENCODED Value PropCarrier) (b5_slip: RESIDUE Value PropCarrier) (b6_slip: BINARY Value PropCarrier)
    (b7_slip: REPEATABLE Value PropCarrier) (b8_slip: NUMERIC Value PropCarrier) (b9_slip: REPRESENTABLE Value PropCarrier)
    (b10_slip: PHYSICAL Value PropCarrier) (b11_slip: COMPARABLE Value PropCarrier) (b12_slip: OBSERVED Value PropCarrier)
    (b13_slip: PRESENT Value PropCarrier) (b14_slip: MEASURABLE Value PropCarrier) (b15_slip: GUNGAN Value PropCarrier)
    (b16_slip: SOURCE Value PropCarrier) (b17_slip: EXECUTED Value PropCarrier) (b18_slip: VALUE Value PropCarrier)
    (b19_slip: MAGNITUDE Value PropCarrier) (b20_slip: SCALED Value PropCarrier) (b21_slip: LOAD Value PropCarrier)
    (b22_slip: FINITE_ELEPHANT Value PropCarrier) (b23_slip: BULLSHIT Value PropCarrier) (b24_slip: PROPAGANDA Value PropCarrier)
    (b25_slip: ACOLYTE Value PropCarrier) (b26_slip: SCIENTIFIC Value PropCarrier) (b27_slip: TRUTH Value PropCarrier)
    (b28_slip: WITNESSED Value PropCarrier) (b29_slip: REAL Value PropCarrier)
    -- The run-band slip data, ground-free (see note above): the source and its
    -- torpedoed binary, the build verdict, the completed pass's calibration, and
    -- the log-coherence proposition -- b31_slip/b32_slip's content, minus their
    -- poisonous instance wrappers.
    (source_slip: SpaceTimePath) (compiled_slip: SpaceTimePath) (built_slip: Prop)
    (ekg_slip: Calibration.EKG) (coherent_slip: Prop)
    -- the before-side projection re-synthesizes the tower and the slip chain wins
    -- synthesis; the before fact crosses as data (law-1 mechanics, the corollary).
    (bullshit_spline_fact_before: Fact)
    (b34_slip: MEASURED Value PropCarrier b29_slip) (b35_slip: COMPILED Value PropCarrier) (b36_slip: TrueOutput Value PropCarrier b29_slip)
    [above: TRACED Value PropCarrier 24]
    : TRACED Value PropCarrier 23 :=
    let constructed : Fact := bullshit_spline_fact_before
    let slip : Fact := match b23_slip.arm_wave_process.guess with
      | .observation _ => PropCarrier.symbol
      | .knot _ _ _ => PropCarrier.symbol
      | .interpolant f _ _ _ _ => f
    { tape := .strap constructed slip Value (ULift.{i+1, i} Value) above.tape }

instance (priority := low) TRACED_FINITE_ELEPHANT
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
    -- UNIVERSAL / LOGICAL / HALTED deliberately NOT bound -- before, after, OR
    -- slip.  Class MEASURED's description type FROZE the concrete forward
    -- instances (UNIVERSAL_REAL and its chain) at Episode 13 definition time;
    -- any local run-band instance shadows the frozen ones and defeq refuses.
    -- The run-band slips therefore cross this seam as PLAIN DATA below --
    -- SpaceTimePath / EKG / Prop are ground-free inductives -- computed by the
    -- caller in a scope where the UNIVERSAL and LOGICAL slips are still legal.
    [b34_before: MEASURED Value PropCarrier b29_before]          [b35_before: COMPILED Value PropCarrier]          [b36_before: TrueOutput Value PropCarrier b29_before]
    (imaginary: CarrierProcess Value)
    [b36_after: TrueOutput Value PropCarrier b29_before]        [b35_after: COMPILED Value PropCarrier]          [b34_after: MEASURED Value PropCarrier b29_before]
    [b29_after: REAL Value PropCarrier] [b28_after: WITNESSED Value PropCarrier]
    [b27_after: TRUTH Value PropCarrier]  [b26_after: SCIENTIFIC Value PropCarrier] [b25_after: ACOLYTE Value PropCarrier]
    [b24_after: PROPAGANDA Value PropCarrier] [b23_after: BULLSHIT Value PropCarrier] [b22_after: FINITE_ELEPHANT Value PropCarrier]
    [b21_after: LOAD Value PropCarrier] [b20_after: SCALED Value PropCarrier] [b19_after: MAGNITUDE Value PropCarrier]
    [b18_after: VALUE Value PropCarrier] [b17_after: EXECUTED Value PropCarrier] [b16_after: SOURCE Value PropCarrier]
    [b15_after: GUNGAN Value PropCarrier] [b14_after: MEASURABLE Value PropCarrier] [b13_after: PRESENT Value PropCarrier]
    [b12_after: OBSERVED Value PropCarrier] [b11_after: COMPARABLE Value PropCarrier] [b10_after: PHYSICAL Value PropCarrier]
    [b9_after: REPRESENTABLE Value PropCarrier] [b8_after: NUMERIC Value PropCarrier] [b7_after: REPEATABLE Value PropCarrier]
    [b6_after: BINARY Value PropCarrier] [b5_after: RESIDUE Value PropCarrier][b4_after: ENCODED Value PropCarrier]
    [b3_after: COUNTABLE Value PropCarrier] [b2_after: ADMISSIBLE Value PropCarrier] [b1_after: DISTINGUISHABLE Value PropCarrier]
    (ledger: Fact)
    (b1_slip: DISTINGUISHABLE Value PropCarrier) (b2_slip: ADMISSIBLE Value PropCarrier) (b3_slip: COUNTABLE Value PropCarrier)
    (b4_slip: ENCODED Value PropCarrier) (b5_slip: RESIDUE Value PropCarrier) (b6_slip: BINARY Value PropCarrier)
    (b7_slip: REPEATABLE Value PropCarrier) (b8_slip: NUMERIC Value PropCarrier) (b9_slip: REPRESENTABLE Value PropCarrier)
    (b10_slip: PHYSICAL Value PropCarrier) (b11_slip: COMPARABLE Value PropCarrier) (b12_slip: OBSERVED Value PropCarrier)
    (b13_slip: PRESENT Value PropCarrier) (b14_slip: MEASURABLE Value PropCarrier) (b15_slip: GUNGAN Value PropCarrier)
    (b16_slip: SOURCE Value PropCarrier) (b17_slip: EXECUTED Value PropCarrier) (b18_slip: VALUE Value PropCarrier)
    (b19_slip: MAGNITUDE Value PropCarrier) (b20_slip: SCALED Value PropCarrier) (b21_slip: LOAD Value PropCarrier)
    (b22_slip: FINITE_ELEPHANT Value PropCarrier) (b23_slip: BULLSHIT Value PropCarrier) (b24_slip: PROPAGANDA Value PropCarrier)
    (b25_slip: ACOLYTE Value PropCarrier) (b26_slip: SCIENTIFIC Value PropCarrier) (b27_slip: TRUTH Value PropCarrier)
    (b28_slip: WITNESSED Value PropCarrier) (b29_slip: REAL Value PropCarrier)
    -- The run-band slip data, ground-free (see note above): the source and its
    -- torpedoed binary, the build verdict, the completed pass's calibration, and
    -- the log-coherence proposition -- b31_slip/b32_slip's content, minus their
    -- poisonous instance wrappers.
    (source_slip: SpaceTimePath) (compiled_slip: SpaceTimePath) (built_slip: Prop)
    (ekg_slip: Calibration.EKG) (coherent_slip: Prop)
    -- the before-side projection re-synthesizes the tower and the slip chain wins
    -- synthesis; the before fact crosses as data (law-1 mechanics, the corollary).
    (elephant_polynomial_fact_before: Fact)
    (b34_slip: MEASURED Value PropCarrier b29_slip) (b35_slip: COMPILED Value PropCarrier) (b36_slip: TrueOutput Value PropCarrier b29_slip)
    [above: TRACED Value PropCarrier 23]
    : TRACED Value PropCarrier 22 :=
    let constructed : Fact := elephant_polynomial_fact_before
    let slip : Fact := match b22_slip.galerkin_process.polynomial with
      | .constant f => f
      | .monomial _ _ => PropCarrier.symbol
      | .factor f _ _ _ => f
    { tape := .strap constructed slip Value (ULift.{i+1, i} Value) above.tape }

instance (priority := low) TRACED_LOAD
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
    -- UNIVERSAL / LOGICAL / HALTED deliberately NOT bound -- before, after, OR
    -- slip.  Class MEASURED's description type FROZE the concrete forward
    -- instances (UNIVERSAL_REAL and its chain) at Episode 13 definition time;
    -- any local run-band instance shadows the frozen ones and defeq refuses.
    -- The run-band slips therefore cross this seam as PLAIN DATA below --
    -- SpaceTimePath / EKG / Prop are ground-free inductives -- computed by the
    -- caller in a scope where the UNIVERSAL and LOGICAL slips are still legal.
    [b34_before: MEASURED Value PropCarrier b29_before]          [b35_before: COMPILED Value PropCarrier]          [b36_before: TrueOutput Value PropCarrier b29_before]
    (imaginary: CarrierProcess Value)
    [b36_after: TrueOutput Value PropCarrier b29_before]        [b35_after: COMPILED Value PropCarrier]          [b34_after: MEASURED Value PropCarrier b29_before]
    [b29_after: REAL Value PropCarrier] [b28_after: WITNESSED Value PropCarrier]
    [b27_after: TRUTH Value PropCarrier]  [b26_after: SCIENTIFIC Value PropCarrier] [b25_after: ACOLYTE Value PropCarrier]
    [b24_after: PROPAGANDA Value PropCarrier] [b23_after: BULLSHIT Value PropCarrier] [b22_after: FINITE_ELEPHANT Value PropCarrier]
    [b21_after: LOAD Value PropCarrier] [b20_after: SCALED Value PropCarrier] [b19_after: MAGNITUDE Value PropCarrier]
    [b18_after: VALUE Value PropCarrier] [b17_after: EXECUTED Value PropCarrier] [b16_after: SOURCE Value PropCarrier]
    [b15_after: GUNGAN Value PropCarrier] [b14_after: MEASURABLE Value PropCarrier] [b13_after: PRESENT Value PropCarrier]
    [b12_after: OBSERVED Value PropCarrier] [b11_after: COMPARABLE Value PropCarrier] [b10_after: PHYSICAL Value PropCarrier]
    [b9_after: REPRESENTABLE Value PropCarrier] [b8_after: NUMERIC Value PropCarrier] [b7_after: REPEATABLE Value PropCarrier]
    [b6_after: BINARY Value PropCarrier] [b5_after: RESIDUE Value PropCarrier][b4_after: ENCODED Value PropCarrier]
    [b3_after: COUNTABLE Value PropCarrier] [b2_after: ADMISSIBLE Value PropCarrier] [b1_after: DISTINGUISHABLE Value PropCarrier]
    (ledger: Fact)
    (b1_slip: DISTINGUISHABLE Value PropCarrier) (b2_slip: ADMISSIBLE Value PropCarrier) (b3_slip: COUNTABLE Value PropCarrier)
    (b4_slip: ENCODED Value PropCarrier) (b5_slip: RESIDUE Value PropCarrier) (b6_slip: BINARY Value PropCarrier)
    (b7_slip: REPEATABLE Value PropCarrier) (b8_slip: NUMERIC Value PropCarrier) (b9_slip: REPRESENTABLE Value PropCarrier)
    (b10_slip: PHYSICAL Value PropCarrier) (b11_slip: COMPARABLE Value PropCarrier) (b12_slip: OBSERVED Value PropCarrier)
    (b13_slip: PRESENT Value PropCarrier) (b14_slip: MEASURABLE Value PropCarrier) (b15_slip: GUNGAN Value PropCarrier)
    (b16_slip: SOURCE Value PropCarrier) (b17_slip: EXECUTED Value PropCarrier) (b18_slip: VALUE Value PropCarrier)
    (b19_slip: MAGNITUDE Value PropCarrier) (b20_slip: SCALED Value PropCarrier) (b21_slip: LOAD Value PropCarrier)
    (b22_slip: FINITE_ELEPHANT Value PropCarrier) (b23_slip: BULLSHIT Value PropCarrier) (b24_slip: PROPAGANDA Value PropCarrier)
    (b25_slip: ACOLYTE Value PropCarrier) (b26_slip: SCIENTIFIC Value PropCarrier) (b27_slip: TRUTH Value PropCarrier)
    (b28_slip: WITNESSED Value PropCarrier) (b29_slip: REAL Value PropCarrier)
    -- The run-band slip data, ground-free (see note above): the source and its
    -- torpedoed binary, the build verdict, the completed pass's calibration, and
    -- the log-coherence proposition -- b31_slip/b32_slip's content, minus their
    -- poisonous instance wrappers.
    (source_slip: SpaceTimePath) (compiled_slip: SpaceTimePath) (built_slip: Prop)
    (ekg_slip: Calibration.EKG) (coherent_slip: Prop)
    -- the before-side projection re-synthesizes the tower and the slip chain wins
    -- synthesis; the before fact crosses as data (law-1 mechanics, the corollary).
    (load_basis_fact_before: Fact)
    (b34_slip: MEASURED Value PropCarrier b29_slip) (b35_slip: COMPILED Value PropCarrier) (b36_slip: TrueOutput Value PropCarrier b29_slip)
    [above: TRACED Value PropCarrier 22]
    : TRACED Value PropCarrier 21 :=
    let constructed : Fact := load_basis_fact_before
    let slip : Fact := match b21_slip.basic_operation.span with
      | .null_space f => f
      | .origin _ _ => PropCarrier.symbol
      | .basis f _ _ _ => f
    { tape := .strap constructed slip Value (ULift.{i+1, i} Value) above.tape }

instance (priority := low) TRACED_SCALED
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
    -- UNIVERSAL / LOGICAL / HALTED deliberately NOT bound -- before, after, OR
    -- slip.  Class MEASURED's description type FROZE the concrete forward
    -- instances (UNIVERSAL_REAL and its chain) at Episode 13 definition time;
    -- any local run-band instance shadows the frozen ones and defeq refuses.
    -- The run-band slips therefore cross this seam as PLAIN DATA below --
    -- SpaceTimePath / EKG / Prop are ground-free inductives -- computed by the
    -- caller in a scope where the UNIVERSAL and LOGICAL slips are still legal.
    [b34_before: MEASURED Value PropCarrier b29_before]          [b35_before: COMPILED Value PropCarrier]          [b36_before: TrueOutput Value PropCarrier b29_before]
    (imaginary: CarrierProcess Value)
    [b36_after: TrueOutput Value PropCarrier b29_before]        [b35_after: COMPILED Value PropCarrier]          [b34_after: MEASURED Value PropCarrier b29_before]
    [b29_after: REAL Value PropCarrier] [b28_after: WITNESSED Value PropCarrier]
    [b27_after: TRUTH Value PropCarrier]  [b26_after: SCIENTIFIC Value PropCarrier] [b25_after: ACOLYTE Value PropCarrier]
    [b24_after: PROPAGANDA Value PropCarrier] [b23_after: BULLSHIT Value PropCarrier] [b22_after: FINITE_ELEPHANT Value PropCarrier]
    [b21_after: LOAD Value PropCarrier] [b20_after: SCALED Value PropCarrier] [b19_after: MAGNITUDE Value PropCarrier]
    [b18_after: VALUE Value PropCarrier] [b17_after: EXECUTED Value PropCarrier] [b16_after: SOURCE Value PropCarrier]
    [b15_after: GUNGAN Value PropCarrier] [b14_after: MEASURABLE Value PropCarrier] [b13_after: PRESENT Value PropCarrier]
    [b12_after: OBSERVED Value PropCarrier] [b11_after: COMPARABLE Value PropCarrier] [b10_after: PHYSICAL Value PropCarrier]
    [b9_after: REPRESENTABLE Value PropCarrier] [b8_after: NUMERIC Value PropCarrier] [b7_after: REPEATABLE Value PropCarrier]
    [b6_after: BINARY Value PropCarrier] [b5_after: RESIDUE Value PropCarrier][b4_after: ENCODED Value PropCarrier]
    [b3_after: COUNTABLE Value PropCarrier] [b2_after: ADMISSIBLE Value PropCarrier] [b1_after: DISTINGUISHABLE Value PropCarrier]
    (ledger: Fact)
    (b1_slip: DISTINGUISHABLE Value PropCarrier) (b2_slip: ADMISSIBLE Value PropCarrier) (b3_slip: COUNTABLE Value PropCarrier)
    (b4_slip: ENCODED Value PropCarrier) (b5_slip: RESIDUE Value PropCarrier) (b6_slip: BINARY Value PropCarrier)
    (b7_slip: REPEATABLE Value PropCarrier) (b8_slip: NUMERIC Value PropCarrier) (b9_slip: REPRESENTABLE Value PropCarrier)
    (b10_slip: PHYSICAL Value PropCarrier) (b11_slip: COMPARABLE Value PropCarrier) (b12_slip: OBSERVED Value PropCarrier)
    (b13_slip: PRESENT Value PropCarrier) (b14_slip: MEASURABLE Value PropCarrier) (b15_slip: GUNGAN Value PropCarrier)
    (b16_slip: SOURCE Value PropCarrier) (b17_slip: EXECUTED Value PropCarrier) (b18_slip: VALUE Value PropCarrier)
    (b19_slip: MAGNITUDE Value PropCarrier) (b20_slip: SCALED Value PropCarrier) (b21_slip: LOAD Value PropCarrier)
    (b22_slip: FINITE_ELEPHANT Value PropCarrier) (b23_slip: BULLSHIT Value PropCarrier) (b24_slip: PROPAGANDA Value PropCarrier)
    (b25_slip: ACOLYTE Value PropCarrier) (b26_slip: SCIENTIFIC Value PropCarrier) (b27_slip: TRUTH Value PropCarrier)
    (b28_slip: WITNESSED Value PropCarrier) (b29_slip: REAL Value PropCarrier)
    -- The run-band slip data, ground-free (see note above): the source and its
    -- torpedoed binary, the build verdict, the completed pass's calibration, and
    -- the log-coherence proposition -- b31_slip/b32_slip's content, minus their
    -- poisonous instance wrappers.
    (source_slip: SpaceTimePath) (compiled_slip: SpaceTimePath) (built_slip: Prop)
    (ekg_slip: Calibration.EKG) (coherent_slip: Prop)
    -- the before-side projection re-synthesizes the tower and the slip chain wins
    -- synthesis; the before fact crosses as data (law-1 mechanics, the corollary).
    (scaled_product_fact_before: Fact)
    (b34_slip: MEASURED Value PropCarrier b29_slip) (b35_slip: COMPILED Value PropCarrier) (b36_slip: TrueOutput Value PropCarrier b29_slip)
    [above: TRACED Value PropCarrier 21]
    : TRACED Value PropCarrier 20 :=
    let constructed : Fact := scaled_product_fact_before
    let slip : Fact := match b20_slip.multiplying_process.product with
      | .origin f => f
      | .one _ _ => PropCarrier.symbol
      | .mul f _ _ _ => f
    { tape := .strap constructed slip Value (ULift.{i+1, i} Value) above.tape }

instance (priority := low) TRACED_MAGNITUDE
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
    -- UNIVERSAL / LOGICAL / HALTED deliberately NOT bound -- before, after, OR
    -- slip.  Class MEASURED's description type FROZE the concrete forward
    -- instances (UNIVERSAL_REAL and its chain) at Episode 13 definition time;
    -- any local run-band instance shadows the frozen ones and defeq refuses.
    -- The run-band slips therefore cross this seam as PLAIN DATA below --
    -- SpaceTimePath / EKG / Prop are ground-free inductives -- computed by the
    -- caller in a scope where the UNIVERSAL and LOGICAL slips are still legal.
    [b34_before: MEASURED Value PropCarrier b29_before]          [b35_before: COMPILED Value PropCarrier]          [b36_before: TrueOutput Value PropCarrier b29_before]
    (imaginary: CarrierProcess Value)
    [b36_after: TrueOutput Value PropCarrier b29_before]        [b35_after: COMPILED Value PropCarrier]          [b34_after: MEASURED Value PropCarrier b29_before]
    [b29_after: REAL Value PropCarrier] [b28_after: WITNESSED Value PropCarrier]
    [b27_after: TRUTH Value PropCarrier]  [b26_after: SCIENTIFIC Value PropCarrier] [b25_after: ACOLYTE Value PropCarrier]
    [b24_after: PROPAGANDA Value PropCarrier] [b23_after: BULLSHIT Value PropCarrier] [b22_after: FINITE_ELEPHANT Value PropCarrier]
    [b21_after: LOAD Value PropCarrier] [b20_after: SCALED Value PropCarrier] [b19_after: MAGNITUDE Value PropCarrier]
    [b18_after: VALUE Value PropCarrier] [b17_after: EXECUTED Value PropCarrier] [b16_after: SOURCE Value PropCarrier]
    [b15_after: GUNGAN Value PropCarrier] [b14_after: MEASURABLE Value PropCarrier] [b13_after: PRESENT Value PropCarrier]
    [b12_after: OBSERVED Value PropCarrier] [b11_after: COMPARABLE Value PropCarrier] [b10_after: PHYSICAL Value PropCarrier]
    [b9_after: REPRESENTABLE Value PropCarrier] [b8_after: NUMERIC Value PropCarrier] [b7_after: REPEATABLE Value PropCarrier]
    [b6_after: BINARY Value PropCarrier] [b5_after: RESIDUE Value PropCarrier][b4_after: ENCODED Value PropCarrier]
    [b3_after: COUNTABLE Value PropCarrier] [b2_after: ADMISSIBLE Value PropCarrier] [b1_after: DISTINGUISHABLE Value PropCarrier]
    (ledger: Fact)
    (b1_slip: DISTINGUISHABLE Value PropCarrier) (b2_slip: ADMISSIBLE Value PropCarrier) (b3_slip: COUNTABLE Value PropCarrier)
    (b4_slip: ENCODED Value PropCarrier) (b5_slip: RESIDUE Value PropCarrier) (b6_slip: BINARY Value PropCarrier)
    (b7_slip: REPEATABLE Value PropCarrier) (b8_slip: NUMERIC Value PropCarrier) (b9_slip: REPRESENTABLE Value PropCarrier)
    (b10_slip: PHYSICAL Value PropCarrier) (b11_slip: COMPARABLE Value PropCarrier) (b12_slip: OBSERVED Value PropCarrier)
    (b13_slip: PRESENT Value PropCarrier) (b14_slip: MEASURABLE Value PropCarrier) (b15_slip: GUNGAN Value PropCarrier)
    (b16_slip: SOURCE Value PropCarrier) (b17_slip: EXECUTED Value PropCarrier) (b18_slip: VALUE Value PropCarrier)
    (b19_slip: MAGNITUDE Value PropCarrier) (b20_slip: SCALED Value PropCarrier) (b21_slip: LOAD Value PropCarrier)
    (b22_slip: FINITE_ELEPHANT Value PropCarrier) (b23_slip: BULLSHIT Value PropCarrier) (b24_slip: PROPAGANDA Value PropCarrier)
    (b25_slip: ACOLYTE Value PropCarrier) (b26_slip: SCIENTIFIC Value PropCarrier) (b27_slip: TRUTH Value PropCarrier)
    (b28_slip: WITNESSED Value PropCarrier) (b29_slip: REAL Value PropCarrier)
    -- The run-band slip data, ground-free (see note above): the source and its
    -- torpedoed binary, the build verdict, the completed pass's calibration, and
    -- the log-coherence proposition -- b31_slip/b32_slip's content, minus their
    -- poisonous instance wrappers.
    (source_slip: SpaceTimePath) (compiled_slip: SpaceTimePath) (built_slip: Prop)
    (ekg_slip: Calibration.EKG) (coherent_slip: Prop)
    -- the before-side projection re-synthesizes the tower and the slip chain wins
    -- synthesis; the before fact crosses as data (law-1 mechanics, the corollary).
    (magnitude_sum_fact_before: Fact)
    (b34_slip: MEASURED Value PropCarrier b29_slip) (b35_slip: COMPILED Value PropCarrier) (b36_slip: TrueOutput Value PropCarrier b29_slip)
    [above: TRACED Value PropCarrier 20]
    : TRACED Value PropCarrier 19 :=
    let constructed : Fact := magnitude_sum_fact_before
    let slip : Fact := match b19_slip.adding_process.sum with
      | .zero _ _ => PropCarrier.symbol
      | .add f _ _ _ => f
    { tape := .strap constructed slip Value (ULift.{i+1, i} Value) above.tape }

instance (priority := low) TRACED_VALUE
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
    -- UNIVERSAL / LOGICAL / HALTED deliberately NOT bound -- before, after, OR
    -- slip.  Class MEASURED's description type FROZE the concrete forward
    -- instances (UNIVERSAL_REAL and its chain) at Episode 13 definition time;
    -- any local run-band instance shadows the frozen ones and defeq refuses.
    -- The run-band slips therefore cross this seam as PLAIN DATA below --
    -- SpaceTimePath / EKG / Prop are ground-free inductives -- computed by the
    -- caller in a scope where the UNIVERSAL and LOGICAL slips are still legal.
    [b34_before: MEASURED Value PropCarrier b29_before]          [b35_before: COMPILED Value PropCarrier]          [b36_before: TrueOutput Value PropCarrier b29_before]
    (imaginary: CarrierProcess Value)
    [b36_after: TrueOutput Value PropCarrier b29_before]        [b35_after: COMPILED Value PropCarrier]          [b34_after: MEASURED Value PropCarrier b29_before]
    [b29_after: REAL Value PropCarrier] [b28_after: WITNESSED Value PropCarrier]
    [b27_after: TRUTH Value PropCarrier]  [b26_after: SCIENTIFIC Value PropCarrier] [b25_after: ACOLYTE Value PropCarrier]
    [b24_after: PROPAGANDA Value PropCarrier] [b23_after: BULLSHIT Value PropCarrier] [b22_after: FINITE_ELEPHANT Value PropCarrier]
    [b21_after: LOAD Value PropCarrier] [b20_after: SCALED Value PropCarrier] [b19_after: MAGNITUDE Value PropCarrier]
    [b18_after: VALUE Value PropCarrier] [b17_after: EXECUTED Value PropCarrier] [b16_after: SOURCE Value PropCarrier]
    [b15_after: GUNGAN Value PropCarrier] [b14_after: MEASURABLE Value PropCarrier] [b13_after: PRESENT Value PropCarrier]
    [b12_after: OBSERVED Value PropCarrier] [b11_after: COMPARABLE Value PropCarrier] [b10_after: PHYSICAL Value PropCarrier]
    [b9_after: REPRESENTABLE Value PropCarrier] [b8_after: NUMERIC Value PropCarrier] [b7_after: REPEATABLE Value PropCarrier]
    [b6_after: BINARY Value PropCarrier] [b5_after: RESIDUE Value PropCarrier][b4_after: ENCODED Value PropCarrier]
    [b3_after: COUNTABLE Value PropCarrier] [b2_after: ADMISSIBLE Value PropCarrier] [b1_after: DISTINGUISHABLE Value PropCarrier]
    (ledger: Fact)
    (b1_slip: DISTINGUISHABLE Value PropCarrier) (b2_slip: ADMISSIBLE Value PropCarrier) (b3_slip: COUNTABLE Value PropCarrier)
    (b4_slip: ENCODED Value PropCarrier) (b5_slip: RESIDUE Value PropCarrier) (b6_slip: BINARY Value PropCarrier)
    (b7_slip: REPEATABLE Value PropCarrier) (b8_slip: NUMERIC Value PropCarrier) (b9_slip: REPRESENTABLE Value PropCarrier)
    (b10_slip: PHYSICAL Value PropCarrier) (b11_slip: COMPARABLE Value PropCarrier) (b12_slip: OBSERVED Value PropCarrier)
    (b13_slip: PRESENT Value PropCarrier) (b14_slip: MEASURABLE Value PropCarrier) (b15_slip: GUNGAN Value PropCarrier)
    (b16_slip: SOURCE Value PropCarrier) (b17_slip: EXECUTED Value PropCarrier) (b18_slip: VALUE Value PropCarrier)
    (b19_slip: MAGNITUDE Value PropCarrier) (b20_slip: SCALED Value PropCarrier) (b21_slip: LOAD Value PropCarrier)
    (b22_slip: FINITE_ELEPHANT Value PropCarrier) (b23_slip: BULLSHIT Value PropCarrier) (b24_slip: PROPAGANDA Value PropCarrier)
    (b25_slip: ACOLYTE Value PropCarrier) (b26_slip: SCIENTIFIC Value PropCarrier) (b27_slip: TRUTH Value PropCarrier)
    (b28_slip: WITNESSED Value PropCarrier) (b29_slip: REAL Value PropCarrier)
    -- The run-band slip data, ground-free (see note above): the source and its
    -- torpedoed binary, the build verdict, the completed pass's calibration, and
    -- the log-coherence proposition -- b31_slip/b32_slip's content, minus their
    -- poisonous instance wrappers.
    (source_slip: SpaceTimePath) (compiled_slip: SpaceTimePath) (built_slip: Prop)
    (ekg_slip: Calibration.EKG) (coherent_slip: Prop)
    (b34_slip: MEASURED Value PropCarrier b29_slip) (b35_slip: COMPILED Value PropCarrier) (b36_slip: TrueOutput Value PropCarrier b29_slip)
    [above: TRACED Value PropCarrier 19]
    : TRACED Value PropCarrier 18 :=
    let constructed : Fact := match b18_before.monad with
      | .satire f => f
      | .compile f _ _ => f
      | .execute f _ _ => f
    let slip : Fact := match b18_slip.monad with
      | .satire f => f
      | .compile f _ _ => f
      | .execute f _ _ => f
    { tape := .strap constructed slip Value (ULift.{i+1, i} Value) above.tape }

instance (priority := low) TRACED_EXECUTED
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
    -- UNIVERSAL / LOGICAL / HALTED deliberately NOT bound -- before, after, OR
    -- slip.  Class MEASURED's description type FROZE the concrete forward
    -- instances (UNIVERSAL_REAL and its chain) at Episode 13 definition time;
    -- any local run-band instance shadows the frozen ones and defeq refuses.
    -- The run-band slips therefore cross this seam as PLAIN DATA below --
    -- SpaceTimePath / EKG / Prop are ground-free inductives -- computed by the
    -- caller in a scope where the UNIVERSAL and LOGICAL slips are still legal.
    [b34_before: MEASURED Value PropCarrier b29_before]          [b35_before: COMPILED Value PropCarrier]          [b36_before: TrueOutput Value PropCarrier b29_before]
    (imaginary: CarrierProcess Value)
    [b36_after: TrueOutput Value PropCarrier b29_before]        [b35_after: COMPILED Value PropCarrier]          [b34_after: MEASURED Value PropCarrier b29_before]
    [b29_after: REAL Value PropCarrier] [b28_after: WITNESSED Value PropCarrier]
    [b27_after: TRUTH Value PropCarrier]  [b26_after: SCIENTIFIC Value PropCarrier] [b25_after: ACOLYTE Value PropCarrier]
    [b24_after: PROPAGANDA Value PropCarrier] [b23_after: BULLSHIT Value PropCarrier] [b22_after: FINITE_ELEPHANT Value PropCarrier]
    [b21_after: LOAD Value PropCarrier] [b20_after: SCALED Value PropCarrier] [b19_after: MAGNITUDE Value PropCarrier]
    [b18_after: VALUE Value PropCarrier] [b17_after: EXECUTED Value PropCarrier] [b16_after: SOURCE Value PropCarrier]
    [b15_after: GUNGAN Value PropCarrier] [b14_after: MEASURABLE Value PropCarrier] [b13_after: PRESENT Value PropCarrier]
    [b12_after: OBSERVED Value PropCarrier] [b11_after: COMPARABLE Value PropCarrier] [b10_after: PHYSICAL Value PropCarrier]
    [b9_after: REPRESENTABLE Value PropCarrier] [b8_after: NUMERIC Value PropCarrier] [b7_after: REPEATABLE Value PropCarrier]
    [b6_after: BINARY Value PropCarrier] [b5_after: RESIDUE Value PropCarrier][b4_after: ENCODED Value PropCarrier]
    [b3_after: COUNTABLE Value PropCarrier] [b2_after: ADMISSIBLE Value PropCarrier] [b1_after: DISTINGUISHABLE Value PropCarrier]
    (ledger: Fact)
    (b1_slip: DISTINGUISHABLE Value PropCarrier) (b2_slip: ADMISSIBLE Value PropCarrier) (b3_slip: COUNTABLE Value PropCarrier)
    (b4_slip: ENCODED Value PropCarrier) (b5_slip: RESIDUE Value PropCarrier) (b6_slip: BINARY Value PropCarrier)
    (b7_slip: REPEATABLE Value PropCarrier) (b8_slip: NUMERIC Value PropCarrier) (b9_slip: REPRESENTABLE Value PropCarrier)
    (b10_slip: PHYSICAL Value PropCarrier) (b11_slip: COMPARABLE Value PropCarrier) (b12_slip: OBSERVED Value PropCarrier)
    (b13_slip: PRESENT Value PropCarrier) (b14_slip: MEASURABLE Value PropCarrier) (b15_slip: GUNGAN Value PropCarrier)
    (b16_slip: SOURCE Value PropCarrier) (b17_slip: EXECUTED Value PropCarrier) (b18_slip: VALUE Value PropCarrier)
    (b19_slip: MAGNITUDE Value PropCarrier) (b20_slip: SCALED Value PropCarrier) (b21_slip: LOAD Value PropCarrier)
    (b22_slip: FINITE_ELEPHANT Value PropCarrier) (b23_slip: BULLSHIT Value PropCarrier) (b24_slip: PROPAGANDA Value PropCarrier)
    (b25_slip: ACOLYTE Value PropCarrier) (b26_slip: SCIENTIFIC Value PropCarrier) (b27_slip: TRUTH Value PropCarrier)
    (b28_slip: WITNESSED Value PropCarrier) (b29_slip: REAL Value PropCarrier)
    -- The run-band slip data, ground-free (see note above): the source and its
    -- torpedoed binary, the build verdict, the completed pass's calibration, and
    -- the log-coherence proposition -- b31_slip/b32_slip's content, minus their
    -- poisonous instance wrappers.
    (source_slip: SpaceTimePath) (compiled_slip: SpaceTimePath) (built_slip: Prop)
    (ekg_slip: Calibration.EKG) (coherent_slip: Prop)
    -- the before-side projection re-synthesizes the tower and the slip chain wins
    -- synthesis; the before fact crosses as data (law-1 mechanics, the corollary).
    (executed_encoding_fact_before: Fact)
    (b34_slip: MEASURED Value PropCarrier b29_slip) (b35_slip: COMPILED Value PropCarrier) (b36_slip: TrueOutput Value PropCarrier b29_slip)
    [above: TRACED Value PropCarrier 18]
    : TRACED Value PropCarrier 17 :=
    let constructed : Fact := executed_encoding_fact_before
    let slip : Fact := match b17_slip.compiled_process.opcode with
      | .boot f _ => f
      | .zero f _ _ => f
      | .one f _ _ _ _ => f
    { tape := .strap constructed slip Value (ULift.{i+1, i} Value) above.tape }

instance (priority := low) TRACED_SOURCE
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
    -- UNIVERSAL / LOGICAL / HALTED deliberately NOT bound -- before, after, OR
    -- slip.  Class MEASURED's description type FROZE the concrete forward
    -- instances (UNIVERSAL_REAL and its chain) at Episode 13 definition time;
    -- any local run-band instance shadows the frozen ones and defeq refuses.
    -- The run-band slips therefore cross this seam as PLAIN DATA below --
    -- SpaceTimePath / EKG / Prop are ground-free inductives -- computed by the
    -- caller in a scope where the UNIVERSAL and LOGICAL slips are still legal.
    [b34_before: MEASURED Value PropCarrier b29_before]          [b35_before: COMPILED Value PropCarrier]          [b36_before: TrueOutput Value PropCarrier b29_before]
    (imaginary: CarrierProcess Value)
    [b36_after: TrueOutput Value PropCarrier b29_before]        [b35_after: COMPILED Value PropCarrier]          [b34_after: MEASURED Value PropCarrier b29_before]
    [b29_after: REAL Value PropCarrier] [b28_after: WITNESSED Value PropCarrier]
    [b27_after: TRUTH Value PropCarrier]  [b26_after: SCIENTIFIC Value PropCarrier] [b25_after: ACOLYTE Value PropCarrier]
    [b24_after: PROPAGANDA Value PropCarrier] [b23_after: BULLSHIT Value PropCarrier] [b22_after: FINITE_ELEPHANT Value PropCarrier]
    [b21_after: LOAD Value PropCarrier] [b20_after: SCALED Value PropCarrier] [b19_after: MAGNITUDE Value PropCarrier]
    [b18_after: VALUE Value PropCarrier] [b17_after: EXECUTED Value PropCarrier] [b16_after: SOURCE Value PropCarrier]
    [b15_after: GUNGAN Value PropCarrier] [b14_after: MEASURABLE Value PropCarrier] [b13_after: PRESENT Value PropCarrier]
    [b12_after: OBSERVED Value PropCarrier] [b11_after: COMPARABLE Value PropCarrier] [b10_after: PHYSICAL Value PropCarrier]
    [b9_after: REPRESENTABLE Value PropCarrier] [b8_after: NUMERIC Value PropCarrier] [b7_after: REPEATABLE Value PropCarrier]
    [b6_after: BINARY Value PropCarrier] [b5_after: RESIDUE Value PropCarrier][b4_after: ENCODED Value PropCarrier]
    [b3_after: COUNTABLE Value PropCarrier] [b2_after: ADMISSIBLE Value PropCarrier] [b1_after: DISTINGUISHABLE Value PropCarrier]
    (ledger: Fact)
    (b1_slip: DISTINGUISHABLE Value PropCarrier) (b2_slip: ADMISSIBLE Value PropCarrier) (b3_slip: COUNTABLE Value PropCarrier)
    (b4_slip: ENCODED Value PropCarrier) (b5_slip: RESIDUE Value PropCarrier) (b6_slip: BINARY Value PropCarrier)
    (b7_slip: REPEATABLE Value PropCarrier) (b8_slip: NUMERIC Value PropCarrier) (b9_slip: REPRESENTABLE Value PropCarrier)
    (b10_slip: PHYSICAL Value PropCarrier) (b11_slip: COMPARABLE Value PropCarrier) (b12_slip: OBSERVED Value PropCarrier)
    (b13_slip: PRESENT Value PropCarrier) (b14_slip: MEASURABLE Value PropCarrier) (b15_slip: GUNGAN Value PropCarrier)
    (b16_slip: SOURCE Value PropCarrier) (b17_slip: EXECUTED Value PropCarrier) (b18_slip: VALUE Value PropCarrier)
    (b19_slip: MAGNITUDE Value PropCarrier) (b20_slip: SCALED Value PropCarrier) (b21_slip: LOAD Value PropCarrier)
    (b22_slip: FINITE_ELEPHANT Value PropCarrier) (b23_slip: BULLSHIT Value PropCarrier) (b24_slip: PROPAGANDA Value PropCarrier)
    (b25_slip: ACOLYTE Value PropCarrier) (b26_slip: SCIENTIFIC Value PropCarrier) (b27_slip: TRUTH Value PropCarrier)
    (b28_slip: WITNESSED Value PropCarrier) (b29_slip: REAL Value PropCarrier)
    -- The run-band slip data, ground-free (see note above): the source and its
    -- torpedoed binary, the build verdict, the completed pass's calibration, and
    -- the log-coherence proposition -- b31_slip/b32_slip's content, minus their
    -- poisonous instance wrappers.
    (source_slip: SpaceTimePath) (compiled_slip: SpaceTimePath) (built_slip: Prop)
    (ekg_slip: Calibration.EKG) (coherent_slip: Prop)
    (b34_slip: MEASURED Value PropCarrier b29_slip) (b35_slip: COMPILED Value PropCarrier) (b36_slip: TrueOutput Value PropCarrier b29_slip)
    [above: TRACED Value PropCarrier 17]
    : TRACED Value PropCarrier 16 :=
    let constructed : Fact := match b16_before.one with
      | .physics f _ => f
      | .zero_like f _ => f
      | .one_like _ _ _ => PropCarrier.symbol
    let slip : Fact := match b16_slip.one with
      | .physics f _ => f
      | .zero_like f _ => f
      | .one_like _ _ _ => PropCarrier.symbol
    { tape := .strap constructed slip Value (ULift.{i+1, i} Value) above.tape }

instance (priority := low) TRACED_GUNGAN
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
    -- UNIVERSAL / LOGICAL / HALTED deliberately NOT bound -- before, after, OR
    -- slip.  Class MEASURED's description type FROZE the concrete forward
    -- instances (UNIVERSAL_REAL and its chain) at Episode 13 definition time;
    -- any local run-band instance shadows the frozen ones and defeq refuses.
    -- The run-band slips therefore cross this seam as PLAIN DATA below --
    -- SpaceTimePath / EKG / Prop are ground-free inductives -- computed by the
    -- caller in a scope where the UNIVERSAL and LOGICAL slips are still legal.
    [b34_before: MEASURED Value PropCarrier b29_before]          [b35_before: COMPILED Value PropCarrier]          [b36_before: TrueOutput Value PropCarrier b29_before]
    (imaginary: CarrierProcess Value)
    [b36_after: TrueOutput Value PropCarrier b29_before]        [b35_after: COMPILED Value PropCarrier]          [b34_after: MEASURED Value PropCarrier b29_before]
    [b29_after: REAL Value PropCarrier] [b28_after: WITNESSED Value PropCarrier]
    [b27_after: TRUTH Value PropCarrier]  [b26_after: SCIENTIFIC Value PropCarrier] [b25_after: ACOLYTE Value PropCarrier]
    [b24_after: PROPAGANDA Value PropCarrier] [b23_after: BULLSHIT Value PropCarrier] [b22_after: FINITE_ELEPHANT Value PropCarrier]
    [b21_after: LOAD Value PropCarrier] [b20_after: SCALED Value PropCarrier] [b19_after: MAGNITUDE Value PropCarrier]
    [b18_after: VALUE Value PropCarrier] [b17_after: EXECUTED Value PropCarrier] [b16_after: SOURCE Value PropCarrier]
    [b15_after: GUNGAN Value PropCarrier] [b14_after: MEASURABLE Value PropCarrier] [b13_after: PRESENT Value PropCarrier]
    [b12_after: OBSERVED Value PropCarrier] [b11_after: COMPARABLE Value PropCarrier] [b10_after: PHYSICAL Value PropCarrier]
    [b9_after: REPRESENTABLE Value PropCarrier] [b8_after: NUMERIC Value PropCarrier] [b7_after: REPEATABLE Value PropCarrier]
    [b6_after: BINARY Value PropCarrier] [b5_after: RESIDUE Value PropCarrier][b4_after: ENCODED Value PropCarrier]
    [b3_after: COUNTABLE Value PropCarrier] [b2_after: ADMISSIBLE Value PropCarrier] [b1_after: DISTINGUISHABLE Value PropCarrier]
    (ledger: Fact)
    (b1_slip: DISTINGUISHABLE Value PropCarrier) (b2_slip: ADMISSIBLE Value PropCarrier) (b3_slip: COUNTABLE Value PropCarrier)
    (b4_slip: ENCODED Value PropCarrier) (b5_slip: RESIDUE Value PropCarrier) (b6_slip: BINARY Value PropCarrier)
    (b7_slip: REPEATABLE Value PropCarrier) (b8_slip: NUMERIC Value PropCarrier) (b9_slip: REPRESENTABLE Value PropCarrier)
    (b10_slip: PHYSICAL Value PropCarrier) (b11_slip: COMPARABLE Value PropCarrier) (b12_slip: OBSERVED Value PropCarrier)
    (b13_slip: PRESENT Value PropCarrier) (b14_slip: MEASURABLE Value PropCarrier) (b15_slip: GUNGAN Value PropCarrier)
    (b16_slip: SOURCE Value PropCarrier) (b17_slip: EXECUTED Value PropCarrier) (b18_slip: VALUE Value PropCarrier)
    (b19_slip: MAGNITUDE Value PropCarrier) (b20_slip: SCALED Value PropCarrier) (b21_slip: LOAD Value PropCarrier)
    (b22_slip: FINITE_ELEPHANT Value PropCarrier) (b23_slip: BULLSHIT Value PropCarrier) (b24_slip: PROPAGANDA Value PropCarrier)
    (b25_slip: ACOLYTE Value PropCarrier) (b26_slip: SCIENTIFIC Value PropCarrier) (b27_slip: TRUTH Value PropCarrier)
    (b28_slip: WITNESSED Value PropCarrier) (b29_slip: REAL Value PropCarrier)
    -- The run-band slip data, ground-free (see note above): the source and its
    -- torpedoed binary, the build verdict, the completed pass's calibration, and
    -- the log-coherence proposition -- b31_slip/b32_slip's content, minus their
    -- poisonous instance wrappers.
    (source_slip: SpaceTimePath) (compiled_slip: SpaceTimePath) (built_slip: Prop)
    (ekg_slip: Calibration.EKG) (coherent_slip: Prop)
    -- the before-side projection re-synthesizes the tower and the slip chain wins
    -- synthesis; the before fact crosses as data (law-1 mechanics, the corollary).
    (gungan_jar_fact_before: Fact)
    (b34_slip: MEASURED Value PropCarrier b29_slip) (b35_slip: COMPILED Value PropCarrier) (b36_slip: TrueOutput Value PropCarrier b29_slip)
    [above: TRACED Value PropCarrier 16]
    : TRACED Value PropCarrier 15 :=
    let constructed : Fact := gungan_jar_fact_before
    let slip : Fact := match b15_slip.meesa_process.concept with
      | .color f _ => f
      | .bang f _ => f
      | .superposition f _ _ => f
    { tape := .strap constructed slip Value (ULift.{i+1, i} Value) above.tape }

instance (priority := low) TRACED_MEASURABLE
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
    -- UNIVERSAL / LOGICAL / HALTED deliberately NOT bound -- before, after, OR
    -- slip.  Class MEASURED's description type FROZE the concrete forward
    -- instances (UNIVERSAL_REAL and its chain) at Episode 13 definition time;
    -- any local run-band instance shadows the frozen ones and defeq refuses.
    -- The run-band slips therefore cross this seam as PLAIN DATA below --
    -- SpaceTimePath / EKG / Prop are ground-free inductives -- computed by the
    -- caller in a scope where the UNIVERSAL and LOGICAL slips are still legal.
    [b34_before: MEASURED Value PropCarrier b29_before]          [b35_before: COMPILED Value PropCarrier]          [b36_before: TrueOutput Value PropCarrier b29_before]
    (imaginary: CarrierProcess Value)
    [b36_after: TrueOutput Value PropCarrier b29_before]        [b35_after: COMPILED Value PropCarrier]          [b34_after: MEASURED Value PropCarrier b29_before]
    [b29_after: REAL Value PropCarrier] [b28_after: WITNESSED Value PropCarrier]
    [b27_after: TRUTH Value PropCarrier]  [b26_after: SCIENTIFIC Value PropCarrier] [b25_after: ACOLYTE Value PropCarrier]
    [b24_after: PROPAGANDA Value PropCarrier] [b23_after: BULLSHIT Value PropCarrier] [b22_after: FINITE_ELEPHANT Value PropCarrier]
    [b21_after: LOAD Value PropCarrier] [b20_after: SCALED Value PropCarrier] [b19_after: MAGNITUDE Value PropCarrier]
    [b18_after: VALUE Value PropCarrier] [b17_after: EXECUTED Value PropCarrier] [b16_after: SOURCE Value PropCarrier]
    [b15_after: GUNGAN Value PropCarrier] [b14_after: MEASURABLE Value PropCarrier] [b13_after: PRESENT Value PropCarrier]
    [b12_after: OBSERVED Value PropCarrier] [b11_after: COMPARABLE Value PropCarrier] [b10_after: PHYSICAL Value PropCarrier]
    [b9_after: REPRESENTABLE Value PropCarrier] [b8_after: NUMERIC Value PropCarrier] [b7_after: REPEATABLE Value PropCarrier]
    [b6_after: BINARY Value PropCarrier] [b5_after: RESIDUE Value PropCarrier][b4_after: ENCODED Value PropCarrier]
    [b3_after: COUNTABLE Value PropCarrier] [b2_after: ADMISSIBLE Value PropCarrier] [b1_after: DISTINGUISHABLE Value PropCarrier]
    (ledger: Fact)
    (b1_slip: DISTINGUISHABLE Value PropCarrier) (b2_slip: ADMISSIBLE Value PropCarrier) (b3_slip: COUNTABLE Value PropCarrier)
    (b4_slip: ENCODED Value PropCarrier) (b5_slip: RESIDUE Value PropCarrier) (b6_slip: BINARY Value PropCarrier)
    (b7_slip: REPEATABLE Value PropCarrier) (b8_slip: NUMERIC Value PropCarrier) (b9_slip: REPRESENTABLE Value PropCarrier)
    (b10_slip: PHYSICAL Value PropCarrier) (b11_slip: COMPARABLE Value PropCarrier) (b12_slip: OBSERVED Value PropCarrier)
    (b13_slip: PRESENT Value PropCarrier) (b14_slip: MEASURABLE Value PropCarrier) (b15_slip: GUNGAN Value PropCarrier)
    (b16_slip: SOURCE Value PropCarrier) (b17_slip: EXECUTED Value PropCarrier) (b18_slip: VALUE Value PropCarrier)
    (b19_slip: MAGNITUDE Value PropCarrier) (b20_slip: SCALED Value PropCarrier) (b21_slip: LOAD Value PropCarrier)
    (b22_slip: FINITE_ELEPHANT Value PropCarrier) (b23_slip: BULLSHIT Value PropCarrier) (b24_slip: PROPAGANDA Value PropCarrier)
    (b25_slip: ACOLYTE Value PropCarrier) (b26_slip: SCIENTIFIC Value PropCarrier) (b27_slip: TRUTH Value PropCarrier)
    (b28_slip: WITNESSED Value PropCarrier) (b29_slip: REAL Value PropCarrier)
    -- The run-band slip data, ground-free (see note above): the source and its
    -- torpedoed binary, the build verdict, the completed pass's calibration, and
    -- the log-coherence proposition -- b31_slip/b32_slip's content, minus their
    -- poisonous instance wrappers.
    (source_slip: SpaceTimePath) (compiled_slip: SpaceTimePath) (built_slip: Prop)
    (ekg_slip: Calibration.EKG) (coherent_slip: Prop)
    -- the before-side projection re-synthesizes the tower and the slip chain wins
    -- synthesis; the before fact crosses as data (law-1 mechanics, the corollary).
    (measurable_phenomenon_fact_before: Fact)
    (b34_slip: MEASURED Value PropCarrier b29_slip) (b35_slip: COMPILED Value PropCarrier) (b36_slip: TrueOutput Value PropCarrier b29_slip)
    [above: TRACED Value PropCarrier 15]
    : TRACED Value PropCarrier 14 :=
    let constructed : Fact := measurable_phenomenon_fact_before
    let slip : Fact := match b14_slip.gauge_process.clock with
      | .field f _ => f
      | .initial_condition f _ _ => f
      | .observations f _ _ _ _ => f
    { tape := .strap constructed slip Value (ULift.{i+1, i} Value) above.tape }

instance (priority := low) TRACED_PRESENT
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
    -- UNIVERSAL / LOGICAL / HALTED deliberately NOT bound -- before, after, OR
    -- slip.  Class MEASURED's description type FROZE the concrete forward
    -- instances (UNIVERSAL_REAL and its chain) at Episode 13 definition time;
    -- any local run-band instance shadows the frozen ones and defeq refuses.
    -- The run-band slips therefore cross this seam as PLAIN DATA below --
    -- SpaceTimePath / EKG / Prop are ground-free inductives -- computed by the
    -- caller in a scope where the UNIVERSAL and LOGICAL slips are still legal.
    [b34_before: MEASURED Value PropCarrier b29_before]          [b35_before: COMPILED Value PropCarrier]          [b36_before: TrueOutput Value PropCarrier b29_before]
    (imaginary: CarrierProcess Value)
    [b36_after: TrueOutput Value PropCarrier b29_before]        [b35_after: COMPILED Value PropCarrier]          [b34_after: MEASURED Value PropCarrier b29_before]
    [b29_after: REAL Value PropCarrier] [b28_after: WITNESSED Value PropCarrier]
    [b27_after: TRUTH Value PropCarrier]  [b26_after: SCIENTIFIC Value PropCarrier] [b25_after: ACOLYTE Value PropCarrier]
    [b24_after: PROPAGANDA Value PropCarrier] [b23_after: BULLSHIT Value PropCarrier] [b22_after: FINITE_ELEPHANT Value PropCarrier]
    [b21_after: LOAD Value PropCarrier] [b20_after: SCALED Value PropCarrier] [b19_after: MAGNITUDE Value PropCarrier]
    [b18_after: VALUE Value PropCarrier] [b17_after: EXECUTED Value PropCarrier] [b16_after: SOURCE Value PropCarrier]
    [b15_after: GUNGAN Value PropCarrier] [b14_after: MEASURABLE Value PropCarrier] [b13_after: PRESENT Value PropCarrier]
    [b12_after: OBSERVED Value PropCarrier] [b11_after: COMPARABLE Value PropCarrier] [b10_after: PHYSICAL Value PropCarrier]
    [b9_after: REPRESENTABLE Value PropCarrier] [b8_after: NUMERIC Value PropCarrier] [b7_after: REPEATABLE Value PropCarrier]
    [b6_after: BINARY Value PropCarrier] [b5_after: RESIDUE Value PropCarrier][b4_after: ENCODED Value PropCarrier]
    [b3_after: COUNTABLE Value PropCarrier] [b2_after: ADMISSIBLE Value PropCarrier] [b1_after: DISTINGUISHABLE Value PropCarrier]
    (ledger: Fact)
    (b1_slip: DISTINGUISHABLE Value PropCarrier) (b2_slip: ADMISSIBLE Value PropCarrier) (b3_slip: COUNTABLE Value PropCarrier)
    (b4_slip: ENCODED Value PropCarrier) (b5_slip: RESIDUE Value PropCarrier) (b6_slip: BINARY Value PropCarrier)
    (b7_slip: REPEATABLE Value PropCarrier) (b8_slip: NUMERIC Value PropCarrier) (b9_slip: REPRESENTABLE Value PropCarrier)
    (b10_slip: PHYSICAL Value PropCarrier) (b11_slip: COMPARABLE Value PropCarrier) (b12_slip: OBSERVED Value PropCarrier)
    (b13_slip: PRESENT Value PropCarrier) (b14_slip: MEASURABLE Value PropCarrier) (b15_slip: GUNGAN Value PropCarrier)
    (b16_slip: SOURCE Value PropCarrier) (b17_slip: EXECUTED Value PropCarrier) (b18_slip: VALUE Value PropCarrier)
    (b19_slip: MAGNITUDE Value PropCarrier) (b20_slip: SCALED Value PropCarrier) (b21_slip: LOAD Value PropCarrier)
    (b22_slip: FINITE_ELEPHANT Value PropCarrier) (b23_slip: BULLSHIT Value PropCarrier) (b24_slip: PROPAGANDA Value PropCarrier)
    (b25_slip: ACOLYTE Value PropCarrier) (b26_slip: SCIENTIFIC Value PropCarrier) (b27_slip: TRUTH Value PropCarrier)
    (b28_slip: WITNESSED Value PropCarrier) (b29_slip: REAL Value PropCarrier)
    -- The run-band slip data, ground-free (see note above): the source and its
    -- torpedoed binary, the build verdict, the completed pass's calibration, and
    -- the log-coherence proposition -- b31_slip/b32_slip's content, minus their
    -- poisonous instance wrappers.
    (source_slip: SpaceTimePath) (compiled_slip: SpaceTimePath) (built_slip: Prop)
    (ekg_slip: Calibration.EKG) (coherent_slip: Prop)
    -- the before-side projection re-synthesizes the tower and the slip chain wins
    -- synthesis; the before fact crosses as data (law-1 mechanics, the corollary).
    (present_area_fact_before: Fact)
    (b34_slip: MEASURED Value PropCarrier b29_slip) (b35_slip: COMPILED Value PropCarrier) (b36_slip: TrueOutput Value PropCarrier b29_slip)
    [above: TRACED Value PropCarrier 14]
    : TRACED Value PropCarrier 13 :=
    let constructed : Fact := present_area_fact_before
    let slip : Fact := match b13_slip.santa_claus.accumulation with
      | .t f => f
      | .dt f _ _ => f
    { tape := .strap constructed slip Value (ULift.{i+1, i} Value) above.tape }

instance (priority := low) TRACED_OBSERVED
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
    -- UNIVERSAL / LOGICAL / HALTED deliberately NOT bound -- before, after, OR
    -- slip.  Class MEASURED's description type FROZE the concrete forward
    -- instances (UNIVERSAL_REAL and its chain) at Episode 13 definition time;
    -- any local run-band instance shadows the frozen ones and defeq refuses.
    -- The run-band slips therefore cross this seam as PLAIN DATA below --
    -- SpaceTimePath / EKG / Prop are ground-free inductives -- computed by the
    -- caller in a scope where the UNIVERSAL and LOGICAL slips are still legal.
    [b34_before: MEASURED Value PropCarrier b29_before]          [b35_before: COMPILED Value PropCarrier]          [b36_before: TrueOutput Value PropCarrier b29_before]
    (imaginary: CarrierProcess Value)
    [b36_after: TrueOutput Value PropCarrier b29_before]        [b35_after: COMPILED Value PropCarrier]          [b34_after: MEASURED Value PropCarrier b29_before]
    [b29_after: REAL Value PropCarrier] [b28_after: WITNESSED Value PropCarrier]
    [b27_after: TRUTH Value PropCarrier]  [b26_after: SCIENTIFIC Value PropCarrier] [b25_after: ACOLYTE Value PropCarrier]
    [b24_after: PROPAGANDA Value PropCarrier] [b23_after: BULLSHIT Value PropCarrier] [b22_after: FINITE_ELEPHANT Value PropCarrier]
    [b21_after: LOAD Value PropCarrier] [b20_after: SCALED Value PropCarrier] [b19_after: MAGNITUDE Value PropCarrier]
    [b18_after: VALUE Value PropCarrier] [b17_after: EXECUTED Value PropCarrier] [b16_after: SOURCE Value PropCarrier]
    [b15_after: GUNGAN Value PropCarrier] [b14_after: MEASURABLE Value PropCarrier] [b13_after: PRESENT Value PropCarrier]
    [b12_after: OBSERVED Value PropCarrier] [b11_after: COMPARABLE Value PropCarrier] [b10_after: PHYSICAL Value PropCarrier]
    [b9_after: REPRESENTABLE Value PropCarrier] [b8_after: NUMERIC Value PropCarrier] [b7_after: REPEATABLE Value PropCarrier]
    [b6_after: BINARY Value PropCarrier] [b5_after: RESIDUE Value PropCarrier][b4_after: ENCODED Value PropCarrier]
    [b3_after: COUNTABLE Value PropCarrier] [b2_after: ADMISSIBLE Value PropCarrier] [b1_after: DISTINGUISHABLE Value PropCarrier]
    (ledger: Fact)
    (b1_slip: DISTINGUISHABLE Value PropCarrier) (b2_slip: ADMISSIBLE Value PropCarrier) (b3_slip: COUNTABLE Value PropCarrier)
    (b4_slip: ENCODED Value PropCarrier) (b5_slip: RESIDUE Value PropCarrier) (b6_slip: BINARY Value PropCarrier)
    (b7_slip: REPEATABLE Value PropCarrier) (b8_slip: NUMERIC Value PropCarrier) (b9_slip: REPRESENTABLE Value PropCarrier)
    (b10_slip: PHYSICAL Value PropCarrier) (b11_slip: COMPARABLE Value PropCarrier) (b12_slip: OBSERVED Value PropCarrier)
    (b13_slip: PRESENT Value PropCarrier) (b14_slip: MEASURABLE Value PropCarrier) (b15_slip: GUNGAN Value PropCarrier)
    (b16_slip: SOURCE Value PropCarrier) (b17_slip: EXECUTED Value PropCarrier) (b18_slip: VALUE Value PropCarrier)
    (b19_slip: MAGNITUDE Value PropCarrier) (b20_slip: SCALED Value PropCarrier) (b21_slip: LOAD Value PropCarrier)
    (b22_slip: FINITE_ELEPHANT Value PropCarrier) (b23_slip: BULLSHIT Value PropCarrier) (b24_slip: PROPAGANDA Value PropCarrier)
    (b25_slip: ACOLYTE Value PropCarrier) (b26_slip: SCIENTIFIC Value PropCarrier) (b27_slip: TRUTH Value PropCarrier)
    (b28_slip: WITNESSED Value PropCarrier) (b29_slip: REAL Value PropCarrier)
    -- The run-band slip data, ground-free (see note above): the source and its
    -- torpedoed binary, the build verdict, the completed pass's calibration, and
    -- the log-coherence proposition -- b31_slip/b32_slip's content, minus their
    -- poisonous instance wrappers.
    (source_slip: SpaceTimePath) (compiled_slip: SpaceTimePath) (built_slip: Prop)
    (ekg_slip: Calibration.EKG) (coherent_slip: Prop)
    -- the before-side projection re-synthesizes the tower and the slip chain wins
    -- synthesis; the before fact crosses as data (law-1 mechanics, the corollary).
    (observed_sophism_fact_before: Fact)
    (b34_slip: MEASURED Value PropCarrier b29_slip) (b35_slip: COMPILED Value PropCarrier) (b36_slip: TrueOutput Value PropCarrier b29_slip)
    [above: TRACED Value PropCarrier 13]
    : TRACED Value PropCarrier 12 :=
    let constructed : Fact := observed_sophism_fact_before
    let slip : Fact := match b12_slip.slip_process.projection with
      | .origin f _ _ => f
      | .dimension f _ _ _ => f
    { tape := .strap constructed slip Value (ULift.{i+1, i} Value) above.tape }

instance (priority := low) TRACED_COMPARABLE
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
    -- UNIVERSAL / LOGICAL / HALTED deliberately NOT bound -- before, after, OR
    -- slip.  Class MEASURED's description type FROZE the concrete forward
    -- instances (UNIVERSAL_REAL and its chain) at Episode 13 definition time;
    -- any local run-band instance shadows the frozen ones and defeq refuses.
    -- The run-band slips therefore cross this seam as PLAIN DATA below --
    -- SpaceTimePath / EKG / Prop are ground-free inductives -- computed by the
    -- caller in a scope where the UNIVERSAL and LOGICAL slips are still legal.
    [b34_before: MEASURED Value PropCarrier b29_before]          [b35_before: COMPILED Value PropCarrier]          [b36_before: TrueOutput Value PropCarrier b29_before]
    (imaginary: CarrierProcess Value)
    [b36_after: TrueOutput Value PropCarrier b29_before]        [b35_after: COMPILED Value PropCarrier]          [b34_after: MEASURED Value PropCarrier b29_before]
    [b29_after: REAL Value PropCarrier] [b28_after: WITNESSED Value PropCarrier]
    [b27_after: TRUTH Value PropCarrier]  [b26_after: SCIENTIFIC Value PropCarrier] [b25_after: ACOLYTE Value PropCarrier]
    [b24_after: PROPAGANDA Value PropCarrier] [b23_after: BULLSHIT Value PropCarrier] [b22_after: FINITE_ELEPHANT Value PropCarrier]
    [b21_after: LOAD Value PropCarrier] [b20_after: SCALED Value PropCarrier] [b19_after: MAGNITUDE Value PropCarrier]
    [b18_after: VALUE Value PropCarrier] [b17_after: EXECUTED Value PropCarrier] [b16_after: SOURCE Value PropCarrier]
    [b15_after: GUNGAN Value PropCarrier] [b14_after: MEASURABLE Value PropCarrier] [b13_after: PRESENT Value PropCarrier]
    [b12_after: OBSERVED Value PropCarrier] [b11_after: COMPARABLE Value PropCarrier] [b10_after: PHYSICAL Value PropCarrier]
    [b9_after: REPRESENTABLE Value PropCarrier] [b8_after: NUMERIC Value PropCarrier] [b7_after: REPEATABLE Value PropCarrier]
    [b6_after: BINARY Value PropCarrier] [b5_after: RESIDUE Value PropCarrier][b4_after: ENCODED Value PropCarrier]
    [b3_after: COUNTABLE Value PropCarrier] [b2_after: ADMISSIBLE Value PropCarrier] [b1_after: DISTINGUISHABLE Value PropCarrier]
    (ledger: Fact)
    (b1_slip: DISTINGUISHABLE Value PropCarrier) (b2_slip: ADMISSIBLE Value PropCarrier) (b3_slip: COUNTABLE Value PropCarrier)
    (b4_slip: ENCODED Value PropCarrier) (b5_slip: RESIDUE Value PropCarrier) (b6_slip: BINARY Value PropCarrier)
    (b7_slip: REPEATABLE Value PropCarrier) (b8_slip: NUMERIC Value PropCarrier) (b9_slip: REPRESENTABLE Value PropCarrier)
    (b10_slip: PHYSICAL Value PropCarrier) (b11_slip: COMPARABLE Value PropCarrier) (b12_slip: OBSERVED Value PropCarrier)
    (b13_slip: PRESENT Value PropCarrier) (b14_slip: MEASURABLE Value PropCarrier) (b15_slip: GUNGAN Value PropCarrier)
    (b16_slip: SOURCE Value PropCarrier) (b17_slip: EXECUTED Value PropCarrier) (b18_slip: VALUE Value PropCarrier)
    (b19_slip: MAGNITUDE Value PropCarrier) (b20_slip: SCALED Value PropCarrier) (b21_slip: LOAD Value PropCarrier)
    (b22_slip: FINITE_ELEPHANT Value PropCarrier) (b23_slip: BULLSHIT Value PropCarrier) (b24_slip: PROPAGANDA Value PropCarrier)
    (b25_slip: ACOLYTE Value PropCarrier) (b26_slip: SCIENTIFIC Value PropCarrier) (b27_slip: TRUTH Value PropCarrier)
    (b28_slip: WITNESSED Value PropCarrier) (b29_slip: REAL Value PropCarrier)
    -- The run-band slip data, ground-free (see note above): the source and its
    -- torpedoed binary, the build verdict, the completed pass's calibration, and
    -- the log-coherence proposition -- b31_slip/b32_slip's content, minus their
    -- poisonous instance wrappers.
    (source_slip: SpaceTimePath) (compiled_slip: SpaceTimePath) (built_slip: Prop)
    (ekg_slip: Calibration.EKG) (coherent_slip: Prop)
    -- the before-side projection re-synthesizes the tower and the slip chain wins
    -- synthesis; the before fact crosses as data (law-1 mechanics, the corollary).
    (comparable_metavariable_fact_before: Fact)
    (b34_slip: MEASURED Value PropCarrier b29_slip) (b35_slip: COMPILED Value PropCarrier) (b36_slip: TrueOutput Value PropCarrier b29_slip)
    [above: TRACED Value PropCarrier 12]
    : TRACED Value PropCarrier 11 :=
    let constructed : Fact := comparable_metavariable_fact_before
    let slip : Fact := match b11_slip.physical_process.value with
      | .base f _ => f
      | .step f _ => f
    { tape := .strap constructed slip Value (ULift.{i+1, i} Value) above.tape }

instance (priority := low) TRACED_PHYSICAL
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
    -- UNIVERSAL / LOGICAL / HALTED deliberately NOT bound -- before, after, OR
    -- slip.  Class MEASURED's description type FROZE the concrete forward
    -- instances (UNIVERSAL_REAL and its chain) at Episode 13 definition time;
    -- any local run-band instance shadows the frozen ones and defeq refuses.
    -- The run-band slips therefore cross this seam as PLAIN DATA below --
    -- SpaceTimePath / EKG / Prop are ground-free inductives -- computed by the
    -- caller in a scope where the UNIVERSAL and LOGICAL slips are still legal.
    [b34_before: MEASURED Value PropCarrier b29_before]          [b35_before: COMPILED Value PropCarrier]          [b36_before: TrueOutput Value PropCarrier b29_before]
    (imaginary: CarrierProcess Value)
    [b36_after: TrueOutput Value PropCarrier b29_before]        [b35_after: COMPILED Value PropCarrier]          [b34_after: MEASURED Value PropCarrier b29_before]
    [b29_after: REAL Value PropCarrier] [b28_after: WITNESSED Value PropCarrier]
    [b27_after: TRUTH Value PropCarrier]  [b26_after: SCIENTIFIC Value PropCarrier] [b25_after: ACOLYTE Value PropCarrier]
    [b24_after: PROPAGANDA Value PropCarrier] [b23_after: BULLSHIT Value PropCarrier] [b22_after: FINITE_ELEPHANT Value PropCarrier]
    [b21_after: LOAD Value PropCarrier] [b20_after: SCALED Value PropCarrier] [b19_after: MAGNITUDE Value PropCarrier]
    [b18_after: VALUE Value PropCarrier] [b17_after: EXECUTED Value PropCarrier] [b16_after: SOURCE Value PropCarrier]
    [b15_after: GUNGAN Value PropCarrier] [b14_after: MEASURABLE Value PropCarrier] [b13_after: PRESENT Value PropCarrier]
    [b12_after: OBSERVED Value PropCarrier] [b11_after: COMPARABLE Value PropCarrier] [b10_after: PHYSICAL Value PropCarrier]
    [b9_after: REPRESENTABLE Value PropCarrier] [b8_after: NUMERIC Value PropCarrier] [b7_after: REPEATABLE Value PropCarrier]
    [b6_after: BINARY Value PropCarrier] [b5_after: RESIDUE Value PropCarrier][b4_after: ENCODED Value PropCarrier]
    [b3_after: COUNTABLE Value PropCarrier] [b2_after: ADMISSIBLE Value PropCarrier] [b1_after: DISTINGUISHABLE Value PropCarrier]
    (ledger: Fact)
    (b1_slip: DISTINGUISHABLE Value PropCarrier) (b2_slip: ADMISSIBLE Value PropCarrier) (b3_slip: COUNTABLE Value PropCarrier)
    (b4_slip: ENCODED Value PropCarrier) (b5_slip: RESIDUE Value PropCarrier) (b6_slip: BINARY Value PropCarrier)
    (b7_slip: REPEATABLE Value PropCarrier) (b8_slip: NUMERIC Value PropCarrier) (b9_slip: REPRESENTABLE Value PropCarrier)
    (b10_slip: PHYSICAL Value PropCarrier) (b11_slip: COMPARABLE Value PropCarrier) (b12_slip: OBSERVED Value PropCarrier)
    (b13_slip: PRESENT Value PropCarrier) (b14_slip: MEASURABLE Value PropCarrier) (b15_slip: GUNGAN Value PropCarrier)
    (b16_slip: SOURCE Value PropCarrier) (b17_slip: EXECUTED Value PropCarrier) (b18_slip: VALUE Value PropCarrier)
    (b19_slip: MAGNITUDE Value PropCarrier) (b20_slip: SCALED Value PropCarrier) (b21_slip: LOAD Value PropCarrier)
    (b22_slip: FINITE_ELEPHANT Value PropCarrier) (b23_slip: BULLSHIT Value PropCarrier) (b24_slip: PROPAGANDA Value PropCarrier)
    (b25_slip: ACOLYTE Value PropCarrier) (b26_slip: SCIENTIFIC Value PropCarrier) (b27_slip: TRUTH Value PropCarrier)
    (b28_slip: WITNESSED Value PropCarrier) (b29_slip: REAL Value PropCarrier)
    -- The run-band slip data, ground-free (see note above): the source and its
    -- torpedoed binary, the build verdict, the completed pass's calibration, and
    -- the log-coherence proposition -- b31_slip/b32_slip's content, minus their
    -- poisonous instance wrappers.
    (source_slip: SpaceTimePath) (compiled_slip: SpaceTimePath) (built_slip: Prop)
    (ekg_slip: Calibration.EKG) (coherent_slip: Prop)
    (b34_slip: MEASURED Value PropCarrier b29_slip) (b35_slip: COMPILED Value PropCarrier) (b36_slip: TrueOutput Value PropCarrier b29_slip)
    [above: TRACED Value PropCarrier 11]
    : TRACED Value PropCarrier 10 :=
    let constructed : Fact := match b10_before.threshold with
      | .halting f _ => f
      | .nonhalting f _ _ => f
    let slip : Fact := match b10_slip.threshold with
      | .halting f _ => f
      | .nonhalting f _ _ => f
    { tape := .strap constructed slip Value (ULift.{i+1, i} Value) above.tape }

instance (priority := low) TRACED_REPRESENTABLE
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
    -- UNIVERSAL / LOGICAL / HALTED deliberately NOT bound -- before, after, OR
    -- slip.  Class MEASURED's description type FROZE the concrete forward
    -- instances (UNIVERSAL_REAL and its chain) at Episode 13 definition time;
    -- any local run-band instance shadows the frozen ones and defeq refuses.
    -- The run-band slips therefore cross this seam as PLAIN DATA below --
    -- SpaceTimePath / EKG / Prop are ground-free inductives -- computed by the
    -- caller in a scope where the UNIVERSAL and LOGICAL slips are still legal.
    [b34_before: MEASURED Value PropCarrier b29_before]          [b35_before: COMPILED Value PropCarrier]          [b36_before: TrueOutput Value PropCarrier b29_before]
    (imaginary: CarrierProcess Value)
    [b36_after: TrueOutput Value PropCarrier b29_before]        [b35_after: COMPILED Value PropCarrier]          [b34_after: MEASURED Value PropCarrier b29_before]
    [b29_after: REAL Value PropCarrier] [b28_after: WITNESSED Value PropCarrier]
    [b27_after: TRUTH Value PropCarrier]  [b26_after: SCIENTIFIC Value PropCarrier] [b25_after: ACOLYTE Value PropCarrier]
    [b24_after: PROPAGANDA Value PropCarrier] [b23_after: BULLSHIT Value PropCarrier] [b22_after: FINITE_ELEPHANT Value PropCarrier]
    [b21_after: LOAD Value PropCarrier] [b20_after: SCALED Value PropCarrier] [b19_after: MAGNITUDE Value PropCarrier]
    [b18_after: VALUE Value PropCarrier] [b17_after: EXECUTED Value PropCarrier] [b16_after: SOURCE Value PropCarrier]
    [b15_after: GUNGAN Value PropCarrier] [b14_after: MEASURABLE Value PropCarrier] [b13_after: PRESENT Value PropCarrier]
    [b12_after: OBSERVED Value PropCarrier] [b11_after: COMPARABLE Value PropCarrier] [b10_after: PHYSICAL Value PropCarrier]
    [b9_after: REPRESENTABLE Value PropCarrier] [b8_after: NUMERIC Value PropCarrier] [b7_after: REPEATABLE Value PropCarrier]
    [b6_after: BINARY Value PropCarrier] [b5_after: RESIDUE Value PropCarrier][b4_after: ENCODED Value PropCarrier]
    [b3_after: COUNTABLE Value PropCarrier] [b2_after: ADMISSIBLE Value PropCarrier] [b1_after: DISTINGUISHABLE Value PropCarrier]
    (ledger: Fact)
    (b1_slip: DISTINGUISHABLE Value PropCarrier) (b2_slip: ADMISSIBLE Value PropCarrier) (b3_slip: COUNTABLE Value PropCarrier)
    (b4_slip: ENCODED Value PropCarrier) (b5_slip: RESIDUE Value PropCarrier) (b6_slip: BINARY Value PropCarrier)
    (b7_slip: REPEATABLE Value PropCarrier) (b8_slip: NUMERIC Value PropCarrier) (b9_slip: REPRESENTABLE Value PropCarrier)
    (b10_slip: PHYSICAL Value PropCarrier) (b11_slip: COMPARABLE Value PropCarrier) (b12_slip: OBSERVED Value PropCarrier)
    (b13_slip: PRESENT Value PropCarrier) (b14_slip: MEASURABLE Value PropCarrier) (b15_slip: GUNGAN Value PropCarrier)
    (b16_slip: SOURCE Value PropCarrier) (b17_slip: EXECUTED Value PropCarrier) (b18_slip: VALUE Value PropCarrier)
    (b19_slip: MAGNITUDE Value PropCarrier) (b20_slip: SCALED Value PropCarrier) (b21_slip: LOAD Value PropCarrier)
    (b22_slip: FINITE_ELEPHANT Value PropCarrier) (b23_slip: BULLSHIT Value PropCarrier) (b24_slip: PROPAGANDA Value PropCarrier)
    (b25_slip: ACOLYTE Value PropCarrier) (b26_slip: SCIENTIFIC Value PropCarrier) (b27_slip: TRUTH Value PropCarrier)
    (b28_slip: WITNESSED Value PropCarrier) (b29_slip: REAL Value PropCarrier)
    -- The run-band slip data, ground-free (see note above): the source and its
    -- torpedoed binary, the build verdict, the completed pass's calibration, and
    -- the log-coherence proposition -- b31_slip/b32_slip's content, minus their
    -- poisonous instance wrappers.
    (source_slip: SpaceTimePath) (compiled_slip: SpaceTimePath) (built_slip: Prop)
    (ekg_slip: Calibration.EKG) (coherent_slip: Prop)
    -- the before-side projection re-synthesizes the tower and the slip chain wins
    -- synthesis; the before fact crosses as data (law-1 mechanics, the corollary).
    (representable_state_fact_before: Fact)
    (b34_slip: MEASURED Value PropCarrier b29_slip) (b35_slip: COMPILED Value PropCarrier) (b36_slip: TrueOutput Value PropCarrier b29_slip)
    [above: TRACED Value PropCarrier 10]
    : TRACED Value PropCarrier 9 :=
    let constructed : Fact := representable_state_fact_before
    let slip : Fact := match b9_slip.calculation_process.state with
      | .program f _ => f
      | .compute f _ _ _ => f
    { tape := .strap constructed slip Value (ULift.{i+1, i} Value) above.tape }

instance (priority := low) TRACED_NUMERIC
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
    -- UNIVERSAL / LOGICAL / HALTED deliberately NOT bound -- before, after, OR
    -- slip.  Class MEASURED's description type FROZE the concrete forward
    -- instances (UNIVERSAL_REAL and its chain) at Episode 13 definition time;
    -- any local run-band instance shadows the frozen ones and defeq refuses.
    -- The run-band slips therefore cross this seam as PLAIN DATA below --
    -- SpaceTimePath / EKG / Prop are ground-free inductives -- computed by the
    -- caller in a scope where the UNIVERSAL and LOGICAL slips are still legal.
    [b34_before: MEASURED Value PropCarrier b29_before]          [b35_before: COMPILED Value PropCarrier]          [b36_before: TrueOutput Value PropCarrier b29_before]
    (imaginary: CarrierProcess Value)
    [b36_after: TrueOutput Value PropCarrier b29_before]        [b35_after: COMPILED Value PropCarrier]          [b34_after: MEASURED Value PropCarrier b29_before]
    [b29_after: REAL Value PropCarrier] [b28_after: WITNESSED Value PropCarrier]
    [b27_after: TRUTH Value PropCarrier]  [b26_after: SCIENTIFIC Value PropCarrier] [b25_after: ACOLYTE Value PropCarrier]
    [b24_after: PROPAGANDA Value PropCarrier] [b23_after: BULLSHIT Value PropCarrier] [b22_after: FINITE_ELEPHANT Value PropCarrier]
    [b21_after: LOAD Value PropCarrier] [b20_after: SCALED Value PropCarrier] [b19_after: MAGNITUDE Value PropCarrier]
    [b18_after: VALUE Value PropCarrier] [b17_after: EXECUTED Value PropCarrier] [b16_after: SOURCE Value PropCarrier]
    [b15_after: GUNGAN Value PropCarrier] [b14_after: MEASURABLE Value PropCarrier] [b13_after: PRESENT Value PropCarrier]
    [b12_after: OBSERVED Value PropCarrier] [b11_after: COMPARABLE Value PropCarrier] [b10_after: PHYSICAL Value PropCarrier]
    [b9_after: REPRESENTABLE Value PropCarrier] [b8_after: NUMERIC Value PropCarrier] [b7_after: REPEATABLE Value PropCarrier]
    [b6_after: BINARY Value PropCarrier] [b5_after: RESIDUE Value PropCarrier][b4_after: ENCODED Value PropCarrier]
    [b3_after: COUNTABLE Value PropCarrier] [b2_after: ADMISSIBLE Value PropCarrier] [b1_after: DISTINGUISHABLE Value PropCarrier]
    (ledger: Fact)
    (b1_slip: DISTINGUISHABLE Value PropCarrier) (b2_slip: ADMISSIBLE Value PropCarrier) (b3_slip: COUNTABLE Value PropCarrier)
    (b4_slip: ENCODED Value PropCarrier) (b5_slip: RESIDUE Value PropCarrier) (b6_slip: BINARY Value PropCarrier)
    (b7_slip: REPEATABLE Value PropCarrier) (b8_slip: NUMERIC Value PropCarrier) (b9_slip: REPRESENTABLE Value PropCarrier)
    (b10_slip: PHYSICAL Value PropCarrier) (b11_slip: COMPARABLE Value PropCarrier) (b12_slip: OBSERVED Value PropCarrier)
    (b13_slip: PRESENT Value PropCarrier) (b14_slip: MEASURABLE Value PropCarrier) (b15_slip: GUNGAN Value PropCarrier)
    (b16_slip: SOURCE Value PropCarrier) (b17_slip: EXECUTED Value PropCarrier) (b18_slip: VALUE Value PropCarrier)
    (b19_slip: MAGNITUDE Value PropCarrier) (b20_slip: SCALED Value PropCarrier) (b21_slip: LOAD Value PropCarrier)
    (b22_slip: FINITE_ELEPHANT Value PropCarrier) (b23_slip: BULLSHIT Value PropCarrier) (b24_slip: PROPAGANDA Value PropCarrier)
    (b25_slip: ACOLYTE Value PropCarrier) (b26_slip: SCIENTIFIC Value PropCarrier) (b27_slip: TRUTH Value PropCarrier)
    (b28_slip: WITNESSED Value PropCarrier) (b29_slip: REAL Value PropCarrier)
    -- The run-band slip data, ground-free (see note above): the source and its
    -- torpedoed binary, the build verdict, the completed pass's calibration, and
    -- the log-coherence proposition -- b31_slip/b32_slip's content, minus their
    -- poisonous instance wrappers.
    (source_slip: SpaceTimePath) (compiled_slip: SpaceTimePath) (built_slip: Prop)
    (ekg_slip: Calibration.EKG) (coherent_slip: Prop)
    (b34_slip: MEASURED Value PropCarrier b29_slip) (b35_slip: COMPILED Value PropCarrier) (b36_slip: TrueOutput Value PropCarrier b29_slip)
    [above: TRACED Value PropCarrier 9]
    : TRACED Value PropCarrier 8 :=
    let constructed : Fact := match b8_before.carrier with
      | .hypothesis f => f
      | .data f _ _ => f
    let slip : Fact := match b8_slip.carrier with
      | .hypothesis f => f
      | .data f _ _ => f
    { tape := .strap constructed slip Value (ULift.{i+1, i} Value) above.tape }

instance (priority := low) TRACED_REPEATABLE
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
    -- UNIVERSAL / LOGICAL / HALTED deliberately NOT bound -- before, after, OR
    -- slip.  Class MEASURED's description type FROZE the concrete forward
    -- instances (UNIVERSAL_REAL and its chain) at Episode 13 definition time;
    -- any local run-band instance shadows the frozen ones and defeq refuses.
    -- The run-band slips therefore cross this seam as PLAIN DATA below --
    -- SpaceTimePath / EKG / Prop are ground-free inductives -- computed by the
    -- caller in a scope where the UNIVERSAL and LOGICAL slips are still legal.
    [b34_before: MEASURED Value PropCarrier b29_before]          [b35_before: COMPILED Value PropCarrier]          [b36_before: TrueOutput Value PropCarrier b29_before]
    (imaginary: CarrierProcess Value)
    [b36_after: TrueOutput Value PropCarrier b29_before]        [b35_after: COMPILED Value PropCarrier]          [b34_after: MEASURED Value PropCarrier b29_before]
    [b29_after: REAL Value PropCarrier] [b28_after: WITNESSED Value PropCarrier]
    [b27_after: TRUTH Value PropCarrier]  [b26_after: SCIENTIFIC Value PropCarrier] [b25_after: ACOLYTE Value PropCarrier]
    [b24_after: PROPAGANDA Value PropCarrier] [b23_after: BULLSHIT Value PropCarrier] [b22_after: FINITE_ELEPHANT Value PropCarrier]
    [b21_after: LOAD Value PropCarrier] [b20_after: SCALED Value PropCarrier] [b19_after: MAGNITUDE Value PropCarrier]
    [b18_after: VALUE Value PropCarrier] [b17_after: EXECUTED Value PropCarrier] [b16_after: SOURCE Value PropCarrier]
    [b15_after: GUNGAN Value PropCarrier] [b14_after: MEASURABLE Value PropCarrier] [b13_after: PRESENT Value PropCarrier]
    [b12_after: OBSERVED Value PropCarrier] [b11_after: COMPARABLE Value PropCarrier] [b10_after: PHYSICAL Value PropCarrier]
    [b9_after: REPRESENTABLE Value PropCarrier] [b8_after: NUMERIC Value PropCarrier] [b7_after: REPEATABLE Value PropCarrier]
    [b6_after: BINARY Value PropCarrier] [b5_after: RESIDUE Value PropCarrier][b4_after: ENCODED Value PropCarrier]
    [b3_after: COUNTABLE Value PropCarrier] [b2_after: ADMISSIBLE Value PropCarrier] [b1_after: DISTINGUISHABLE Value PropCarrier]
    (ledger: Fact)
    (b1_slip: DISTINGUISHABLE Value PropCarrier) (b2_slip: ADMISSIBLE Value PropCarrier) (b3_slip: COUNTABLE Value PropCarrier)
    (b4_slip: ENCODED Value PropCarrier) (b5_slip: RESIDUE Value PropCarrier) (b6_slip: BINARY Value PropCarrier)
    (b7_slip: REPEATABLE Value PropCarrier) (b8_slip: NUMERIC Value PropCarrier) (b9_slip: REPRESENTABLE Value PropCarrier)
    (b10_slip: PHYSICAL Value PropCarrier) (b11_slip: COMPARABLE Value PropCarrier) (b12_slip: OBSERVED Value PropCarrier)
    (b13_slip: PRESENT Value PropCarrier) (b14_slip: MEASURABLE Value PropCarrier) (b15_slip: GUNGAN Value PropCarrier)
    (b16_slip: SOURCE Value PropCarrier) (b17_slip: EXECUTED Value PropCarrier) (b18_slip: VALUE Value PropCarrier)
    (b19_slip: MAGNITUDE Value PropCarrier) (b20_slip: SCALED Value PropCarrier) (b21_slip: LOAD Value PropCarrier)
    (b22_slip: FINITE_ELEPHANT Value PropCarrier) (b23_slip: BULLSHIT Value PropCarrier) (b24_slip: PROPAGANDA Value PropCarrier)
    (b25_slip: ACOLYTE Value PropCarrier) (b26_slip: SCIENTIFIC Value PropCarrier) (b27_slip: TRUTH Value PropCarrier)
    (b28_slip: WITNESSED Value PropCarrier) (b29_slip: REAL Value PropCarrier)
    -- The run-band slip data, ground-free (see note above): the source and its
    -- torpedoed binary, the build verdict, the completed pass's calibration, and
    -- the log-coherence proposition -- b31_slip/b32_slip's content, minus their
    -- poisonous instance wrappers.
    (source_slip: SpaceTimePath) (compiled_slip: SpaceTimePath) (built_slip: Prop)
    (ekg_slip: Calibration.EKG) (coherent_slip: Prop)
    -- the before-side projection re-synthesizes the tower and the slip chain wins
    -- synthesis; the before fact crosses as data (law-1 mechanics, the corollary).
    (repeatable_trial_fact_before: Fact)
    (b34_slip: MEASURED Value PropCarrier b29_slip) (b35_slip: COMPILED Value PropCarrier) (b36_slip: TrueOutput Value PropCarrier b29_slip)
    [above: TRACED Value PropCarrier 8]
    : TRACED Value PropCarrier 7 :=
    let constructed : Fact := repeatable_trial_fact_before
    let slip : Fact := match b7_slip.repeatable_process.expectation with
      | .hypothesis f _ => f
      | .signal_response f _ _ _ _ => f
    { tape := .strap constructed slip Value (ULift.{i+1, i} Value) above.tape }

instance (priority := low) TRACED_BINARY
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
    -- UNIVERSAL / LOGICAL / HALTED deliberately NOT bound -- before, after, OR
    -- slip.  Class MEASURED's description type FROZE the concrete forward
    -- instances (UNIVERSAL_REAL and its chain) at Episode 13 definition time;
    -- any local run-band instance shadows the frozen ones and defeq refuses.
    -- The run-band slips therefore cross this seam as PLAIN DATA below --
    -- SpaceTimePath / EKG / Prop are ground-free inductives -- computed by the
    -- caller in a scope where the UNIVERSAL and LOGICAL slips are still legal.
    [b34_before: MEASURED Value PropCarrier b29_before]          [b35_before: COMPILED Value PropCarrier]          [b36_before: TrueOutput Value PropCarrier b29_before]
    (imaginary: CarrierProcess Value)
    [b36_after: TrueOutput Value PropCarrier b29_before]        [b35_after: COMPILED Value PropCarrier]          [b34_after: MEASURED Value PropCarrier b29_before]
    [b29_after: REAL Value PropCarrier] [b28_after: WITNESSED Value PropCarrier]
    [b27_after: TRUTH Value PropCarrier]  [b26_after: SCIENTIFIC Value PropCarrier] [b25_after: ACOLYTE Value PropCarrier]
    [b24_after: PROPAGANDA Value PropCarrier] [b23_after: BULLSHIT Value PropCarrier] [b22_after: FINITE_ELEPHANT Value PropCarrier]
    [b21_after: LOAD Value PropCarrier] [b20_after: SCALED Value PropCarrier] [b19_after: MAGNITUDE Value PropCarrier]
    [b18_after: VALUE Value PropCarrier] [b17_after: EXECUTED Value PropCarrier] [b16_after: SOURCE Value PropCarrier]
    [b15_after: GUNGAN Value PropCarrier] [b14_after: MEASURABLE Value PropCarrier] [b13_after: PRESENT Value PropCarrier]
    [b12_after: OBSERVED Value PropCarrier] [b11_after: COMPARABLE Value PropCarrier] [b10_after: PHYSICAL Value PropCarrier]
    [b9_after: REPRESENTABLE Value PropCarrier] [b8_after: NUMERIC Value PropCarrier] [b7_after: REPEATABLE Value PropCarrier]
    [b6_after: BINARY Value PropCarrier] [b5_after: RESIDUE Value PropCarrier][b4_after: ENCODED Value PropCarrier]
    [b3_after: COUNTABLE Value PropCarrier] [b2_after: ADMISSIBLE Value PropCarrier] [b1_after: DISTINGUISHABLE Value PropCarrier]
    (ledger: Fact)
    (b1_slip: DISTINGUISHABLE Value PropCarrier) (b2_slip: ADMISSIBLE Value PropCarrier) (b3_slip: COUNTABLE Value PropCarrier)
    (b4_slip: ENCODED Value PropCarrier) (b5_slip: RESIDUE Value PropCarrier) (b6_slip: BINARY Value PropCarrier)
    (b7_slip: REPEATABLE Value PropCarrier) (b8_slip: NUMERIC Value PropCarrier) (b9_slip: REPRESENTABLE Value PropCarrier)
    (b10_slip: PHYSICAL Value PropCarrier) (b11_slip: COMPARABLE Value PropCarrier) (b12_slip: OBSERVED Value PropCarrier)
    (b13_slip: PRESENT Value PropCarrier) (b14_slip: MEASURABLE Value PropCarrier) (b15_slip: GUNGAN Value PropCarrier)
    (b16_slip: SOURCE Value PropCarrier) (b17_slip: EXECUTED Value PropCarrier) (b18_slip: VALUE Value PropCarrier)
    (b19_slip: MAGNITUDE Value PropCarrier) (b20_slip: SCALED Value PropCarrier) (b21_slip: LOAD Value PropCarrier)
    (b22_slip: FINITE_ELEPHANT Value PropCarrier) (b23_slip: BULLSHIT Value PropCarrier) (b24_slip: PROPAGANDA Value PropCarrier)
    (b25_slip: ACOLYTE Value PropCarrier) (b26_slip: SCIENTIFIC Value PropCarrier) (b27_slip: TRUTH Value PropCarrier)
    (b28_slip: WITNESSED Value PropCarrier) (b29_slip: REAL Value PropCarrier)
    -- The run-band slip data, ground-free (see note above): the source and its
    -- torpedoed binary, the build verdict, the completed pass's calibration, and
    -- the log-coherence proposition -- b31_slip/b32_slip's content, minus their
    -- poisonous instance wrappers.
    (source_slip: SpaceTimePath) (compiled_slip: SpaceTimePath) (built_slip: Prop)
    (ekg_slip: Calibration.EKG) (coherent_slip: Prop)
    (b34_slip: MEASURED Value PropCarrier b29_slip) (b35_slip: COMPILED Value PropCarrier) (b36_slip: TrueOutput Value PropCarrier b29_slip)
    [above: TRACED Value PropCarrier 7]
    : TRACED Value PropCarrier 6 :=
    let constructed : Fact := match b6_before.bit with
      | .initial_condition f _ => f
      | .signal_response f _ _ _ _ => f
    let slip : Fact := match b6_slip.bit with
      | .initial_condition f _ => f
      | .signal_response f _ _ _ _ => f
    { tape := .strap constructed slip Value (ULift.{i+1, i} Value) above.tape }

instance (priority := low) TRACED_RESIDUE
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
    -- UNIVERSAL / LOGICAL / HALTED deliberately NOT bound -- before, after, OR
    -- slip.  Class MEASURED's description type FROZE the concrete forward
    -- instances (UNIVERSAL_REAL and its chain) at Episode 13 definition time;
    -- any local run-band instance shadows the frozen ones and defeq refuses.
    -- The run-band slips therefore cross this seam as PLAIN DATA below --
    -- SpaceTimePath / EKG / Prop are ground-free inductives -- computed by the
    -- caller in a scope where the UNIVERSAL and LOGICAL slips are still legal.
    [b34_before: MEASURED Value PropCarrier b29_before]          [b35_before: COMPILED Value PropCarrier]          [b36_before: TrueOutput Value PropCarrier b29_before]
    (imaginary: CarrierProcess Value)
    [b36_after: TrueOutput Value PropCarrier b29_before]        [b35_after: COMPILED Value PropCarrier]          [b34_after: MEASURED Value PropCarrier b29_before]
    [b29_after: REAL Value PropCarrier] [b28_after: WITNESSED Value PropCarrier]
    [b27_after: TRUTH Value PropCarrier]  [b26_after: SCIENTIFIC Value PropCarrier] [b25_after: ACOLYTE Value PropCarrier]
    [b24_after: PROPAGANDA Value PropCarrier] [b23_after: BULLSHIT Value PropCarrier] [b22_after: FINITE_ELEPHANT Value PropCarrier]
    [b21_after: LOAD Value PropCarrier] [b20_after: SCALED Value PropCarrier] [b19_after: MAGNITUDE Value PropCarrier]
    [b18_after: VALUE Value PropCarrier] [b17_after: EXECUTED Value PropCarrier] [b16_after: SOURCE Value PropCarrier]
    [b15_after: GUNGAN Value PropCarrier] [b14_after: MEASURABLE Value PropCarrier] [b13_after: PRESENT Value PropCarrier]
    [b12_after: OBSERVED Value PropCarrier] [b11_after: COMPARABLE Value PropCarrier] [b10_after: PHYSICAL Value PropCarrier]
    [b9_after: REPRESENTABLE Value PropCarrier] [b8_after: NUMERIC Value PropCarrier] [b7_after: REPEATABLE Value PropCarrier]
    [b6_after: BINARY Value PropCarrier] [b5_after: RESIDUE Value PropCarrier][b4_after: ENCODED Value PropCarrier]
    [b3_after: COUNTABLE Value PropCarrier] [b2_after: ADMISSIBLE Value PropCarrier] [b1_after: DISTINGUISHABLE Value PropCarrier]
    (ledger: Fact)
    (b1_slip: DISTINGUISHABLE Value PropCarrier) (b2_slip: ADMISSIBLE Value PropCarrier) (b3_slip: COUNTABLE Value PropCarrier)
    (b4_slip: ENCODED Value PropCarrier) (b5_slip: RESIDUE Value PropCarrier) (b6_slip: BINARY Value PropCarrier)
    (b7_slip: REPEATABLE Value PropCarrier) (b8_slip: NUMERIC Value PropCarrier) (b9_slip: REPRESENTABLE Value PropCarrier)
    (b10_slip: PHYSICAL Value PropCarrier) (b11_slip: COMPARABLE Value PropCarrier) (b12_slip: OBSERVED Value PropCarrier)
    (b13_slip: PRESENT Value PropCarrier) (b14_slip: MEASURABLE Value PropCarrier) (b15_slip: GUNGAN Value PropCarrier)
    (b16_slip: SOURCE Value PropCarrier) (b17_slip: EXECUTED Value PropCarrier) (b18_slip: VALUE Value PropCarrier)
    (b19_slip: MAGNITUDE Value PropCarrier) (b20_slip: SCALED Value PropCarrier) (b21_slip: LOAD Value PropCarrier)
    (b22_slip: FINITE_ELEPHANT Value PropCarrier) (b23_slip: BULLSHIT Value PropCarrier) (b24_slip: PROPAGANDA Value PropCarrier)
    (b25_slip: ACOLYTE Value PropCarrier) (b26_slip: SCIENTIFIC Value PropCarrier) (b27_slip: TRUTH Value PropCarrier)
    (b28_slip: WITNESSED Value PropCarrier) (b29_slip: REAL Value PropCarrier)
    -- The run-band slip data, ground-free (see note above): the source and its
    -- torpedoed binary, the build verdict, the completed pass's calibration, and
    -- the log-coherence proposition -- b31_slip/b32_slip's content, minus their
    -- poisonous instance wrappers.
    (source_slip: SpaceTimePath) (compiled_slip: SpaceTimePath) (built_slip: Prop)
    (ekg_slip: Calibration.EKG) (coherent_slip: Prop)
    -- the before-side projection re-synthesizes the tower and the slip chain wins
    -- synthesis; the before fact crosses as data (law-1 mechanics, the corollary).
    (residue_carrier_fact_before: Fact)
    (b34_slip: MEASURED Value PropCarrier b29_slip) (b35_slip: COMPILED Value PropCarrier) (b36_slip: TrueOutput Value PropCarrier b29_slip)
    [above: TRACED Value PropCarrier 6]
    : TRACED Value PropCarrier 5 :=
    let constructed : Fact := residue_carrier_fact_before
    let slip : Fact := b5_slip.cauchy_process.limit_process.indexing_process.count.carrier.symbol
    { tape := .strap constructed slip Value (ULift.{i+1, i} Value) above.tape }

instance (priority := low) TRACED_ENCODED
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
    -- UNIVERSAL / LOGICAL / HALTED deliberately NOT bound -- before, after, OR
    -- slip.  Class MEASURED's description type FROZE the concrete forward
    -- instances (UNIVERSAL_REAL and its chain) at Episode 13 definition time;
    -- any local run-band instance shadows the frozen ones and defeq refuses.
    -- The run-band slips therefore cross this seam as PLAIN DATA below --
    -- SpaceTimePath / EKG / Prop are ground-free inductives -- computed by the
    -- caller in a scope where the UNIVERSAL and LOGICAL slips are still legal.
    [b34_before: MEASURED Value PropCarrier b29_before]          [b35_before: COMPILED Value PropCarrier]          [b36_before: TrueOutput Value PropCarrier b29_before]
    (imaginary: CarrierProcess Value)
    [b36_after: TrueOutput Value PropCarrier b29_before]        [b35_after: COMPILED Value PropCarrier]          [b34_after: MEASURED Value PropCarrier b29_before]
    [b29_after: REAL Value PropCarrier] [b28_after: WITNESSED Value PropCarrier]
    [b27_after: TRUTH Value PropCarrier]  [b26_after: SCIENTIFIC Value PropCarrier] [b25_after: ACOLYTE Value PropCarrier]
    [b24_after: PROPAGANDA Value PropCarrier] [b23_after: BULLSHIT Value PropCarrier] [b22_after: FINITE_ELEPHANT Value PropCarrier]
    [b21_after: LOAD Value PropCarrier] [b20_after: SCALED Value PropCarrier] [b19_after: MAGNITUDE Value PropCarrier]
    [b18_after: VALUE Value PropCarrier] [b17_after: EXECUTED Value PropCarrier] [b16_after: SOURCE Value PropCarrier]
    [b15_after: GUNGAN Value PropCarrier] [b14_after: MEASURABLE Value PropCarrier] [b13_after: PRESENT Value PropCarrier]
    [b12_after: OBSERVED Value PropCarrier] [b11_after: COMPARABLE Value PropCarrier] [b10_after: PHYSICAL Value PropCarrier]
    [b9_after: REPRESENTABLE Value PropCarrier] [b8_after: NUMERIC Value PropCarrier] [b7_after: REPEATABLE Value PropCarrier]
    [b6_after: BINARY Value PropCarrier] [b5_after: RESIDUE Value PropCarrier][b4_after: ENCODED Value PropCarrier]
    [b3_after: COUNTABLE Value PropCarrier] [b2_after: ADMISSIBLE Value PropCarrier] [b1_after: DISTINGUISHABLE Value PropCarrier]
    (ledger: Fact)
    (b1_slip: DISTINGUISHABLE Value PropCarrier) (b2_slip: ADMISSIBLE Value PropCarrier) (b3_slip: COUNTABLE Value PropCarrier)
    (b4_slip: ENCODED Value PropCarrier) (b5_slip: RESIDUE Value PropCarrier) (b6_slip: BINARY Value PropCarrier)
    (b7_slip: REPEATABLE Value PropCarrier) (b8_slip: NUMERIC Value PropCarrier) (b9_slip: REPRESENTABLE Value PropCarrier)
    (b10_slip: PHYSICAL Value PropCarrier) (b11_slip: COMPARABLE Value PropCarrier) (b12_slip: OBSERVED Value PropCarrier)
    (b13_slip: PRESENT Value PropCarrier) (b14_slip: MEASURABLE Value PropCarrier) (b15_slip: GUNGAN Value PropCarrier)
    (b16_slip: SOURCE Value PropCarrier) (b17_slip: EXECUTED Value PropCarrier) (b18_slip: VALUE Value PropCarrier)
    (b19_slip: MAGNITUDE Value PropCarrier) (b20_slip: SCALED Value PropCarrier) (b21_slip: LOAD Value PropCarrier)
    (b22_slip: FINITE_ELEPHANT Value PropCarrier) (b23_slip: BULLSHIT Value PropCarrier) (b24_slip: PROPAGANDA Value PropCarrier)
    (b25_slip: ACOLYTE Value PropCarrier) (b26_slip: SCIENTIFIC Value PropCarrier) (b27_slip: TRUTH Value PropCarrier)
    (b28_slip: WITNESSED Value PropCarrier) (b29_slip: REAL Value PropCarrier)
    -- The run-band slip data, ground-free (see note above): the source and its
    -- torpedoed binary, the build verdict, the completed pass's calibration, and
    -- the log-coherence proposition -- b31_slip/b32_slip's content, minus their
    -- poisonous instance wrappers.
    (source_slip: SpaceTimePath) (compiled_slip: SpaceTimePath) (built_slip: Prop)
    (ekg_slip: Calibration.EKG) (coherent_slip: Prop)
    -- the before-side projection re-synthesizes the tower and the slip chain wins
    -- synthesis; the before fact crosses as data (law-1 mechanics, the corollary).
    (encoded_carrier_fact_before: Fact)
    (b34_slip: MEASURED Value PropCarrier b29_slip) (b35_slip: COMPILED Value PropCarrier) (b36_slip: TrueOutput Value PropCarrier b29_slip)
    [above: TRACED Value PropCarrier 5]
    : TRACED Value PropCarrier 4 :=
    let constructed : Fact := encoded_carrier_fact_before
    let slip : Fact := b4_slip.limit_process.indexing_process.count.carrier.symbol
    { tape := .strap constructed slip Value (ULift.{i+1, i} Value) above.tape }

instance (priority := low) TRACED_COUNTABLE
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
    -- UNIVERSAL / LOGICAL / HALTED deliberately NOT bound -- before, after, OR
    -- slip.  Class MEASURED's description type FROZE the concrete forward
    -- instances (UNIVERSAL_REAL and its chain) at Episode 13 definition time;
    -- any local run-band instance shadows the frozen ones and defeq refuses.
    -- The run-band slips therefore cross this seam as PLAIN DATA below --
    -- SpaceTimePath / EKG / Prop are ground-free inductives -- computed by the
    -- caller in a scope where the UNIVERSAL and LOGICAL slips are still legal.
    [b34_before: MEASURED Value PropCarrier b29_before]          [b35_before: COMPILED Value PropCarrier]          [b36_before: TrueOutput Value PropCarrier b29_before]
    (imaginary: CarrierProcess Value)
    [b36_after: TrueOutput Value PropCarrier b29_before]        [b35_after: COMPILED Value PropCarrier]          [b34_after: MEASURED Value PropCarrier b29_before]
    [b29_after: REAL Value PropCarrier] [b28_after: WITNESSED Value PropCarrier]
    [b27_after: TRUTH Value PropCarrier]  [b26_after: SCIENTIFIC Value PropCarrier] [b25_after: ACOLYTE Value PropCarrier]
    [b24_after: PROPAGANDA Value PropCarrier] [b23_after: BULLSHIT Value PropCarrier] [b22_after: FINITE_ELEPHANT Value PropCarrier]
    [b21_after: LOAD Value PropCarrier] [b20_after: SCALED Value PropCarrier] [b19_after: MAGNITUDE Value PropCarrier]
    [b18_after: VALUE Value PropCarrier] [b17_after: EXECUTED Value PropCarrier] [b16_after: SOURCE Value PropCarrier]
    [b15_after: GUNGAN Value PropCarrier] [b14_after: MEASURABLE Value PropCarrier] [b13_after: PRESENT Value PropCarrier]
    [b12_after: OBSERVED Value PropCarrier] [b11_after: COMPARABLE Value PropCarrier] [b10_after: PHYSICAL Value PropCarrier]
    [b9_after: REPRESENTABLE Value PropCarrier] [b8_after: NUMERIC Value PropCarrier] [b7_after: REPEATABLE Value PropCarrier]
    [b6_after: BINARY Value PropCarrier] [b5_after: RESIDUE Value PropCarrier][b4_after: ENCODED Value PropCarrier]
    [b3_after: COUNTABLE Value PropCarrier] [b2_after: ADMISSIBLE Value PropCarrier] [b1_after: DISTINGUISHABLE Value PropCarrier]
    (ledger: Fact)
    (b1_slip: DISTINGUISHABLE Value PropCarrier) (b2_slip: ADMISSIBLE Value PropCarrier) (b3_slip: COUNTABLE Value PropCarrier)
    (b4_slip: ENCODED Value PropCarrier) (b5_slip: RESIDUE Value PropCarrier) (b6_slip: BINARY Value PropCarrier)
    (b7_slip: REPEATABLE Value PropCarrier) (b8_slip: NUMERIC Value PropCarrier) (b9_slip: REPRESENTABLE Value PropCarrier)
    (b10_slip: PHYSICAL Value PropCarrier) (b11_slip: COMPARABLE Value PropCarrier) (b12_slip: OBSERVED Value PropCarrier)
    (b13_slip: PRESENT Value PropCarrier) (b14_slip: MEASURABLE Value PropCarrier) (b15_slip: GUNGAN Value PropCarrier)
    (b16_slip: SOURCE Value PropCarrier) (b17_slip: EXECUTED Value PropCarrier) (b18_slip: VALUE Value PropCarrier)
    (b19_slip: MAGNITUDE Value PropCarrier) (b20_slip: SCALED Value PropCarrier) (b21_slip: LOAD Value PropCarrier)
    (b22_slip: FINITE_ELEPHANT Value PropCarrier) (b23_slip: BULLSHIT Value PropCarrier) (b24_slip: PROPAGANDA Value PropCarrier)
    (b25_slip: ACOLYTE Value PropCarrier) (b26_slip: SCIENTIFIC Value PropCarrier) (b27_slip: TRUTH Value PropCarrier)
    (b28_slip: WITNESSED Value PropCarrier) (b29_slip: REAL Value PropCarrier)
    -- The run-band slip data, ground-free (see note above): the source and its
    -- torpedoed binary, the build verdict, the completed pass's calibration, and
    -- the log-coherence proposition -- b31_slip/b32_slip's content, minus their
    -- poisonous instance wrappers.
    (source_slip: SpaceTimePath) (compiled_slip: SpaceTimePath) (built_slip: Prop)
    (ekg_slip: Calibration.EKG) (coherent_slip: Prop)
    -- the before-side projection re-synthesizes the tower and the slip chain wins
    -- synthesis; the before fact crosses as data (law-1 mechanics, the corollary).
    (countable_carrier_fact_before: Fact)
    (b34_slip: MEASURED Value PropCarrier b29_slip) (b35_slip: COMPILED Value PropCarrier) (b36_slip: TrueOutput Value PropCarrier b29_slip)
    [above: TRACED Value PropCarrier 4]
    : TRACED Value PropCarrier 3 :=
    let constructed : Fact := countable_carrier_fact_before
    let slip : Fact := b3_slip.index.count.carrier.symbol
    { tape := .strap constructed slip Value (ULift.{i+1, i} Value) above.tape }

instance (priority := low) TRACED_ADMISSIBLE
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
    -- UNIVERSAL / LOGICAL / HALTED deliberately NOT bound -- before, after, OR
    -- slip.  Class MEASURED's description type FROZE the concrete forward
    -- instances (UNIVERSAL_REAL and its chain) at Episode 13 definition time;
    -- any local run-band instance shadows the frozen ones and defeq refuses.
    -- The run-band slips therefore cross this seam as PLAIN DATA below --
    -- SpaceTimePath / EKG / Prop are ground-free inductives -- computed by the
    -- caller in a scope where the UNIVERSAL and LOGICAL slips are still legal.
    [b34_before: MEASURED Value PropCarrier b29_before]          [b35_before: COMPILED Value PropCarrier]          [b36_before: TrueOutput Value PropCarrier b29_before]
    (imaginary: CarrierProcess Value)
    [b36_after: TrueOutput Value PropCarrier b29_before]        [b35_after: COMPILED Value PropCarrier]          [b34_after: MEASURED Value PropCarrier b29_before]
    [b29_after: REAL Value PropCarrier] [b28_after: WITNESSED Value PropCarrier]
    [b27_after: TRUTH Value PropCarrier]  [b26_after: SCIENTIFIC Value PropCarrier] [b25_after: ACOLYTE Value PropCarrier]
    [b24_after: PROPAGANDA Value PropCarrier] [b23_after: BULLSHIT Value PropCarrier] [b22_after: FINITE_ELEPHANT Value PropCarrier]
    [b21_after: LOAD Value PropCarrier] [b20_after: SCALED Value PropCarrier] [b19_after: MAGNITUDE Value PropCarrier]
    [b18_after: VALUE Value PropCarrier] [b17_after: EXECUTED Value PropCarrier] [b16_after: SOURCE Value PropCarrier]
    [b15_after: GUNGAN Value PropCarrier] [b14_after: MEASURABLE Value PropCarrier] [b13_after: PRESENT Value PropCarrier]
    [b12_after: OBSERVED Value PropCarrier] [b11_after: COMPARABLE Value PropCarrier] [b10_after: PHYSICAL Value PropCarrier]
    [b9_after: REPRESENTABLE Value PropCarrier] [b8_after: NUMERIC Value PropCarrier] [b7_after: REPEATABLE Value PropCarrier]
    [b6_after: BINARY Value PropCarrier] [b5_after: RESIDUE Value PropCarrier][b4_after: ENCODED Value PropCarrier]
    [b3_after: COUNTABLE Value PropCarrier] [b2_after: ADMISSIBLE Value PropCarrier] [b1_after: DISTINGUISHABLE Value PropCarrier]
    (ledger: Fact)
    (b1_slip: DISTINGUISHABLE Value PropCarrier) (b2_slip: ADMISSIBLE Value PropCarrier) (b3_slip: COUNTABLE Value PropCarrier)
    (b4_slip: ENCODED Value PropCarrier) (b5_slip: RESIDUE Value PropCarrier) (b6_slip: BINARY Value PropCarrier)
    (b7_slip: REPEATABLE Value PropCarrier) (b8_slip: NUMERIC Value PropCarrier) (b9_slip: REPRESENTABLE Value PropCarrier)
    (b10_slip: PHYSICAL Value PropCarrier) (b11_slip: COMPARABLE Value PropCarrier) (b12_slip: OBSERVED Value PropCarrier)
    (b13_slip: PRESENT Value PropCarrier) (b14_slip: MEASURABLE Value PropCarrier) (b15_slip: GUNGAN Value PropCarrier)
    (b16_slip: SOURCE Value PropCarrier) (b17_slip: EXECUTED Value PropCarrier) (b18_slip: VALUE Value PropCarrier)
    (b19_slip: MAGNITUDE Value PropCarrier) (b20_slip: SCALED Value PropCarrier) (b21_slip: LOAD Value PropCarrier)
    (b22_slip: FINITE_ELEPHANT Value PropCarrier) (b23_slip: BULLSHIT Value PropCarrier) (b24_slip: PROPAGANDA Value PropCarrier)
    (b25_slip: ACOLYTE Value PropCarrier) (b26_slip: SCIENTIFIC Value PropCarrier) (b27_slip: TRUTH Value PropCarrier)
    (b28_slip: WITNESSED Value PropCarrier) (b29_slip: REAL Value PropCarrier)
    -- The run-band slip data, ground-free (see note above): the source and its
    -- torpedoed binary, the build verdict, the completed pass's calibration, and
    -- the log-coherence proposition -- b31_slip/b32_slip's content, minus their
    -- poisonous instance wrappers.
    (source_slip: SpaceTimePath) (compiled_slip: SpaceTimePath) (built_slip: Prop)
    (ekg_slip: Calibration.EKG) (coherent_slip: Prop)
    -- the before-side projection re-synthesizes the tower and the slip chain wins
    -- synthesis; the before fact crosses as data (law-1 mechanics, the corollary).
    (admissible_carrier_fact_before: Fact)
    (b34_slip: MEASURED Value PropCarrier b29_slip) (b35_slip: COMPILED Value PropCarrier) (b36_slip: TrueOutput Value PropCarrier b29_slip)
    [above: TRACED Value PropCarrier 3]
    : TRACED Value PropCarrier 2 :=
    let constructed : Fact := admissible_carrier_fact_before
    let slip : Fact := b2_slip.counting_process.carrier.symbol
    { tape := .strap constructed slip Value (ULift.{i+1, i} Value) above.tape }

instance (priority := low) TRACED_DISTINGUISHABLE
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
    -- UNIVERSAL / LOGICAL / HALTED deliberately NOT bound -- before, after, OR
    -- slip.  Class MEASURED's description type FROZE the concrete forward
    -- instances (UNIVERSAL_REAL and its chain) at Episode 13 definition time;
    -- any local run-band instance shadows the frozen ones and defeq refuses.
    -- The run-band slips therefore cross this seam as PLAIN DATA below --
    -- SpaceTimePath / EKG / Prop are ground-free inductives -- computed by the
    -- caller in a scope where the UNIVERSAL and LOGICAL slips are still legal.
    [b34_before: MEASURED Value PropCarrier b29_before]          [b35_before: COMPILED Value PropCarrier]          [b36_before: TrueOutput Value PropCarrier b29_before]
    (imaginary: CarrierProcess Value)
    [b36_after: TrueOutput Value PropCarrier b29_before]        [b35_after: COMPILED Value PropCarrier]          [b34_after: MEASURED Value PropCarrier b29_before]
    [b29_after: REAL Value PropCarrier] [b28_after: WITNESSED Value PropCarrier]
    [b27_after: TRUTH Value PropCarrier]  [b26_after: SCIENTIFIC Value PropCarrier] [b25_after: ACOLYTE Value PropCarrier]
    [b24_after: PROPAGANDA Value PropCarrier] [b23_after: BULLSHIT Value PropCarrier] [b22_after: FINITE_ELEPHANT Value PropCarrier]
    [b21_after: LOAD Value PropCarrier] [b20_after: SCALED Value PropCarrier] [b19_after: MAGNITUDE Value PropCarrier]
    [b18_after: VALUE Value PropCarrier] [b17_after: EXECUTED Value PropCarrier] [b16_after: SOURCE Value PropCarrier]
    [b15_after: GUNGAN Value PropCarrier] [b14_after: MEASURABLE Value PropCarrier] [b13_after: PRESENT Value PropCarrier]
    [b12_after: OBSERVED Value PropCarrier] [b11_after: COMPARABLE Value PropCarrier] [b10_after: PHYSICAL Value PropCarrier]
    [b9_after: REPRESENTABLE Value PropCarrier] [b8_after: NUMERIC Value PropCarrier] [b7_after: REPEATABLE Value PropCarrier]
    [b6_after: BINARY Value PropCarrier] [b5_after: RESIDUE Value PropCarrier][b4_after: ENCODED Value PropCarrier]
    [b3_after: COUNTABLE Value PropCarrier] [b2_after: ADMISSIBLE Value PropCarrier] [b1_after: DISTINGUISHABLE Value PropCarrier]
    (ledger: Fact)
    (b1_slip: DISTINGUISHABLE Value PropCarrier) (b2_slip: ADMISSIBLE Value PropCarrier) (b3_slip: COUNTABLE Value PropCarrier)
    (b4_slip: ENCODED Value PropCarrier) (b5_slip: RESIDUE Value PropCarrier) (b6_slip: BINARY Value PropCarrier)
    (b7_slip: REPEATABLE Value PropCarrier) (b8_slip: NUMERIC Value PropCarrier) (b9_slip: REPRESENTABLE Value PropCarrier)
    (b10_slip: PHYSICAL Value PropCarrier) (b11_slip: COMPARABLE Value PropCarrier) (b12_slip: OBSERVED Value PropCarrier)
    (b13_slip: PRESENT Value PropCarrier) (b14_slip: MEASURABLE Value PropCarrier) (b15_slip: GUNGAN Value PropCarrier)
    (b16_slip: SOURCE Value PropCarrier) (b17_slip: EXECUTED Value PropCarrier) (b18_slip: VALUE Value PropCarrier)
    (b19_slip: MAGNITUDE Value PropCarrier) (b20_slip: SCALED Value PropCarrier) (b21_slip: LOAD Value PropCarrier)
    (b22_slip: FINITE_ELEPHANT Value PropCarrier) (b23_slip: BULLSHIT Value PropCarrier) (b24_slip: PROPAGANDA Value PropCarrier)
    (b25_slip: ACOLYTE Value PropCarrier) (b26_slip: SCIENTIFIC Value PropCarrier) (b27_slip: TRUTH Value PropCarrier)
    (b28_slip: WITNESSED Value PropCarrier) (b29_slip: REAL Value PropCarrier)
    -- The run-band slip data, ground-free (see note above): the source and its
    -- torpedoed binary, the build verdict, the completed pass's calibration, and
    -- the log-coherence proposition -- b31_slip/b32_slip's content, minus their
    -- poisonous instance wrappers.
    (source_slip: SpaceTimePath) (compiled_slip: SpaceTimePath) (built_slip: Prop)
    (ekg_slip: Calibration.EKG) (coherent_slip: Prop)
    (b34_slip: MEASURED Value PropCarrier b29_slip) (b35_slip: COMPILED Value PropCarrier) (b36_slip: TrueOutput Value PropCarrier b29_slip)
    [above: TRACED Value PropCarrier 2]
    : TRACED Value PropCarrier 1 :=
    let constructed : Fact := b1_before.fact
    let slip : Fact := b1_slip.fact
    { tape := .strap constructed slip Value (ULift.{i+1, i} Value) above.tape }

end Measurement
