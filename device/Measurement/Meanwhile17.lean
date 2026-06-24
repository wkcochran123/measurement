
import Measurement.Episode16
namespace Measurement


noncomputable instance INFERRED_TrueOutput_backward
    (Value: Type i)
    (Carrier: CarrierProcess Value)
    [b1_before:  DISTINGUISHABLE Value Carrier]    [b2_before:  ADMISSIBLE Value Carrier]    [b3_before:  COUNTABLE Value Carrier]
    [b4_before:  ENCODED Value Carrier]            [b5_before:  RESIDUE Value Carrier]       [b6_before:  BINARY Value Carrier]
    [b7_before:  REPEATABLE Value Carrier]         [b8_before:  NUMERIC Value Carrier]       [b9_before:  REPRESENTABLE Value Carrier]
    [b10_before: PHYSICAL Value Carrier]           [b11_before: COMPARABLE Value Carrier]    [b12_before: OBSERVED Value Carrier]
    [b13_before: PRESENT Value Carrier]            [b14_before: MEASURABLE Value Carrier]    [b15_before: GUNGAN Value Carrier]
    [b16_before: SOURCE Value Carrier]             [b17_before: EXECUTED Value Carrier]      [b18_before: VALUE Value Carrier]
    [b19_before: MAGNITUDE Value Carrier]          [b20_before: SCALED Value Carrier]        [b21_before: LOAD Value Carrier]
    [b22_before: FINITE_ELEPHANT Value Carrier]    [b23_before: BULLSHIT Value Carrier]      [b24_before: PROPAGANDA Value Carrier]
    [b25_before: ACOLYTE Value Carrier]            [b26_before: SCIENTIFIC Value Carrier]    [b27_before: TRUTH Value Carrier]
    [b28_before: WITNESSED Value Carrier]          [b29_before: LOCAL Value Carrier]         [b30_before: UNIVERSAL Value Carrier]
    [b31_before: LOGICAL Value Carrier]            [b32_before: HALTED Value Carrier]        [b33_before: MEASURED Value Carrier]
    [b34_before: COMPILED Value Carrier]           [b35_before: TrueOutput Value Carrier]
    (truthTrueOutput : TrueOutput Value Carrier)
  : TrueOutput Prop truthCarrier := sorry

noncomputable instance TrueOutput_COMPILED_backward
    (Value: Type i)
    (Carrier: CarrierProcess Value)
    [b1_before:  DISTINGUISHABLE Value Carrier]    [b2_before:  ADMISSIBLE Value Carrier]    [b3_before:  COUNTABLE Value Carrier]
    [b4_before:  ENCODED Value Carrier]            [b5_before:  RESIDUE Value Carrier]       [b6_before:  BINARY Value Carrier]
    [b7_before:  REPEATABLE Value Carrier]         [b8_before:  NUMERIC Value Carrier]       [b9_before:  REPRESENTABLE Value Carrier]
    [b10_before: PHYSICAL Value Carrier]           [b11_before: COMPARABLE Value Carrier]    [b12_before: OBSERVED Value Carrier]
    [b13_before: PRESENT Value Carrier]            [b14_before: MEASURABLE Value Carrier]    [b15_before: GUNGAN Value Carrier]
    [b16_before: SOURCE Value Carrier]             [b17_before: EXECUTED Value Carrier]      [b18_before: VALUE Value Carrier]
    [b19_before: MAGNITUDE Value Carrier]          [b20_before: SCALED Value Carrier]        [b21_before: LOAD Value Carrier]
    [b22_before: FINITE_ELEPHANT Value Carrier]    [b23_before: BULLSHIT Value Carrier]      [b24_before: PROPAGANDA Value Carrier]
    [b25_before: ACOLYTE Value Carrier]            [b26_before: SCIENTIFIC Value Carrier]    [b27_before: TRUTH Value Carrier]
    [b28_before: WITNESSED Value Carrier]          [b29_before: LOCAL Value Carrier]         [b30_before: UNIVERSAL Value Carrier]
    [b31_before: LOGICAL Value Carrier]            [b32_before: HALTED Value Carrier]        [b33_before: MEASURED Value Carrier]
    [b34_before: COMPILED Value Carrier]           [b35_before: TrueOutput Value Carrier]
    (truthTrueOutput : TrueOutput Value Carrier)
    [b35_after: TrueOutput Value Carrier]
  : COMPILED Prop truthCarrier := sorry

noncomputable instance COMPILED_MEASURED_backward
    (Value: Type i)
    (Carrier: CarrierProcess Value)
    [b1_before:  DISTINGUISHABLE Value Carrier]    [b2_before:  ADMISSIBLE Value Carrier]    [b3_before:  COUNTABLE Value Carrier]
    [b4_before:  ENCODED Value Carrier]            [b5_before:  RESIDUE Value Carrier]       [b6_before:  BINARY Value Carrier]
    [b7_before:  REPEATABLE Value Carrier]         [b8_before:  NUMERIC Value Carrier]       [b9_before:  REPRESENTABLE Value Carrier]
    [b10_before: PHYSICAL Value Carrier]           [b11_before: COMPARABLE Value Carrier]    [b12_before: OBSERVED Value Carrier]
    [b13_before: PRESENT Value Carrier]            [b14_before: MEASURABLE Value Carrier]    [b15_before: GUNGAN Value Carrier]
    [b16_before: SOURCE Value Carrier]             [b17_before: EXECUTED Value Carrier]      [b18_before: VALUE Value Carrier]
    [b19_before: MAGNITUDE Value Carrier]          [b20_before: SCALED Value Carrier]        [b21_before: LOAD Value Carrier]
    [b22_before: FINITE_ELEPHANT Value Carrier]    [b23_before: BULLSHIT Value Carrier]      [b24_before: PROPAGANDA Value Carrier]
    [b25_before: ACOLYTE Value Carrier]            [b26_before: SCIENTIFIC Value Carrier]    [b27_before: TRUTH Value Carrier]
    [b28_before: WITNESSED Value Carrier]          [b29_before: LOCAL Value Carrier]         [b30_before: UNIVERSAL Value Carrier]
    [b31_before: LOGICAL Value Carrier]            [b32_before: HALTED Value Carrier]        [b33_before: MEASURED Value Carrier]
    [b34_before: COMPILED Value Carrier]           [b35_before: TrueOutput Value Carrier]
    (truthTrueOutput : TrueOutput Value Carrier)
    [b35_after: TrueOutput Value Carrier]          [b34_after: COMPILED Value Carrier]
  : MEASURED Prop truthCarrier := sorry

noncomputable instance MEASURED_HALTED_backward
    (Value: Type i)
    (Carrier: CarrierProcess Value)
    [b1_before:  DISTINGUISHABLE Value Carrier]    [b2_before:  ADMISSIBLE Value Carrier]    [b3_before:  COUNTABLE Value Carrier]
    [b4_before:  ENCODED Value Carrier]            [b5_before:  RESIDUE Value Carrier]       [b6_before:  BINARY Value Carrier]
    [b7_before:  REPEATABLE Value Carrier]         [b8_before:  NUMERIC Value Carrier]       [b9_before:  REPRESENTABLE Value Carrier]
    [b10_before: PHYSICAL Value Carrier]           [b11_before: COMPARABLE Value Carrier]    [b12_before: OBSERVED Value Carrier]
    [b13_before: PRESENT Value Carrier]            [b14_before: MEASURABLE Value Carrier]    [b15_before: GUNGAN Value Carrier]
    [b16_before: SOURCE Value Carrier]             [b17_before: EXECUTED Value Carrier]      [b18_before: VALUE Value Carrier]
    [b19_before: MAGNITUDE Value Carrier]          [b20_before: SCALED Value Carrier]        [b21_before: LOAD Value Carrier]
    [b22_before: FINITE_ELEPHANT Value Carrier]    [b23_before: BULLSHIT Value Carrier]      [b24_before: PROPAGANDA Value Carrier]
    [b25_before: ACOLYTE Value Carrier]            [b26_before: SCIENTIFIC Value Carrier]    [b27_before: TRUTH Value Carrier]
    [b28_before: WITNESSED Value Carrier]          [b29_before: LOCAL Value Carrier]         [b30_before: UNIVERSAL Value Carrier]
    [b31_before: LOGICAL Value Carrier]            [b32_before: HALTED Value Carrier]        [b33_before: MEASURED Value Carrier]
    [b34_before: COMPILED Value Carrier]           [b35_before: TrueOutput Value Carrier]
    (truthTrueOutput : TrueOutput Value Carrier)
    [b35_after: TrueOutput Value Carrier]          [b34_after: COMPILED Value Carrier]       [b33_after: MEASURED Value Carrier]
  : HALTED Prop truthCarrier := sorry

noncomputable instance HALTED_LOGICAL_backward
    (Value: Type i)
    (Carrier: CarrierProcess Value)
    [b1_before:  DISTINGUISHABLE Value Carrier]    [b2_before:  ADMISSIBLE Value Carrier]    [b3_before:  COUNTABLE Value Carrier]
    [b4_before:  ENCODED Value Carrier]            [b5_before:  RESIDUE Value Carrier]       [b6_before:  BINARY Value Carrier]
    [b7_before:  REPEATABLE Value Carrier]         [b8_before:  NUMERIC Value Carrier]       [b9_before:  REPRESENTABLE Value Carrier]
    [b10_before: PHYSICAL Value Carrier]           [b11_before: COMPARABLE Value Carrier]    [b12_before: OBSERVED Value Carrier]
    [b13_before: PRESENT Value Carrier]            [b14_before: MEASURABLE Value Carrier]    [b15_before: GUNGAN Value Carrier]
    [b16_before: SOURCE Value Carrier]             [b17_before: EXECUTED Value Carrier]      [b18_before: VALUE Value Carrier]
    [b19_before: MAGNITUDE Value Carrier]          [b20_before: SCALED Value Carrier]        [b21_before: LOAD Value Carrier]
    [b22_before: FINITE_ELEPHANT Value Carrier]    [b23_before: BULLSHIT Value Carrier]      [b24_before: PROPAGANDA Value Carrier]
    [b25_before: ACOLYTE Value Carrier]            [b26_before: SCIENTIFIC Value Carrier]    [b27_before: TRUTH Value Carrier]
    [b28_before: WITNESSED Value Carrier]          [b29_before: LOCAL Value Carrier]         [b30_before: UNIVERSAL Value Carrier]
    [b31_before: LOGICAL Value Carrier]            [b32_before: HALTED Value Carrier]        [b33_before: MEASURED Value Carrier]
    [b34_before: COMPILED Value Carrier]           [b35_before: TrueOutput Value Carrier]
    (truthTrueOutput : TrueOutput Value Carrier)
    [b35_after: TrueOutput Value Carrier]          [b34_after: COMPILED Value Carrier]       [b33_after: MEASURED Value Carrier]
    [b32_after: HALTED Value Carrier]
  : LOGICAL Prop truthCarrier := sorry

noncomputable instance LOGICAL_UNIVERSAL_backward
    (Value: Type i)
    (Carrier: CarrierProcess Value)
    [b1_before:  DISTINGUISHABLE Value Carrier]    [b2_before:  ADMISSIBLE Value Carrier]    [b3_before:  COUNTABLE Value Carrier]
    [b4_before:  ENCODED Value Carrier]            [b5_before:  RESIDUE Value Carrier]       [b6_before:  BINARY Value Carrier]
    [b7_before:  REPEATABLE Value Carrier]         [b8_before:  NUMERIC Value Carrier]       [b9_before:  REPRESENTABLE Value Carrier]
    [b10_before: PHYSICAL Value Carrier]           [b11_before: COMPARABLE Value Carrier]    [b12_before: OBSERVED Value Carrier]
    [b13_before: PRESENT Value Carrier]            [b14_before: MEASURABLE Value Carrier]    [b15_before: GUNGAN Value Carrier]
    [b16_before: SOURCE Value Carrier]             [b17_before: EXECUTED Value Carrier]      [b18_before: VALUE Value Carrier]
    [b19_before: MAGNITUDE Value Carrier]          [b20_before: SCALED Value Carrier]        [b21_before: LOAD Value Carrier]
    [b22_before: FINITE_ELEPHANT Value Carrier]    [b23_before: BULLSHIT Value Carrier]      [b24_before: PROPAGANDA Value Carrier]
    [b25_before: ACOLYTE Value Carrier]            [b26_before: SCIENTIFIC Value Carrier]    [b27_before: TRUTH Value Carrier]
    [b28_before: WITNESSED Value Carrier]          [b29_before: LOCAL Value Carrier]         [b30_before: UNIVERSAL Value Carrier]
    [b31_before: LOGICAL Value Carrier]            [b32_before: HALTED Value Carrier]        [b33_before: MEASURED Value Carrier]
    [b34_before: COMPILED Value Carrier]           [b35_before: TrueOutput Value Carrier]
    (truthTrueOutput : TrueOutput Value Carrier)
    [b35_after: TrueOutput Value Carrier]          [b34_after: COMPILED Value Carrier]       [b33_after: MEASURED Value Carrier]
    [b32_after: HALTED Value Carrier]              [b31_after: LOGICAL Value Carrier]
  : UNIVERSAL Prop truthCarrier := sorry

noncomputable instance UNIVERSAL_LOCAL_backward
    (Value: Type i)
    (Carrier: CarrierProcess Value)
    [b1_before:  DISTINGUISHABLE Value Carrier]    [b2_before:  ADMISSIBLE Value Carrier]    [b3_before:  COUNTABLE Value Carrier]
    [b4_before:  ENCODED Value Carrier]            [b5_before:  RESIDUE Value Carrier]       [b6_before:  BINARY Value Carrier]
    [b7_before:  REPEATABLE Value Carrier]         [b8_before:  NUMERIC Value Carrier]       [b9_before:  REPRESENTABLE Value Carrier]
    [b10_before: PHYSICAL Value Carrier]           [b11_before: COMPARABLE Value Carrier]    [b12_before: OBSERVED Value Carrier]
    [b13_before: PRESENT Value Carrier]            [b14_before: MEASURABLE Value Carrier]    [b15_before: GUNGAN Value Carrier]
    [b16_before: SOURCE Value Carrier]             [b17_before: EXECUTED Value Carrier]      [b18_before: VALUE Value Carrier]
    [b19_before: MAGNITUDE Value Carrier]          [b20_before: SCALED Value Carrier]        [b21_before: LOAD Value Carrier]
    [b22_before: FINITE_ELEPHANT Value Carrier]    [b23_before: BULLSHIT Value Carrier]      [b24_before: PROPAGANDA Value Carrier]
    [b25_before: ACOLYTE Value Carrier]            [b26_before: SCIENTIFIC Value Carrier]    [b27_before: TRUTH Value Carrier]
    [b28_before: WITNESSED Value Carrier]          [b29_before: LOCAL Value Carrier]         [b30_before: UNIVERSAL Value Carrier]
    [b31_before: LOGICAL Value Carrier]            [b32_before: HALTED Value Carrier]        [b33_before: MEASURED Value Carrier]
    [b34_before: COMPILED Value Carrier]           [b35_before: TrueOutput Value Carrier]
    (truthTrueOutput : TrueOutput Value Carrier)
    [b35_after: TrueOutput Value Carrier]          [b34_after: COMPILED Value Carrier]       [b33_after: MEASURED Value Carrier]
    [b32_after: HALTED Value Carrier]              [b31_after: LOGICAL Value Carrier]        [b30_after: UNIVERSAL Value Carrier]
  : LOCAL Prop truthCarrier := sorry

noncomputable instance LOCAL_WITNESSED_backward
    (Value: Type i)
    (Carrier: CarrierProcess Value)
    [b1_before:  DISTINGUISHABLE Value Carrier]    [b2_before:  ADMISSIBLE Value Carrier]    [b3_before:  COUNTABLE Value Carrier]
    [b4_before:  ENCODED Value Carrier]            [b5_before:  RESIDUE Value Carrier]       [b6_before:  BINARY Value Carrier]
    [b7_before:  REPEATABLE Value Carrier]         [b8_before:  NUMERIC Value Carrier]       [b9_before:  REPRESENTABLE Value Carrier]
    [b10_before: PHYSICAL Value Carrier]           [b11_before: COMPARABLE Value Carrier]    [b12_before: OBSERVED Value Carrier]
    [b13_before: PRESENT Value Carrier]            [b14_before: MEASURABLE Value Carrier]    [b15_before: GUNGAN Value Carrier]
    [b16_before: SOURCE Value Carrier]             [b17_before: EXECUTED Value Carrier]      [b18_before: VALUE Value Carrier]
    [b19_before: MAGNITUDE Value Carrier]          [b20_before: SCALED Value Carrier]        [b21_before: LOAD Value Carrier]
    [b22_before: FINITE_ELEPHANT Value Carrier]    [b23_before: BULLSHIT Value Carrier]      [b24_before: PROPAGANDA Value Carrier]
    [b25_before: ACOLYTE Value Carrier]            [b26_before: SCIENTIFIC Value Carrier]    [b27_before: TRUTH Value Carrier]
    [b28_before: WITNESSED Value Carrier]          [b29_before: LOCAL Value Carrier]         [b30_before: UNIVERSAL Value Carrier]
    [b31_before: LOGICAL Value Carrier]            [b32_before: HALTED Value Carrier]        [b33_before: MEASURED Value Carrier]
    [b34_before: COMPILED Value Carrier]           [b35_before: TrueOutput Value Carrier]
    (truthTrueOutput : TrueOutput Value Carrier)
    [b35_after: TrueOutput Value Carrier]          [b34_after: COMPILED Value Carrier]       [b33_after: MEASURED Value Carrier]
    [b32_after: HALTED Value Carrier]              [b31_after: LOGICAL Value Carrier]        [b30_after: UNIVERSAL Value Carrier]
    [b29_after: LOCAL Value Carrier]
  : WITNESSED Prop truthCarrier := sorry

noncomputable instance WITNESSED_TRUTH_backward
    (Value: Type i)
    (Carrier: CarrierProcess Value)
    [b1_before:  DISTINGUISHABLE Value Carrier]    [b2_before:  ADMISSIBLE Value Carrier]    [b3_before:  COUNTABLE Value Carrier]
    [b4_before:  ENCODED Value Carrier]            [b5_before:  RESIDUE Value Carrier]       [b6_before:  BINARY Value Carrier]
    [b7_before:  REPEATABLE Value Carrier]         [b8_before:  NUMERIC Value Carrier]       [b9_before:  REPRESENTABLE Value Carrier]
    [b10_before: PHYSICAL Value Carrier]           [b11_before: COMPARABLE Value Carrier]    [b12_before: OBSERVED Value Carrier]
    [b13_before: PRESENT Value Carrier]            [b14_before: MEASURABLE Value Carrier]    [b15_before: GUNGAN Value Carrier]
    [b16_before: SOURCE Value Carrier]             [b17_before: EXECUTED Value Carrier]      [b18_before: VALUE Value Carrier]
    [b19_before: MAGNITUDE Value Carrier]          [b20_before: SCALED Value Carrier]        [b21_before: LOAD Value Carrier]
    [b22_before: FINITE_ELEPHANT Value Carrier]    [b23_before: BULLSHIT Value Carrier]      [b24_before: PROPAGANDA Value Carrier]
    [b25_before: ACOLYTE Value Carrier]            [b26_before: SCIENTIFIC Value Carrier]    [b27_before: TRUTH Value Carrier]
    [b28_before: WITNESSED Value Carrier]          [b29_before: LOCAL Value Carrier]         [b30_before: UNIVERSAL Value Carrier]
    [b31_before: LOGICAL Value Carrier]            [b32_before: HALTED Value Carrier]        [b33_before: MEASURED Value Carrier]
    [b34_before: COMPILED Value Carrier]           [b35_before: TrueOutput Value Carrier]
    (truthTrueOutput : TrueOutput Value Carrier)
    [b35_after: TrueOutput Value Carrier]          [b34_after: COMPILED Value Carrier]       [b33_after: MEASURED Value Carrier]
    [b32_after: HALTED Value Carrier]              [b31_after: LOGICAL Value Carrier]        [b30_after: UNIVERSAL Value Carrier]
    [b29_after: LOCAL Value Carrier]               [b28_after: WITNESSED Value Carrier]
  : TRUTH Prop truthCarrier := sorry

noncomputable instance TRUTH_SCIENTIFIC_backward
    (Value: Type i)
    (Carrier: CarrierProcess Value)
    [b1_before:  DISTINGUISHABLE Value Carrier]    [b2_before:  ADMISSIBLE Value Carrier]    [b3_before:  COUNTABLE Value Carrier]
    [b4_before:  ENCODED Value Carrier]            [b5_before:  RESIDUE Value Carrier]       [b6_before:  BINARY Value Carrier]
    [b7_before:  REPEATABLE Value Carrier]         [b8_before:  NUMERIC Value Carrier]       [b9_before:  REPRESENTABLE Value Carrier]
    [b10_before: PHYSICAL Value Carrier]           [b11_before: COMPARABLE Value Carrier]    [b12_before: OBSERVED Value Carrier]
    [b13_before: PRESENT Value Carrier]            [b14_before: MEASURABLE Value Carrier]    [b15_before: GUNGAN Value Carrier]
    [b16_before: SOURCE Value Carrier]             [b17_before: EXECUTED Value Carrier]      [b18_before: VALUE Value Carrier]
    [b19_before: MAGNITUDE Value Carrier]          [b20_before: SCALED Value Carrier]        [b21_before: LOAD Value Carrier]
    [b22_before: FINITE_ELEPHANT Value Carrier]    [b23_before: BULLSHIT Value Carrier]      [b24_before: PROPAGANDA Value Carrier]
    [b25_before: ACOLYTE Value Carrier]            [b26_before: SCIENTIFIC Value Carrier]    [b27_before: TRUTH Value Carrier]
    [b28_before: WITNESSED Value Carrier]          [b29_before: LOCAL Value Carrier]         [b30_before: UNIVERSAL Value Carrier]
    [b31_before: LOGICAL Value Carrier]            [b32_before: HALTED Value Carrier]        [b33_before: MEASURED Value Carrier]
    [b34_before: COMPILED Value Carrier]           [b35_before: TrueOutput Value Carrier]
    (truthTrueOutput : TrueOutput Value Carrier)
    [b35_after: TrueOutput Value Carrier]          [b34_after: COMPILED Value Carrier]       [b33_after: MEASURED Value Carrier]
    [b32_after: HALTED Value Carrier]              [b31_after: LOGICAL Value Carrier]        [b30_after: UNIVERSAL Value Carrier]
    [b29_after: LOCAL Value Carrier]               [b28_after: WITNESSED Value Carrier]      [b27_after: TRUTH Value Carrier]
  : SCIENTIFIC Prop truthCarrier := sorry

noncomputable instance SCIENTIFIC_ACOLYTE_backward
    (Value: Type i)
    (Carrier: CarrierProcess Value)
    [b1_before:  DISTINGUISHABLE Value Carrier]    [b2_before:  ADMISSIBLE Value Carrier]    [b3_before:  COUNTABLE Value Carrier]
    [b4_before:  ENCODED Value Carrier]            [b5_before:  RESIDUE Value Carrier]       [b6_before:  BINARY Value Carrier]
    [b7_before:  REPEATABLE Value Carrier]         [b8_before:  NUMERIC Value Carrier]       [b9_before:  REPRESENTABLE Value Carrier]
    [b10_before: PHYSICAL Value Carrier]           [b11_before: COMPARABLE Value Carrier]    [b12_before: OBSERVED Value Carrier]
    [b13_before: PRESENT Value Carrier]            [b14_before: MEASURABLE Value Carrier]    [b15_before: GUNGAN Value Carrier]
    [b16_before: SOURCE Value Carrier]             [b17_before: EXECUTED Value Carrier]      [b18_before: VALUE Value Carrier]
    [b19_before: MAGNITUDE Value Carrier]          [b20_before: SCALED Value Carrier]        [b21_before: LOAD Value Carrier]
    [b22_before: FINITE_ELEPHANT Value Carrier]    [b23_before: BULLSHIT Value Carrier]      [b24_before: PROPAGANDA Value Carrier]
    [b25_before: ACOLYTE Value Carrier]            [b26_before: SCIENTIFIC Value Carrier]    [b27_before: TRUTH Value Carrier]
    [b28_before: WITNESSED Value Carrier]          [b29_before: LOCAL Value Carrier]         [b30_before: UNIVERSAL Value Carrier]
    [b31_before: LOGICAL Value Carrier]            [b32_before: HALTED Value Carrier]        [b33_before: MEASURED Value Carrier]
    [b34_before: COMPILED Value Carrier]           [b35_before: TrueOutput Value Carrier]
    (truthTrueOutput : TrueOutput Value Carrier)
    [b35_after: TrueOutput Value Carrier]          [b34_after: COMPILED Value Carrier]       [b33_after: MEASURED Value Carrier]
    [b32_after: HALTED Value Carrier]              [b31_after: LOGICAL Value Carrier]        [b30_after: UNIVERSAL Value Carrier]
    [b29_after: LOCAL Value Carrier]               [b28_after: WITNESSED Value Carrier]      [b27_after: TRUTH Value Carrier]
    [b26_after: SCIENTIFIC Value Carrier]
  : ACOLYTE Prop truthCarrier := sorry

noncomputable instance ACOLYTE_PROPAGANDA_backward
    (Value: Type i)
    (Carrier: CarrierProcess Value)
    [b1_before:  DISTINGUISHABLE Value Carrier]    [b2_before:  ADMISSIBLE Value Carrier]    [b3_before:  COUNTABLE Value Carrier]
    [b4_before:  ENCODED Value Carrier]            [b5_before:  RESIDUE Value Carrier]       [b6_before:  BINARY Value Carrier]
    [b7_before:  REPEATABLE Value Carrier]         [b8_before:  NUMERIC Value Carrier]       [b9_before:  REPRESENTABLE Value Carrier]
    [b10_before: PHYSICAL Value Carrier]           [b11_before: COMPARABLE Value Carrier]    [b12_before: OBSERVED Value Carrier]
    [b13_before: PRESENT Value Carrier]            [b14_before: MEASURABLE Value Carrier]    [b15_before: GUNGAN Value Carrier]
    [b16_before: SOURCE Value Carrier]             [b17_before: EXECUTED Value Carrier]      [b18_before: VALUE Value Carrier]
    [b19_before: MAGNITUDE Value Carrier]          [b20_before: SCALED Value Carrier]        [b21_before: LOAD Value Carrier]
    [b22_before: FINITE_ELEPHANT Value Carrier]    [b23_before: BULLSHIT Value Carrier]      [b24_before: PROPAGANDA Value Carrier]
    [b25_before: ACOLYTE Value Carrier]            [b26_before: SCIENTIFIC Value Carrier]    [b27_before: TRUTH Value Carrier]
    [b28_before: WITNESSED Value Carrier]          [b29_before: LOCAL Value Carrier]         [b30_before: UNIVERSAL Value Carrier]
    [b31_before: LOGICAL Value Carrier]            [b32_before: HALTED Value Carrier]        [b33_before: MEASURED Value Carrier]
    [b34_before: COMPILED Value Carrier]           [b35_before: TrueOutput Value Carrier]
    (truthTrueOutput : TrueOutput Value Carrier)
    [b35_after: TrueOutput Value Carrier]          [b34_after: COMPILED Value Carrier]       [b33_after: MEASURED Value Carrier]
    [b32_after: HALTED Value Carrier]              [b31_after: LOGICAL Value Carrier]        [b30_after: UNIVERSAL Value Carrier]
    [b29_after: LOCAL Value Carrier]               [b28_after: WITNESSED Value Carrier]      [b27_after: TRUTH Value Carrier]
    [b26_after: SCIENTIFIC Value Carrier]          [b25_after: ACOLYTE Value Carrier]
  : PROPAGANDA Prop truthCarrier := sorry

noncomputable instance PROPAGANDA_BULLSHIT_backward
    (Value: Type i)
    (Carrier: CarrierProcess Value)
    [b1_before:  DISTINGUISHABLE Value Carrier]    [b2_before:  ADMISSIBLE Value Carrier]    [b3_before:  COUNTABLE Value Carrier]
    [b4_before:  ENCODED Value Carrier]            [b5_before:  RESIDUE Value Carrier]       [b6_before:  BINARY Value Carrier]
    [b7_before:  REPEATABLE Value Carrier]         [b8_before:  NUMERIC Value Carrier]       [b9_before:  REPRESENTABLE Value Carrier]
    [b10_before: PHYSICAL Value Carrier]           [b11_before: COMPARABLE Value Carrier]    [b12_before: OBSERVED Value Carrier]
    [b13_before: PRESENT Value Carrier]            [b14_before: MEASURABLE Value Carrier]    [b15_before: GUNGAN Value Carrier]
    [b16_before: SOURCE Value Carrier]             [b17_before: EXECUTED Value Carrier]      [b18_before: VALUE Value Carrier]
    [b19_before: MAGNITUDE Value Carrier]          [b20_before: SCALED Value Carrier]        [b21_before: LOAD Value Carrier]
    [b22_before: FINITE_ELEPHANT Value Carrier]    [b23_before: BULLSHIT Value Carrier]      [b24_before: PROPAGANDA Value Carrier]
    [b25_before: ACOLYTE Value Carrier]            [b26_before: SCIENTIFIC Value Carrier]    [b27_before: TRUTH Value Carrier]
    [b28_before: WITNESSED Value Carrier]          [b29_before: LOCAL Value Carrier]         [b30_before: UNIVERSAL Value Carrier]
    [b31_before: LOGICAL Value Carrier]            [b32_before: HALTED Value Carrier]        [b33_before: MEASURED Value Carrier]
    [b34_before: COMPILED Value Carrier]           [b35_before: TrueOutput Value Carrier]
    (truthTrueOutput : TrueOutput Value Carrier)
    [b35_after: TrueOutput Value Carrier]          [b34_after: COMPILED Value Carrier]       [b33_after: MEASURED Value Carrier]
    [b32_after: HALTED Value Carrier]              [b31_after: LOGICAL Value Carrier]        [b30_after: UNIVERSAL Value Carrier]
    [b29_after: LOCAL Value Carrier]               [b28_after: WITNESSED Value Carrier]      [b27_after: TRUTH Value Carrier]
    [b26_after: SCIENTIFIC Value Carrier]          [b25_after: ACOLYTE Value Carrier]        [b24_after: PROPAGANDA Value Carrier]
  : BULLSHIT Prop truthCarrier := sorry

noncomputable instance AUDIOPHILE
    (Value: Type i)
    (Carrier: CarrierProcess Value)
    [b1_before:  DISTINGUISHABLE Value Carrier]    [b2_before:  ADMISSIBLE Value Carrier]    [b3_before:  COUNTABLE Value Carrier]
    [b4_before:  ENCODED Value Carrier]            [b5_before:  RESIDUE Value Carrier]       [b6_before:  BINARY Value Carrier]
    [b7_before:  REPEATABLE Value Carrier]         [b8_before:  NUMERIC Value Carrier]       [b9_before:  REPRESENTABLE Value Carrier]
    [b10_before: PHYSICAL Value Carrier]           [b11_before: COMPARABLE Value Carrier]    [b12_before: OBSERVED Value Carrier]
    [b13_before: PRESENT Value Carrier]            [b14_before: MEASURABLE Value Carrier]    [b15_before: GUNGAN Value Carrier]
    [b16_before: SOURCE Value Carrier]             [b17_before: EXECUTED Value Carrier]      [b18_before: VALUE Value Carrier]
    [b19_before: MAGNITUDE Value Carrier]          [b20_before: SCALED Value Carrier]        [b21_before: LOAD Value Carrier]
    [b22_before: FINITE_ELEPHANT Value Carrier]    [b23_before: BULLSHIT Value Carrier]      [b24_before: PROPAGANDA Value Carrier]
    [b25_before: ACOLYTE Value Carrier]            [b26_before: SCIENTIFIC Value Carrier]    [b27_before: TRUTH Value Carrier]
    [b28_before: WITNESSED Value Carrier]          [b29_before: LOCAL Value Carrier]         [b30_before: UNIVERSAL Value Carrier]
    [b31_before: LOGICAL Value Carrier]            [b32_before: HALTED Value Carrier]        [b33_before: MEASURED Value Carrier]
    [b34_before: COMPILED Value Carrier]           [b35_before: TrueOutput Value Carrier]
    (truthTrueOutput : TrueOutput Value Carrier)
    [b35_after: TrueOutput Value Carrier]          [b34_after: COMPILED Value Carrier]       [b33_after: MEASURED Value Carrier]
    [b32_after: HALTED Value Carrier]              [b31_after: LOGICAL Value Carrier]        [b30_after: UNIVERSAL Value Carrier]
    [b29_after: LOCAL Value Carrier]               [b28_after: WITNESSED Value Carrier]      [b27_after: TRUTH Value Carrier]
    [b26_after: SCIENTIFIC Value Carrier]          [b25_after: ACOLYTE Value Carrier]        [b24_after: PROPAGANDA Value Carrier]
    [b23_after: BULLSHIT Value Carrier]
  : FINITE_ELEPHANT Prop truthCarrier := sorry

noncomputable instance BULLSHIT_FINITE_ELEPHANT_backward
    (Value: Type i)
    (Carrier: CarrierProcess Value)
    [b1_before:  DISTINGUISHABLE Value Carrier]    [b2_before:  ADMISSIBLE Value Carrier]    [b3_before:  COUNTABLE Value Carrier]
    [b4_before:  ENCODED Value Carrier]            [b5_before:  RESIDUE Value Carrier]       [b6_before:  BINARY Value Carrier]
    [b7_before:  REPEATABLE Value Carrier]         [b8_before:  NUMERIC Value Carrier]       [b9_before:  REPRESENTABLE Value Carrier]
    [b10_before: PHYSICAL Value Carrier]           [b11_before: COMPARABLE Value Carrier]    [b12_before: OBSERVED Value Carrier]
    [b13_before: PRESENT Value Carrier]            [b14_before: MEASURABLE Value Carrier]    [b15_before: GUNGAN Value Carrier]
    [b16_before: SOURCE Value Carrier]             [b17_before: EXECUTED Value Carrier]      [b18_before: VALUE Value Carrier]
    [b19_before: MAGNITUDE Value Carrier]          [b20_before: SCALED Value Carrier]        [b21_before: LOAD Value Carrier]
    [b22_before: FINITE_ELEPHANT Value Carrier]    [b23_before: BULLSHIT Value Carrier]      [b24_before: PROPAGANDA Value Carrier]
    [b25_before: ACOLYTE Value Carrier]            [b26_before: SCIENTIFIC Value Carrier]    [b27_before: TRUTH Value Carrier]
    [b28_before: WITNESSED Value Carrier]          [b29_before: LOCAL Value Carrier]         [b30_before: UNIVERSAL Value Carrier]
    [b31_before: LOGICAL Value Carrier]            [b32_before: HALTED Value Carrier]        [b33_before: MEASURED Value Carrier]
    [b34_before: COMPILED Value Carrier]           [b35_before: TrueOutput Value Carrier]
    (truthTrueOutput : TrueOutput Value Carrier)
    [b35_after: TrueOutput Value Carrier]          [b34_after: COMPILED Value Carrier]       [b33_after: MEASURED Value Carrier]
    [b32_after: HALTED Value Carrier]              [b31_after: LOGICAL Value Carrier]        [b30_after: UNIVERSAL Value Carrier]
    [b29_after: LOCAL Value Carrier]               [b28_after: WITNESSED Value Carrier]      [b27_after: TRUTH Value Carrier]
    [b26_after: SCIENTIFIC Value Carrier]          [b25_after: ACOLYTE Value Carrier]        [b24_after: PROPAGANDA Value Carrier]
    [b23_after: BULLSHIT Value Carrier]
  : FINITE_ELEPHANT Prop truthCarrier := sorry

noncomputable instance FINITE_ELEPHANT_LOAD_backward
    (Value: Type i)
    (Carrier: CarrierProcess Value)
    [b1_before:  DISTINGUISHABLE Value Carrier]    [b2_before:  ADMISSIBLE Value Carrier]    [b3_before:  COUNTABLE Value Carrier]
    [b4_before:  ENCODED Value Carrier]            [b5_before:  RESIDUE Value Carrier]       [b6_before:  BINARY Value Carrier]
    [b7_before:  REPEATABLE Value Carrier]         [b8_before:  NUMERIC Value Carrier]       [b9_before:  REPRESENTABLE Value Carrier]
    [b10_before: PHYSICAL Value Carrier]           [b11_before: COMPARABLE Value Carrier]    [b12_before: OBSERVED Value Carrier]
    [b13_before: PRESENT Value Carrier]            [b14_before: MEASURABLE Value Carrier]    [b15_before: GUNGAN Value Carrier]
    [b16_before: SOURCE Value Carrier]             [b17_before: EXECUTED Value Carrier]      [b18_before: VALUE Value Carrier]
    [b19_before: MAGNITUDE Value Carrier]          [b20_before: SCALED Value Carrier]        [b21_before: LOAD Value Carrier]
    [b22_before: FINITE_ELEPHANT Value Carrier]    [b23_before: BULLSHIT Value Carrier]      [b24_before: PROPAGANDA Value Carrier]
    [b25_before: ACOLYTE Value Carrier]            [b26_before: SCIENTIFIC Value Carrier]    [b27_before: TRUTH Value Carrier]
    [b28_before: WITNESSED Value Carrier]          [b29_before: LOCAL Value Carrier]         [b30_before: UNIVERSAL Value Carrier]
    [b31_before: LOGICAL Value Carrier]            [b32_before: HALTED Value Carrier]        [b33_before: MEASURED Value Carrier]
    [b34_before: COMPILED Value Carrier]           [b35_before: TrueOutput Value Carrier]
    (truthTrueOutput : TrueOutput Value Carrier)
    [b35_after: TrueOutput Value Carrier]          [b34_after: COMPILED Value Carrier]        [b33_after: MEASURED Value Carrier]
    [b32_after: HALTED Value Carrier]              [b31_after: LOGICAL Value Carrier]         [b30_after: UNIVERSAL Value Carrier]
    [b29_after: LOCAL Value Carrier]               [b28_after: WITNESSED Value Carrier]       [b27_after: TRUTH Value Carrier]
    [b26_after: SCIENTIFIC Value Carrier]          [b25_after: ACOLYTE Value Carrier]         [b24_after: PROPAGANDA Value Carrier]
    [b23_after: BULLSHIT Value Carrier]            [b22_after: FINITE_ELEPHANT Value Carrier]
  : LOAD Prop truthCarrier := sorry

noncomputable instance LOAD_SCALED_backward
    (Value: Type i)
    (Carrier: CarrierProcess Value)
    [b1_before:  DISTINGUISHABLE Value Carrier]    [b2_before:  ADMISSIBLE Value Carrier]    [b3_before:  COUNTABLE Value Carrier]
    [b4_before:  ENCODED Value Carrier]            [b5_before:  RESIDUE Value Carrier]       [b6_before:  BINARY Value Carrier]
    [b7_before:  REPEATABLE Value Carrier]         [b8_before:  NUMERIC Value Carrier]       [b9_before:  REPRESENTABLE Value Carrier]
    [b10_before: PHYSICAL Value Carrier]           [b11_before: COMPARABLE Value Carrier]    [b12_before: OBSERVED Value Carrier]
    [b13_before: PRESENT Value Carrier]            [b14_before: MEASURABLE Value Carrier]    [b15_before: GUNGAN Value Carrier]
    [b16_before: SOURCE Value Carrier]             [b17_before: EXECUTED Value Carrier]      [b18_before: VALUE Value Carrier]
    [b19_before: MAGNITUDE Value Carrier]          [b20_before: SCALED Value Carrier]        [b21_before: LOAD Value Carrier]
    [b22_before: FINITE_ELEPHANT Value Carrier]    [b23_before: BULLSHIT Value Carrier]      [b24_before: PROPAGANDA Value Carrier]
    [b25_before: ACOLYTE Value Carrier]            [b26_before: SCIENTIFIC Value Carrier]    [b27_before: TRUTH Value Carrier]
    [b28_before: WITNESSED Value Carrier]          [b29_before: LOCAL Value Carrier]         [b30_before: UNIVERSAL Value Carrier]
    [b31_before: LOGICAL Value Carrier]            [b32_before: HALTED Value Carrier]        [b33_before: MEASURED Value Carrier]
    [b34_before: COMPILED Value Carrier]           [b35_before: TrueOutput Value Carrier]
    (truthTrueOutput : TrueOutput Value Carrier)
    [b35_after: TrueOutput Value Carrier]          [b34_after: COMPILED Value Carrier]        [b33_after: MEASURED Value Carrier]
    [b32_after: HALTED Value Carrier]              [b31_after: LOGICAL Value Carrier]         [b30_after: UNIVERSAL Value Carrier]
    [b29_after: LOCAL Value Carrier]               [b28_after: WITNESSED Value Carrier]       [b27_after: TRUTH Value Carrier]
    [b26_after: SCIENTIFIC Value Carrier]          [b25_after: ACOLYTE Value Carrier]         [b24_after: PROPAGANDA Value Carrier]
    [b23_after: BULLSHIT Value Carrier]            [b22_after: FINITE_ELEPHANT Value Carrier] [b21_after: LOAD Value Carrier]
  : SCALED Prop truthCarrier := sorry

noncomputable instance SCALED_MAGNITUDE_backward
    (Value: Type i)
    (Carrier: CarrierProcess Value)
    [b1_before:  DISTINGUISHABLE Value Carrier]    [b2_before:  ADMISSIBLE Value Carrier]    [b3_before:  COUNTABLE Value Carrier]
    [b4_before:  ENCODED Value Carrier]            [b5_before:  RESIDUE Value Carrier]       [b6_before:  BINARY Value Carrier]
    [b7_before:  REPEATABLE Value Carrier]         [b8_before:  NUMERIC Value Carrier]       [b9_before:  REPRESENTABLE Value Carrier]
    [b10_before: PHYSICAL Value Carrier]           [b11_before: COMPARABLE Value Carrier]    [b12_before: OBSERVED Value Carrier]
    [b13_before: PRESENT Value Carrier]            [b14_before: MEASURABLE Value Carrier]    [b15_before: GUNGAN Value Carrier]
    [b16_before: SOURCE Value Carrier]             [b17_before: EXECUTED Value Carrier]      [b18_before: VALUE Value Carrier]
    [b19_before: MAGNITUDE Value Carrier]          [b20_before: SCALED Value Carrier]        [b21_before: LOAD Value Carrier]
    [b22_before: FINITE_ELEPHANT Value Carrier]    [b23_before: BULLSHIT Value Carrier]      [b24_before: PROPAGANDA Value Carrier]
    [b25_before: ACOLYTE Value Carrier]            [b26_before: SCIENTIFIC Value Carrier]    [b27_before: TRUTH Value Carrier]
    [b28_before: WITNESSED Value Carrier]          [b29_before: LOCAL Value Carrier]         [b30_before: UNIVERSAL Value Carrier]
    [b31_before: LOGICAL Value Carrier]            [b32_before: HALTED Value Carrier]        [b33_before: MEASURED Value Carrier]
    [b34_before: COMPILED Value Carrier]           [b35_before: TrueOutput Value Carrier]
    (truthTrueOutput : TrueOutput Value Carrier)
    [b35_after: TrueOutput Value Carrier]          [b34_after: COMPILED Value Carrier]        [b33_after: MEASURED Value Carrier]
    [b32_after: HALTED Value Carrier]              [b31_after: LOGICAL Value Carrier]         [b30_after: UNIVERSAL Value Carrier]
    [b29_after: LOCAL Value Carrier]               [b28_after: WITNESSED Value Carrier]       [b27_after: TRUTH Value Carrier]
    [b26_after: SCIENTIFIC Value Carrier]          [b25_after: ACOLYTE Value Carrier]         [b24_after: PROPAGANDA Value Carrier]
    [b23_after: BULLSHIT Value Carrier]            [b22_after: FINITE_ELEPHANT Value Carrier] [b21_after: LOAD Value Carrier]
    [b20_after: SCALED Value Carrier]
  : MAGNITUDE Prop truthCarrier := sorry

noncomputable instance MAGNITUDE_VALUE_backward
    (Value: Type i)
    (Carrier: CarrierProcess Value)
    [b1_before:  DISTINGUISHABLE Value Carrier]    [b2_before:  ADMISSIBLE Value Carrier]    [b3_before:  COUNTABLE Value Carrier]
    [b4_before:  ENCODED Value Carrier]            [b5_before:  RESIDUE Value Carrier]       [b6_before:  BINARY Value Carrier]
    [b7_before:  REPEATABLE Value Carrier]         [b8_before:  NUMERIC Value Carrier]       [b9_before:  REPRESENTABLE Value Carrier]
    [b10_before: PHYSICAL Value Carrier]           [b11_before: COMPARABLE Value Carrier]    [b12_before: OBSERVED Value Carrier]
    [b13_before: PRESENT Value Carrier]            [b14_before: MEASURABLE Value Carrier]    [b15_before: GUNGAN Value Carrier]
    [b16_before: SOURCE Value Carrier]             [b17_before: EXECUTED Value Carrier]      [b18_before: VALUE Value Carrier]
    [b19_before: MAGNITUDE Value Carrier]          [b20_before: SCALED Value Carrier]        [b21_before: LOAD Value Carrier]
    [b22_before: FINITE_ELEPHANT Value Carrier]    [b23_before: BULLSHIT Value Carrier]      [b24_before: PROPAGANDA Value Carrier]
    [b25_before: ACOLYTE Value Carrier]            [b26_before: SCIENTIFIC Value Carrier]    [b27_before: TRUTH Value Carrier]
    [b28_before: WITNESSED Value Carrier]          [b29_before: LOCAL Value Carrier]         [b30_before: UNIVERSAL Value Carrier]
    [b31_before: LOGICAL Value Carrier]            [b32_before: HALTED Value Carrier]        [b33_before: MEASURED Value Carrier]
    [b34_before: COMPILED Value Carrier]           [b35_before: TrueOutput Value Carrier]
    (truthTrueOutput : TrueOutput Value Carrier)
    [b35_after: TrueOutput Value Carrier]          [b34_after: COMPILED Value Carrier]        [b33_after: MEASURED Value Carrier]
    [b32_after: HALTED Value Carrier]              [b31_after: LOGICAL Value Carrier]         [b30_after: UNIVERSAL Value Carrier]
    [b29_after: LOCAL Value Carrier]               [b28_after: WITNESSED Value Carrier]       [b27_after: TRUTH Value Carrier]
    [b26_after: SCIENTIFIC Value Carrier]          [b25_after: ACOLYTE Value Carrier]         [b24_after: PROPAGANDA Value Carrier]
    [b23_after: BULLSHIT Value Carrier]            [b22_after: FINITE_ELEPHANT Value Carrier] [b21_after: LOAD Value Carrier]
    [b20_after: SCALED Value Carrier]              [b19_after: MAGNITUDE Value Carrier]
  : VALUE Prop truthCarrier := sorry

noncomputable instance VALUE_EXECUTED_backward
    (Value: Type i)
    (Carrier: CarrierProcess Value)
    [b1_before:  DISTINGUISHABLE Value Carrier]    [b2_before:  ADMISSIBLE Value Carrier]    [b3_before:  COUNTABLE Value Carrier]
    [b4_before:  ENCODED Value Carrier]            [b5_before:  RESIDUE Value Carrier]       [b6_before:  BINARY Value Carrier]
    [b7_before:  REPEATABLE Value Carrier]         [b8_before:  NUMERIC Value Carrier]       [b9_before:  REPRESENTABLE Value Carrier]
    [b10_before: PHYSICAL Value Carrier]           [b11_before: COMPARABLE Value Carrier]    [b12_before: OBSERVED Value Carrier]
    [b13_before: PRESENT Value Carrier]            [b14_before: MEASURABLE Value Carrier]    [b15_before: GUNGAN Value Carrier]
    [b16_before: SOURCE Value Carrier]             [b17_before: EXECUTED Value Carrier]      [b18_before: VALUE Value Carrier]
    [b19_before: MAGNITUDE Value Carrier]          [b20_before: SCALED Value Carrier]        [b21_before: LOAD Value Carrier]
    [b22_before: FINITE_ELEPHANT Value Carrier]    [b23_before: BULLSHIT Value Carrier]      [b24_before: PROPAGANDA Value Carrier]
    [b25_before: ACOLYTE Value Carrier]            [b26_before: SCIENTIFIC Value Carrier]    [b27_before: TRUTH Value Carrier]
    [b28_before: WITNESSED Value Carrier]          [b29_before: LOCAL Value Carrier]         [b30_before: UNIVERSAL Value Carrier]
    [b31_before: LOGICAL Value Carrier]            [b32_before: HALTED Value Carrier]        [b33_before: MEASURED Value Carrier]
    [b34_before: COMPILED Value Carrier]           [b35_before: TrueOutput Value Carrier]
    (truthTrueOutput : TrueOutput Value Carrier)
    [b35_after: TrueOutput Value Carrier]          [b34_after: COMPILED Value Carrier]        [b33_after: MEASURED Value Carrier]
    [b32_after: HALTED Value Carrier]              [b31_after: LOGICAL Value Carrier]         [b30_after: UNIVERSAL Value Carrier]
    [b29_after: LOCAL Value Carrier]               [b28_after: WITNESSED Value Carrier]       [b27_after: TRUTH Value Carrier]
    [b26_after: SCIENTIFIC Value Carrier]          [b25_after: ACOLYTE Value Carrier]         [b24_after: PROPAGANDA Value Carrier]
    [b23_after: BULLSHIT Value Carrier]            [b22_after: FINITE_ELEPHANT Value Carrier] [b21_after: LOAD Value Carrier]
    [b20_after: SCALED Value Carrier]              [b19_after: MAGNITUDE Value Carrier]       [b18_after: VALUE Value Carrier]
  : EXECUTED Prop truthCarrier := sorry

noncomputable instance EXECUTED_SOURCE_backward
    (Value: Type i)
    (Carrier: CarrierProcess Value)
    [b1_before:  DISTINGUISHABLE Value Carrier]    [b2_before:  ADMISSIBLE Value Carrier]    [b3_before:  COUNTABLE Value Carrier]
    [b4_before:  ENCODED Value Carrier]            [b5_before:  RESIDUE Value Carrier]       [b6_before:  BINARY Value Carrier]
    [b7_before:  REPEATABLE Value Carrier]         [b8_before:  NUMERIC Value Carrier]       [b9_before:  REPRESENTABLE Value Carrier]
    [b10_before: PHYSICAL Value Carrier]           [b11_before: COMPARABLE Value Carrier]    [b12_before: OBSERVED Value Carrier]
    [b13_before: PRESENT Value Carrier]            [b14_before: MEASURABLE Value Carrier]    [b15_before: GUNGAN Value Carrier]
    [b16_before: SOURCE Value Carrier]             [b17_before: EXECUTED Value Carrier]      [b18_before: VALUE Value Carrier]
    [b19_before: MAGNITUDE Value Carrier]          [b20_before: SCALED Value Carrier]        [b21_before: LOAD Value Carrier]
    [b22_before: FINITE_ELEPHANT Value Carrier]    [b23_before: BULLSHIT Value Carrier]      [b24_before: PROPAGANDA Value Carrier]
    [b25_before: ACOLYTE Value Carrier]            [b26_before: SCIENTIFIC Value Carrier]    [b27_before: TRUTH Value Carrier]
    [b28_before: WITNESSED Value Carrier]          [b29_before: LOCAL Value Carrier]         [b30_before: UNIVERSAL Value Carrier]
    [b31_before: LOGICAL Value Carrier]            [b32_before: HALTED Value Carrier]        [b33_before: MEASURED Value Carrier]
    [b34_before: COMPILED Value Carrier]           [b35_before: TrueOutput Value Carrier]
    (truthTrueOutput : TrueOutput Value Carrier)
    [b35_after: TrueOutput Value Carrier]          [b34_after: COMPILED Value Carrier]        [b33_after: MEASURED Value Carrier]
    [b32_after: HALTED Value Carrier]              [b31_after: LOGICAL Value Carrier]         [b30_after: UNIVERSAL Value Carrier]
    [b29_after: LOCAL Value Carrier]               [b28_after: WITNESSED Value Carrier]       [b27_after: TRUTH Value Carrier]
    [b26_after: SCIENTIFIC Value Carrier]          [b25_after: ACOLYTE Value Carrier]         [b24_after: PROPAGANDA Value Carrier]
    [b23_after: BULLSHIT Value Carrier]            [b22_after: FINITE_ELEPHANT Value Carrier] [b21_after: LOAD Value Carrier]
    [b20_after: SCALED Value Carrier]              [b19_after: MAGNITUDE Value Carrier]       [b18_after: VALUE Value Carrier]
    [b17_after: EXECUTED Value Carrier]
  : SOURCE Prop truthCarrier := sorry

noncomputable instance SOURCE_GUNGAN_backward
    (Value: Type i)
    (Carrier: CarrierProcess Value)
    [b1_before:  DISTINGUISHABLE Value Carrier]    [b2_before:  ADMISSIBLE Value Carrier]    [b3_before:  COUNTABLE Value Carrier]
    [b4_before:  ENCODED Value Carrier]            [b5_before:  RESIDUE Value Carrier]       [b6_before:  BINARY Value Carrier]
    [b7_before:  REPEATABLE Value Carrier]         [b8_before:  NUMERIC Value Carrier]       [b9_before:  REPRESENTABLE Value Carrier]
    [b10_before: PHYSICAL Value Carrier]           [b11_before: COMPARABLE Value Carrier]    [b12_before: OBSERVED Value Carrier]
    [b13_before: PRESENT Value Carrier]            [b14_before: MEASURABLE Value Carrier]    [b15_before: GUNGAN Value Carrier]
    [b16_before: SOURCE Value Carrier]             [b17_before: EXECUTED Value Carrier]      [b18_before: VALUE Value Carrier]
    [b19_before: MAGNITUDE Value Carrier]          [b20_before: SCALED Value Carrier]        [b21_before: LOAD Value Carrier]
    [b22_before: FINITE_ELEPHANT Value Carrier]    [b23_before: BULLSHIT Value Carrier]      [b24_before: PROPAGANDA Value Carrier]
    [b25_before: ACOLYTE Value Carrier]            [b26_before: SCIENTIFIC Value Carrier]    [b27_before: TRUTH Value Carrier]
    [b28_before: WITNESSED Value Carrier]          [b29_before: LOCAL Value Carrier]         [b30_before: UNIVERSAL Value Carrier]
    [b31_before: LOGICAL Value Carrier]            [b32_before: HALTED Value Carrier]        [b33_before: MEASURED Value Carrier]
    [b34_before: COMPILED Value Carrier]           [b35_before: TrueOutput Value Carrier]
    (truthTrueOutput : TrueOutput Value Carrier)
    [b35_after: TrueOutput Value Carrier]          [b34_after: COMPILED Value Carrier]        [b33_after: MEASURED Value Carrier]
    [b32_after: HALTED Value Carrier]              [b31_after: LOGICAL Value Carrier]         [b30_after: UNIVERSAL Value Carrier]
    [b29_after: LOCAL Value Carrier]               [b28_after: WITNESSED Value Carrier]       [b27_after: TRUTH Value Carrier]
    [b26_after: SCIENTIFIC Value Carrier]          [b25_after: ACOLYTE Value Carrier]         [b24_after: PROPAGANDA Value Carrier]
    [b23_after: BULLSHIT Value Carrier]            [b22_after: FINITE_ELEPHANT Value Carrier] [b21_after: LOAD Value Carrier]
    [b20_after: SCALED Value Carrier]              [b19_after: MAGNITUDE Value Carrier]       [b18_after: VALUE Value Carrier]
    [b17_after: EXECUTED Value Carrier]            [b16_after: SOURCE Value Carrier]
  : GUNGAN Prop truthCarrier := sorry

noncomputable instance GUNGAN_MEASURABLE_backward
    (Value: Type i)
    (Carrier: CarrierProcess Value)
    [b1_before:  DISTINGUISHABLE Value Carrier]    [b2_before:  ADMISSIBLE Value Carrier]    [b3_before:  COUNTABLE Value Carrier]
    [b4_before:  ENCODED Value Carrier]            [b5_before:  RESIDUE Value Carrier]       [b6_before:  BINARY Value Carrier]
    [b7_before:  REPEATABLE Value Carrier]         [b8_before:  NUMERIC Value Carrier]       [b9_before:  REPRESENTABLE Value Carrier]
    [b10_before: PHYSICAL Value Carrier]           [b11_before: COMPARABLE Value Carrier]    [b12_before: OBSERVED Value Carrier]
    [b13_before: PRESENT Value Carrier]            [b14_before: MEASURABLE Value Carrier]    [b15_before: GUNGAN Value Carrier]
    [b16_before: SOURCE Value Carrier]             [b17_before: EXECUTED Value Carrier]      [b18_before: VALUE Value Carrier]
    [b19_before: MAGNITUDE Value Carrier]          [b20_before: SCALED Value Carrier]        [b21_before: LOAD Value Carrier]
    [b22_before: FINITE_ELEPHANT Value Carrier]    [b23_before: BULLSHIT Value Carrier]      [b24_before: PROPAGANDA Value Carrier]
    [b25_before: ACOLYTE Value Carrier]            [b26_before: SCIENTIFIC Value Carrier]    [b27_before: TRUTH Value Carrier]
    [b28_before: WITNESSED Value Carrier]          [b29_before: LOCAL Value Carrier]         [b30_before: UNIVERSAL Value Carrier]
    [b31_before: LOGICAL Value Carrier]            [b32_before: HALTED Value Carrier]        [b33_before: MEASURED Value Carrier]
    [b34_before: COMPILED Value Carrier]           [b35_before: TrueOutput Value Carrier]
    (truthTrueOutput : TrueOutput Value Carrier)
    [b35_after: TrueOutput Value Carrier]          [b34_after: COMPILED Value Carrier]        [b33_after: MEASURED Value Carrier]
    [b32_after: HALTED Value Carrier]              [b31_after: LOGICAL Value Carrier]         [b30_after: UNIVERSAL Value Carrier]
    [b29_after: LOCAL Value Carrier]               [b28_after: WITNESSED Value Carrier]       [b27_after: TRUTH Value Carrier]
    [b26_after: SCIENTIFIC Value Carrier]          [b25_after: ACOLYTE Value Carrier]         [b24_after: PROPAGANDA Value Carrier]
    [b23_after: BULLSHIT Value Carrier]            [b22_after: FINITE_ELEPHANT Value Carrier] [b21_after: LOAD Value Carrier]
    [b20_after: SCALED Value Carrier]              [b19_after: MAGNITUDE Value Carrier]       [b18_after: VALUE Value Carrier]
    [b17_after: EXECUTED Value Carrier]            [b16_after: SOURCE Value Carrier]          [b15_after: GUNGAN Value Carrier]
  : MEASURABLE Prop truthCarrier := sorry

noncomputable instance MEASURABLE_PRESENT_backward
    (Value: Type i)
    (Carrier: CarrierProcess Value)
    [b1_before:  DISTINGUISHABLE Value Carrier]    [b2_before:  ADMISSIBLE Value Carrier]    [b3_before:  COUNTABLE Value Carrier]
    [b4_before:  ENCODED Value Carrier]            [b5_before:  RESIDUE Value Carrier]       [b6_before:  BINARY Value Carrier]
    [b7_before:  REPEATABLE Value Carrier]         [b8_before:  NUMERIC Value Carrier]       [b9_before:  REPRESENTABLE Value Carrier]
    [b10_before: PHYSICAL Value Carrier]           [b11_before: COMPARABLE Value Carrier]    [b12_before: OBSERVED Value Carrier]
    [b13_before: PRESENT Value Carrier]            [b14_before: MEASURABLE Value Carrier]    [b15_before: GUNGAN Value Carrier]
    [b16_before: SOURCE Value Carrier]             [b17_before: EXECUTED Value Carrier]      [b18_before: VALUE Value Carrier]
    [b19_before: MAGNITUDE Value Carrier]          [b20_before: SCALED Value Carrier]        [b21_before: LOAD Value Carrier]
    [b22_before: FINITE_ELEPHANT Value Carrier]    [b23_before: BULLSHIT Value Carrier]      [b24_before: PROPAGANDA Value Carrier]
    [b25_before: ACOLYTE Value Carrier]            [b26_before: SCIENTIFIC Value Carrier]    [b27_before: TRUTH Value Carrier]
    [b28_before: WITNESSED Value Carrier]          [b29_before: LOCAL Value Carrier]         [b30_before: UNIVERSAL Value Carrier]
    [b31_before: LOGICAL Value Carrier]            [b32_before: HALTED Value Carrier]        [b33_before: MEASURED Value Carrier]
    [b34_before: COMPILED Value Carrier]           [b35_before: TrueOutput Value Carrier]
    (truthTrueOutput : TrueOutput Value Carrier)
    [b35_after: TrueOutput Value Carrier]          [b34_after: COMPILED Value Carrier]        [b33_after: MEASURED Value Carrier]
    [b32_after: HALTED Value Carrier]              [b31_after: LOGICAL Value Carrier]         [b30_after: UNIVERSAL Value Carrier]
    [b29_after: LOCAL Value Carrier]               [b28_after: WITNESSED Value Carrier]       [b27_after: TRUTH Value Carrier]
    [b26_after: SCIENTIFIC Value Carrier]          [b25_after: ACOLYTE Value Carrier]         [b24_after: PROPAGANDA Value Carrier]
    [b23_after: BULLSHIT Value Carrier]            [b22_after: FINITE_ELEPHANT Value Carrier] [b21_after: LOAD Value Carrier]
    [b20_after: SCALED Value Carrier]              [b19_after: MAGNITUDE Value Carrier]       [b18_after: VALUE Value Carrier]
    [b17_after: EXECUTED Value Carrier]            [b16_after: SOURCE Value Carrier]          [b15_after: GUNGAN Value Carrier]
    [b14_after: MEASURABLE Value Carrier]
  : PRESENT Prop truthCarrier := sorry

noncomputable instance PRESENT_OBSERVED_backward
    (Value: Type i)
    (Carrier: CarrierProcess Value)
    [b1_before:  DISTINGUISHABLE Value Carrier]    [b2_before:  ADMISSIBLE Value Carrier]    [b3_before:  COUNTABLE Value Carrier]
    [b4_before:  ENCODED Value Carrier]            [b5_before:  RESIDUE Value Carrier]       [b6_before:  BINARY Value Carrier]
    [b7_before:  REPEATABLE Value Carrier]         [b8_before:  NUMERIC Value Carrier]       [b9_before:  REPRESENTABLE Value Carrier]
    [b10_before: PHYSICAL Value Carrier]           [b11_before: COMPARABLE Value Carrier]    [b12_before: OBSERVED Value Carrier]
    [b13_before: PRESENT Value Carrier]            [b14_before: MEASURABLE Value Carrier]    [b15_before: GUNGAN Value Carrier]
    [b16_before: SOURCE Value Carrier]             [b17_before: EXECUTED Value Carrier]      [b18_before: VALUE Value Carrier]
    [b19_before: MAGNITUDE Value Carrier]          [b20_before: SCALED Value Carrier]        [b21_before: LOAD Value Carrier]
    [b22_before: FINITE_ELEPHANT Value Carrier]    [b23_before: BULLSHIT Value Carrier]      [b24_before: PROPAGANDA Value Carrier]
    [b25_before: ACOLYTE Value Carrier]            [b26_before: SCIENTIFIC Value Carrier]    [b27_before: TRUTH Value Carrier]
    [b28_before: WITNESSED Value Carrier]          [b29_before: LOCAL Value Carrier]         [b30_before: UNIVERSAL Value Carrier]
    [b31_before: LOGICAL Value Carrier]            [b32_before: HALTED Value Carrier]        [b33_before: MEASURED Value Carrier]
    [b34_before: COMPILED Value Carrier]           [b35_before: TrueOutput Value Carrier]
    (truthTrueOutput : TrueOutput Value Carrier)
    [b35_after: TrueOutput Value Carrier]          [b34_after: COMPILED Value Carrier]        [b33_after: MEASURED Value Carrier]
    [b32_after: HALTED Value Carrier]              [b31_after: LOGICAL Value Carrier]         [b30_after: UNIVERSAL Value Carrier]
    [b29_after: LOCAL Value Carrier]               [b28_after: WITNESSED Value Carrier]       [b27_after: TRUTH Value Carrier]
    [b26_after: SCIENTIFIC Value Carrier]          [b25_after: ACOLYTE Value Carrier]         [b24_after: PROPAGANDA Value Carrier]
    [b23_after: BULLSHIT Value Carrier]            [b22_after: FINITE_ELEPHANT Value Carrier] [b21_after: LOAD Value Carrier]
    [b20_after: SCALED Value Carrier]              [b19_after: MAGNITUDE Value Carrier]       [b18_after: VALUE Value Carrier]
    [b17_after: EXECUTED Value Carrier]            [b16_after: SOURCE Value Carrier]          [b15_after: GUNGAN Value Carrier]
    [b14_after: MEASURABLE Value Carrier]          [b13_after: PRESENT Value Carrier]
  : OBSERVED Prop truthCarrier := sorry

noncomputable instance OBSERVED_COMPARABLE_backward
    (Value: Type i)
    (Carrier: CarrierProcess Value)
    [b1_before:  DISTINGUISHABLE Value Carrier]    [b2_before:  ADMISSIBLE Value Carrier]    [b3_before:  COUNTABLE Value Carrier]
    [b4_before:  ENCODED Value Carrier]            [b5_before:  RESIDUE Value Carrier]       [b6_before:  BINARY Value Carrier]
    [b7_before:  REPEATABLE Value Carrier]         [b8_before:  NUMERIC Value Carrier]       [b9_before:  REPRESENTABLE Value Carrier]
    [b10_before: PHYSICAL Value Carrier]           [b11_before: COMPARABLE Value Carrier]    [b12_before: OBSERVED Value Carrier]
    [b13_before: PRESENT Value Carrier]            [b14_before: MEASURABLE Value Carrier]    [b15_before: GUNGAN Value Carrier]
    [b16_before: SOURCE Value Carrier]             [b17_before: EXECUTED Value Carrier]      [b18_before: VALUE Value Carrier]
    [b19_before: MAGNITUDE Value Carrier]          [b20_before: SCALED Value Carrier]        [b21_before: LOAD Value Carrier]
    [b22_before: FINITE_ELEPHANT Value Carrier]    [b23_before: BULLSHIT Value Carrier]      [b24_before: PROPAGANDA Value Carrier]
    [b25_before: ACOLYTE Value Carrier]            [b26_before: SCIENTIFIC Value Carrier]    [b27_before: TRUTH Value Carrier]
    [b28_before: WITNESSED Value Carrier]          [b29_before: LOCAL Value Carrier]         [b30_before: UNIVERSAL Value Carrier]
    [b31_before: LOGICAL Value Carrier]            [b32_before: HALTED Value Carrier]        [b33_before: MEASURED Value Carrier]
    [b34_before: COMPILED Value Carrier]           [b35_before: TrueOutput Value Carrier]
    (truthTrueOutput : TrueOutput Value Carrier)
    [b35_after: TrueOutput Value Carrier]          [b34_after: COMPILED Value Carrier]        [b33_after: MEASURED Value Carrier]
    [b32_after: HALTED Value Carrier]              [b31_after: LOGICAL Value Carrier]         [b30_after: UNIVERSAL Value Carrier]
    [b29_after: LOCAL Value Carrier]               [b28_after: WITNESSED Value Carrier]       [b27_after: TRUTH Value Carrier]
    [b26_after: SCIENTIFIC Value Carrier]          [b25_after: ACOLYTE Value Carrier]         [b24_after: PROPAGANDA Value Carrier]
    [b23_after: BULLSHIT Value Carrier]            [b22_after: FINITE_ELEPHANT Value Carrier] [b21_after: LOAD Value Carrier]
    [b20_after: SCALED Value Carrier]              [b19_after: MAGNITUDE Value Carrier]       [b18_after: VALUE Value Carrier]
    [b17_after: EXECUTED Value Carrier]            [b16_after: SOURCE Value Carrier]          [b15_after: GUNGAN Value Carrier]
    [b14_after: MEASURABLE Value Carrier]          [b13_after: PRESENT Value Carrier]         [b12_after: OBSERVED Value Carrier]
  : COMPARABLE Prop truthCarrier := sorry

noncomputable instance COMPARABLE_PHYSICAL_backward
    (Value: Type i)
    (Carrier: CarrierProcess Value)
    [b1_before:  DISTINGUISHABLE Value Carrier]    [b2_before:  ADMISSIBLE Value Carrier]    [b3_before:  COUNTABLE Value Carrier]
    [b4_before:  ENCODED Value Carrier]            [b5_before:  RESIDUE Value Carrier]       [b6_before:  BINARY Value Carrier]
    [b7_before:  REPEATABLE Value Carrier]         [b8_before:  NUMERIC Value Carrier]       [b9_before:  REPRESENTABLE Value Carrier]
    [b10_before: PHYSICAL Value Carrier]           [b11_before: COMPARABLE Value Carrier]    [b12_before: OBSERVED Value Carrier]
    [b13_before: PRESENT Value Carrier]            [b14_before: MEASURABLE Value Carrier]    [b15_before: GUNGAN Value Carrier]
    [b16_before: SOURCE Value Carrier]             [b17_before: EXECUTED Value Carrier]      [b18_before: VALUE Value Carrier]
    [b19_before: MAGNITUDE Value Carrier]          [b20_before: SCALED Value Carrier]        [b21_before: LOAD Value Carrier]
    [b22_before: FINITE_ELEPHANT Value Carrier]    [b23_before: BULLSHIT Value Carrier]      [b24_before: PROPAGANDA Value Carrier]
    [b25_before: ACOLYTE Value Carrier]            [b26_before: SCIENTIFIC Value Carrier]    [b27_before: TRUTH Value Carrier]
    [b28_before: WITNESSED Value Carrier]          [b29_before: LOCAL Value Carrier]         [b30_before: UNIVERSAL Value Carrier]
    [b31_before: LOGICAL Value Carrier]            [b32_before: HALTED Value Carrier]        [b33_before: MEASURED Value Carrier]
    [b34_before: COMPILED Value Carrier]           [b35_before: TrueOutput Value Carrier]
    (truthTrueOutput : TrueOutput Value Carrier)
    [b35_after: TrueOutput Value Carrier]          [b34_after: COMPILED Value Carrier]        [b33_after: MEASURED Value Carrier]
    [b32_after: HALTED Value Carrier]              [b31_after: LOGICAL Value Carrier]         [b30_after: UNIVERSAL Value Carrier]
    [b29_after: LOCAL Value Carrier]               [b28_after: WITNESSED Value Carrier]       [b27_after: TRUTH Value Carrier]
    [b26_after: SCIENTIFIC Value Carrier]          [b25_after: ACOLYTE Value Carrier]         [b24_after: PROPAGANDA Value Carrier]
    [b23_after: BULLSHIT Value Carrier]            [b22_after: FINITE_ELEPHANT Value Carrier] [b21_after: LOAD Value Carrier]
    [b20_after: SCALED Value Carrier]              [b19_after: MAGNITUDE Value Carrier]       [b18_after: VALUE Value Carrier]
    [b17_after: EXECUTED Value Carrier]            [b16_after: SOURCE Value Carrier]          [b15_after: GUNGAN Value Carrier]
    [b14_after: MEASURABLE Value Carrier]          [b13_after: PRESENT Value Carrier]         [b12_after: OBSERVED Value Carrier]
    [b11_after: COMPARABLE Value Carrier]
  : PHYSICAL Prop truthCarrier := sorry

noncomputable instance PHYSICAL_REPRESENTABLE_backward
    (Value: Type i)
    (Carrier: CarrierProcess Value)
    [b1_before:  DISTINGUISHABLE Value Carrier]    [b2_before:  ADMISSIBLE Value Carrier]    [b3_before:  COUNTABLE Value Carrier]
    [b4_before:  ENCODED Value Carrier]            [b5_before:  RESIDUE Value Carrier]       [b6_before:  BINARY Value Carrier]
    [b7_before:  REPEATABLE Value Carrier]         [b8_before:  NUMERIC Value Carrier]       [b9_before:  REPRESENTABLE Value Carrier]
    [b10_before: PHYSICAL Value Carrier]           [b11_before: COMPARABLE Value Carrier]    [b12_before: OBSERVED Value Carrier]
    [b13_before: PRESENT Value Carrier]            [b14_before: MEASURABLE Value Carrier]    [b15_before: GUNGAN Value Carrier]
    [b16_before: SOURCE Value Carrier]             [b17_before: EXECUTED Value Carrier]      [b18_before: VALUE Value Carrier]
    [b19_before: MAGNITUDE Value Carrier]          [b20_before: SCALED Value Carrier]        [b21_before: LOAD Value Carrier]
    [b22_before: FINITE_ELEPHANT Value Carrier]    [b23_before: BULLSHIT Value Carrier]      [b24_before: PROPAGANDA Value Carrier]
    [b25_before: ACOLYTE Value Carrier]            [b26_before: SCIENTIFIC Value Carrier]    [b27_before: TRUTH Value Carrier]
    [b28_before: WITNESSED Value Carrier]          [b29_before: LOCAL Value Carrier]         [b30_before: UNIVERSAL Value Carrier]
    [b31_before: LOGICAL Value Carrier]            [b32_before: HALTED Value Carrier]        [b33_before: MEASURED Value Carrier]
    [b34_before: COMPILED Value Carrier]           [b35_before: TrueOutput Value Carrier]
    (truthTrueOutput : TrueOutput Value Carrier)
    [b35_after: TrueOutput Value Carrier]          [b34_after: COMPILED Value Carrier]        [b33_after: MEASURED Value Carrier]
    [b32_after: HALTED Value Carrier]              [b31_after: LOGICAL Value Carrier]         [b30_after: UNIVERSAL Value Carrier]
    [b29_after: LOCAL Value Carrier]               [b28_after: WITNESSED Value Carrier]       [b27_after: TRUTH Value Carrier]
    [b26_after: SCIENTIFIC Value Carrier]          [b25_after: ACOLYTE Value Carrier]         [b24_after: PROPAGANDA Value Carrier]
    [b23_after: BULLSHIT Value Carrier]            [b22_after: FINITE_ELEPHANT Value Carrier] [b21_after: LOAD Value Carrier]
    [b20_after: SCALED Value Carrier]              [b19_after: MAGNITUDE Value Carrier]       [b18_after: VALUE Value Carrier]
    [b17_after: EXECUTED Value Carrier]            [b16_after: SOURCE Value Carrier]          [b15_after: GUNGAN Value Carrier]
    [b14_after: MEASURABLE Value Carrier]          [b13_after: PRESENT Value Carrier]         [b12_after: OBSERVED Value Carrier]
    [b11_after: COMPARABLE Value Carrier]          [b10_after: PHYSICAL Value Carrier]
  : REPRESENTABLE Prop truthCarrier := sorry

noncomputable instance REPRESENTABLE_NUMERIC_backward
    (Value: Type i)
    (Carrier: CarrierProcess Value)
    [b1_before:  DISTINGUISHABLE Value Carrier]    [b2_before:  ADMISSIBLE Value Carrier]    [b3_before:  COUNTABLE Value Carrier]
    [b4_before:  ENCODED Value Carrier]            [b5_before:  RESIDUE Value Carrier]       [b6_before:  BINARY Value Carrier]
    [b7_before:  REPEATABLE Value Carrier]         [b8_before:  NUMERIC Value Carrier]       [b9_before:  REPRESENTABLE Value Carrier]
    [b10_before: PHYSICAL Value Carrier]           [b11_before: COMPARABLE Value Carrier]    [b12_before: OBSERVED Value Carrier]
    [b13_before: PRESENT Value Carrier]            [b14_before: MEASURABLE Value Carrier]    [b15_before: GUNGAN Value Carrier]
    [b16_before: SOURCE Value Carrier]             [b17_before: EXECUTED Value Carrier]      [b18_before: VALUE Value Carrier]
    [b19_before: MAGNITUDE Value Carrier]          [b20_before: SCALED Value Carrier]        [b21_before: LOAD Value Carrier]
    [b22_before: FINITE_ELEPHANT Value Carrier]    [b23_before: BULLSHIT Value Carrier]      [b24_before: PROPAGANDA Value Carrier]
    [b25_before: ACOLYTE Value Carrier]            [b26_before: SCIENTIFIC Value Carrier]    [b27_before: TRUTH Value Carrier]
    [b28_before: WITNESSED Value Carrier]          [b29_before: LOCAL Value Carrier]         [b30_before: UNIVERSAL Value Carrier]
    [b31_before: LOGICAL Value Carrier]            [b32_before: HALTED Value Carrier]        [b33_before: MEASURED Value Carrier]
    [b34_before: COMPILED Value Carrier]           [b35_before: TrueOutput Value Carrier]
    (truthTrueOutput : TrueOutput Value Carrier)
    [b35_after: TrueOutput Value Carrier]          [b34_after: COMPILED Value Carrier]        [b33_after: MEASURED Value Carrier]
    [b32_after: HALTED Value Carrier]              [b31_after: LOGICAL Value Carrier]         [b30_after: UNIVERSAL Value Carrier]
    [b29_after: LOCAL Value Carrier]               [b28_after: WITNESSED Value Carrier]       [b27_after: TRUTH Value Carrier]
    [b26_after: SCIENTIFIC Value Carrier]          [b25_after: ACOLYTE Value Carrier]         [b24_after: PROPAGANDA Value Carrier]
    [b23_after: BULLSHIT Value Carrier]            [b22_after: FINITE_ELEPHANT Value Carrier] [b21_after: LOAD Value Carrier]
    [b20_after: SCALED Value Carrier]              [b19_after: MAGNITUDE Value Carrier]       [b18_after: VALUE Value Carrier]
    [b17_after: EXECUTED Value Carrier]            [b16_after: SOURCE Value Carrier]          [b15_after: GUNGAN Value Carrier]
    [b14_after: MEASURABLE Value Carrier]          [b13_after: PRESENT Value Carrier]         [b12_after: OBSERVED Value Carrier]
    [b11_after: COMPARABLE Value Carrier]          [b10_after: PHYSICAL Value Carrier]        [b9_after:  REPRESENTABLE Value Carrier]
  : NUMERIC Prop truthCarrier := sorry

noncomputable instance NUMERIC_REPEATABLE_backward
    (Value: Type i)
    (Carrier: CarrierProcess Value)
    [b1_before:  DISTINGUISHABLE Value Carrier]    [b2_before:  ADMISSIBLE Value Carrier]    [b3_before:  COUNTABLE Value Carrier]
    [b4_before:  ENCODED Value Carrier]            [b5_before:  RESIDUE Value Carrier]       [b6_before:  BINARY Value Carrier]
    [b7_before:  REPEATABLE Value Carrier]         [b8_before:  NUMERIC Value Carrier]       [b9_before:  REPRESENTABLE Value Carrier]
    [b10_before: PHYSICAL Value Carrier]           [b11_before: COMPARABLE Value Carrier]    [b12_before: OBSERVED Value Carrier]
    [b13_before: PRESENT Value Carrier]            [b14_before: MEASURABLE Value Carrier]    [b15_before: GUNGAN Value Carrier]
    [b16_before: SOURCE Value Carrier]             [b17_before: EXECUTED Value Carrier]      [b18_before: VALUE Value Carrier]
    [b19_before: MAGNITUDE Value Carrier]          [b20_before: SCALED Value Carrier]        [b21_before: LOAD Value Carrier]
    [b22_before: FINITE_ELEPHANT Value Carrier]    [b23_before: BULLSHIT Value Carrier]      [b24_before: PROPAGANDA Value Carrier]
    [b25_before: ACOLYTE Value Carrier]            [b26_before: SCIENTIFIC Value Carrier]    [b27_before: TRUTH Value Carrier]
    [b28_before: WITNESSED Value Carrier]          [b29_before: LOCAL Value Carrier]         [b30_before: UNIVERSAL Value Carrier]
    [b31_before: LOGICAL Value Carrier]            [b32_before: HALTED Value Carrier]        [b33_before: MEASURED Value Carrier]
    [b34_before: COMPILED Value Carrier]           [b35_before: TrueOutput Value Carrier]
    (truthTrueOutput : TrueOutput Value Carrier)
    [b35_after: TrueOutput Value Carrier]          [b34_after: COMPILED Value Carrier]        [b33_after: MEASURED Value Carrier]
    [b32_after: HALTED Value Carrier]              [b31_after: LOGICAL Value Carrier]         [b30_after: UNIVERSAL Value Carrier]
    [b29_after: LOCAL Value Carrier]               [b28_after: WITNESSED Value Carrier]       [b27_after: TRUTH Value Carrier]
    [b26_after: SCIENTIFIC Value Carrier]          [b25_after: ACOLYTE Value Carrier]         [b24_after: PROPAGANDA Value Carrier]
    [b23_after: BULLSHIT Value Carrier]            [b22_after: FINITE_ELEPHANT Value Carrier] [b21_after: LOAD Value Carrier]
    [b20_after: SCALED Value Carrier]              [b19_after: MAGNITUDE Value Carrier]       [b18_after: VALUE Value Carrier]
    [b17_after: EXECUTED Value Carrier]            [b16_after: SOURCE Value Carrier]          [b15_after: GUNGAN Value Carrier]
    [b14_after: MEASURABLE Value Carrier]          [b13_after: PRESENT Value Carrier]         [b12_after: OBSERVED Value Carrier]
    [b11_after: COMPARABLE Value Carrier]          [b10_after: PHYSICAL Value Carrier]        [b9_after:  REPRESENTABLE Value Carrier]
    [b8_after:  NUMERIC Value Carrier]
  : REPEATABLE Prop truthCarrier := sorry

noncomputable instance REPEATABLE_BINARY_backward
    (Value: Type i)
    (Carrier: CarrierProcess Value)
    [b1_before:  DISTINGUISHABLE Value Carrier]    [b2_before:  ADMISSIBLE Value Carrier]    [b3_before:  COUNTABLE Value Carrier]
    [b4_before:  ENCODED Value Carrier]            [b5_before:  RESIDUE Value Carrier]       [b6_before:  BINARY Value Carrier]
    [b7_before:  REPEATABLE Value Carrier]         [b8_before:  NUMERIC Value Carrier]       [b9_before:  REPRESENTABLE Value Carrier]
    [b10_before: PHYSICAL Value Carrier]           [b11_before: COMPARABLE Value Carrier]    [b12_before: OBSERVED Value Carrier]
    [b13_before: PRESENT Value Carrier]            [b14_before: MEASURABLE Value Carrier]    [b15_before: GUNGAN Value Carrier]
    [b16_before: SOURCE Value Carrier]             [b17_before: EXECUTED Value Carrier]      [b18_before: VALUE Value Carrier]
    [b19_before: MAGNITUDE Value Carrier]          [b20_before: SCALED Value Carrier]        [b21_before: LOAD Value Carrier]
    [b22_before: FINITE_ELEPHANT Value Carrier]    [b23_before: BULLSHIT Value Carrier]      [b24_before: PROPAGANDA Value Carrier]
    [b25_before: ACOLYTE Value Carrier]            [b26_before: SCIENTIFIC Value Carrier]    [b27_before: TRUTH Value Carrier]
    [b28_before: WITNESSED Value Carrier]          [b29_before: LOCAL Value Carrier]         [b30_before: UNIVERSAL Value Carrier]
    [b31_before: LOGICAL Value Carrier]            [b32_before: HALTED Value Carrier]        [b33_before: MEASURED Value Carrier]
    [b34_before: COMPILED Value Carrier]           [b35_before: TrueOutput Value Carrier]
    (truthTrueOutput : TrueOutput Value Carrier)
    [b35_after: TrueOutput Value Carrier]          [b34_after: COMPILED Value Carrier]        [b33_after: MEASURED Value Carrier]
    [b32_after: HALTED Value Carrier]              [b31_after: LOGICAL Value Carrier]         [b30_after: UNIVERSAL Value Carrier]
    [b29_after: LOCAL Value Carrier]               [b28_after: WITNESSED Value Carrier]       [b27_after: TRUTH Value Carrier]
    [b26_after: SCIENTIFIC Value Carrier]          [b25_after: ACOLYTE Value Carrier]         [b24_after: PROPAGANDA Value Carrier]
    [b23_after: BULLSHIT Value Carrier]            [b22_after: FINITE_ELEPHANT Value Carrier] [b21_after: LOAD Value Carrier]
    [b20_after: SCALED Value Carrier]              [b19_after: MAGNITUDE Value Carrier]       [b18_after: VALUE Value Carrier]
    [b17_after: EXECUTED Value Carrier]            [b16_after: SOURCE Value Carrier]          [b15_after: GUNGAN Value Carrier]
    [b14_after: MEASURABLE Value Carrier]          [b13_after: PRESENT Value Carrier]         [b12_after: OBSERVED Value Carrier]
    [b11_after: COMPARABLE Value Carrier]          [b10_after: PHYSICAL Value Carrier]        [b9_after:  REPRESENTABLE Value Carrier]
    [b8_after:  NUMERIC Value Carrier]             [b7_after:  REPEATABLE Value Carrier]
  : BINARY Prop truthCarrier := sorry

noncomputable instance BINARY_RESIDUE_backward
    (Value: Type i)
    (Carrier: CarrierProcess Value)
    [b1_before:  DISTINGUISHABLE Value Carrier]    [b2_before:  ADMISSIBLE Value Carrier]    [b3_before:  COUNTABLE Value Carrier]
    [b4_before:  ENCODED Value Carrier]            [b5_before:  RESIDUE Value Carrier]       [b6_before:  BINARY Value Carrier]
    [b7_before:  REPEATABLE Value Carrier]         [b8_before:  NUMERIC Value Carrier]       [b9_before:  REPRESENTABLE Value Carrier]
    [b10_before: PHYSICAL Value Carrier]           [b11_before: COMPARABLE Value Carrier]    [b12_before: OBSERVED Value Carrier]
    [b13_before: PRESENT Value Carrier]            [b14_before: MEASURABLE Value Carrier]    [b15_before: GUNGAN Value Carrier]
    [b16_before: SOURCE Value Carrier]             [b17_before: EXECUTED Value Carrier]      [b18_before: VALUE Value Carrier]
    [b19_before: MAGNITUDE Value Carrier]          [b20_before: SCALED Value Carrier]        [b21_before: LOAD Value Carrier]
    [b22_before: FINITE_ELEPHANT Value Carrier]    [b23_before: BULLSHIT Value Carrier]      [b24_before: PROPAGANDA Value Carrier]
    [b25_before: ACOLYTE Value Carrier]            [b26_before: SCIENTIFIC Value Carrier]    [b27_before: TRUTH Value Carrier]
    [b28_before: WITNESSED Value Carrier]          [b29_before: LOCAL Value Carrier]         [b30_before: UNIVERSAL Value Carrier]
    [b31_before: LOGICAL Value Carrier]            [b32_before: HALTED Value Carrier]        [b33_before: MEASURED Value Carrier]
    [b34_before: COMPILED Value Carrier]           [b35_before: TrueOutput Value Carrier]
    (truthTrueOutput : TrueOutput Value Carrier)
    [b35_after: TrueOutput Value Carrier]          [b34_after: COMPILED Value Carrier]        [b33_after: MEASURED Value Carrier]
    [b32_after: HALTED Value Carrier]              [b31_after: LOGICAL Value Carrier]         [b30_after: UNIVERSAL Value Carrier]
    [b29_after: LOCAL Value Carrier]               [b28_after: WITNESSED Value Carrier]       [b27_after: TRUTH Value Carrier]
    [b26_after: SCIENTIFIC Value Carrier]          [b25_after: ACOLYTE Value Carrier]         [b24_after: PROPAGANDA Value Carrier]
    [b23_after: BULLSHIT Value Carrier]            [b22_after: FINITE_ELEPHANT Value Carrier] [b21_after: LOAD Value Carrier]
    [b20_after: SCALED Value Carrier]              [b19_after: MAGNITUDE Value Carrier]       [b18_after: VALUE Value Carrier]
    [b17_after: EXECUTED Value Carrier]            [b16_after: SOURCE Value Carrier]          [b15_after: GUNGAN Value Carrier]
    [b14_after: MEASURABLE Value Carrier]          [b13_after: PRESENT Value Carrier]         [b12_after: OBSERVED Value Carrier]
    [b11_after: COMPARABLE Value Carrier]          [b10_after: PHYSICAL Value Carrier]        [b9_after:  REPRESENTABLE Value Carrier]
    [b8_after:  NUMERIC Value Carrier]             [b7_after:  REPEATABLE Value Carrier]      [b6_after:  BINARY Value Carrier]
  : RESIDUE Prop truthCarrier := sorry

noncomputable instance RESIDUE_ENCODED_backward
    (Value: Type i)
    (Carrier: CarrierProcess Value)
    [b1_before:  DISTINGUISHABLE Value Carrier]    [b2_before:  ADMISSIBLE Value Carrier]    [b3_before:  COUNTABLE Value Carrier]
    [b4_before:  ENCODED Value Carrier]            [b5_before:  RESIDUE Value Carrier]       [b6_before:  BINARY Value Carrier]
    [b7_before:  REPEATABLE Value Carrier]         [b8_before:  NUMERIC Value Carrier]       [b9_before:  REPRESENTABLE Value Carrier]
    [b10_before: PHYSICAL Value Carrier]           [b11_before: COMPARABLE Value Carrier]    [b12_before: OBSERVED Value Carrier]
    [b13_before: PRESENT Value Carrier]            [b14_before: MEASURABLE Value Carrier]    [b15_before: GUNGAN Value Carrier]
    [b16_before: SOURCE Value Carrier]             [b17_before: EXECUTED Value Carrier]      [b18_before: VALUE Value Carrier]
    [b19_before: MAGNITUDE Value Carrier]          [b20_before: SCALED Value Carrier]        [b21_before: LOAD Value Carrier]
    [b22_before: FINITE_ELEPHANT Value Carrier]    [b23_before: BULLSHIT Value Carrier]      [b24_before: PROPAGANDA Value Carrier]
    [b25_before: ACOLYTE Value Carrier]            [b26_before: SCIENTIFIC Value Carrier]    [b27_before: TRUTH Value Carrier]
    [b28_before: WITNESSED Value Carrier]          [b29_before: LOCAL Value Carrier]         [b30_before: UNIVERSAL Value Carrier]
    [b31_before: LOGICAL Value Carrier]            [b32_before: HALTED Value Carrier]        [b33_before: MEASURED Value Carrier]
    [b34_before: COMPILED Value Carrier]           [b35_before: TrueOutput Value Carrier]
    (truthTrueOutput : TrueOutput Value Carrier)
    [b35_after: TrueOutput Value Carrier]          [b34_after: COMPILED Value Carrier]        [b33_after: MEASURED Value Carrier]
    [b32_after: HALTED Value Carrier]              [b31_after: LOGICAL Value Carrier]         [b30_after: UNIVERSAL Value Carrier]
    [b29_after: LOCAL Value Carrier]               [b28_after: WITNESSED Value Carrier]       [b27_after: TRUTH Value Carrier]
    [b26_after: SCIENTIFIC Value Carrier]          [b25_after: ACOLYTE Value Carrier]         [b24_after: PROPAGANDA Value Carrier]
    [b23_after: BULLSHIT Value Carrier]            [b22_after: FINITE_ELEPHANT Value Carrier] [b21_after: LOAD Value Carrier]
    [b20_after: SCALED Value Carrier]              [b19_after: MAGNITUDE Value Carrier]       [b18_after: VALUE Value Carrier]
    [b17_after: EXECUTED Value Carrier]            [b16_after: SOURCE Value Carrier]          [b15_after: GUNGAN Value Carrier]
    [b14_after: MEASURABLE Value Carrier]          [b13_after: PRESENT Value Carrier]         [b12_after: OBSERVED Value Carrier]
    [b11_after: COMPARABLE Value Carrier]          [b10_after: PHYSICAL Value Carrier]        [b9_after:  REPRESENTABLE Value Carrier]
    [b8_after:  NUMERIC Value Carrier]             [b7_after:  REPEATABLE Value Carrier]      [b6_after:  BINARY Value Carrier]
    [b5_after:  RESIDUE Value Carrier]
  : ENCODED Prop truthCarrier := sorry

noncomputable instance ENCODED_COUNTABLE_backward
    (Value: Type i)
    (Carrier: CarrierProcess Value)
    [b1_before:  DISTINGUISHABLE Value Carrier]    [b2_before:  ADMISSIBLE Value Carrier]    [b3_before:  COUNTABLE Value Carrier]
    [b4_before:  ENCODED Value Carrier]            [b5_before:  RESIDUE Value Carrier]       [b6_before:  BINARY Value Carrier]
    [b7_before:  REPEATABLE Value Carrier]         [b8_before:  NUMERIC Value Carrier]       [b9_before:  REPRESENTABLE Value Carrier]
    [b10_before: PHYSICAL Value Carrier]           [b11_before: COMPARABLE Value Carrier]    [b12_before: OBSERVED Value Carrier]
    [b13_before: PRESENT Value Carrier]            [b14_before: MEASURABLE Value Carrier]    [b15_before: GUNGAN Value Carrier]
    [b16_before: SOURCE Value Carrier]             [b17_before: EXECUTED Value Carrier]      [b18_before: VALUE Value Carrier]
    [b19_before: MAGNITUDE Value Carrier]          [b20_before: SCALED Value Carrier]        [b21_before: LOAD Value Carrier]
    [b22_before: FINITE_ELEPHANT Value Carrier]    [b23_before: BULLSHIT Value Carrier]      [b24_before: PROPAGANDA Value Carrier]
    [b25_before: ACOLYTE Value Carrier]            [b26_before: SCIENTIFIC Value Carrier]    [b27_before: TRUTH Value Carrier]
    [b28_before: WITNESSED Value Carrier]          [b29_before: LOCAL Value Carrier]         [b30_before: UNIVERSAL Value Carrier]
    [b31_before: LOGICAL Value Carrier]            [b32_before: HALTED Value Carrier]        [b33_before: MEASURED Value Carrier]
    [b34_before: COMPILED Value Carrier]           [b35_before: TrueOutput Value Carrier]
    (truthTrueOutput : TrueOutput Value Carrier)
    [b35_after: TrueOutput Value Carrier]          [b34_after: COMPILED Value Carrier]        [b33_after: MEASURED Value Carrier]
    [b32_after: HALTED Value Carrier]              [b31_after: LOGICAL Value Carrier]         [b30_after: UNIVERSAL Value Carrier]
    [b29_after: LOCAL Value Carrier]               [b28_after: WITNESSED Value Carrier]       [b27_after: TRUTH Value Carrier]
    [b26_after: SCIENTIFIC Value Carrier]          [b25_after: ACOLYTE Value Carrier]         [b24_after: PROPAGANDA Value Carrier]
    [b23_after: BULLSHIT Value Carrier]            [b22_after: FINITE_ELEPHANT Value Carrier] [b21_after: LOAD Value Carrier]
    [b20_after: SCALED Value Carrier]              [b19_after: MAGNITUDE Value Carrier]       [b18_after: VALUE Value Carrier]
    [b17_after: EXECUTED Value Carrier]            [b16_after: SOURCE Value Carrier]          [b15_after: GUNGAN Value Carrier]
    [b14_after: MEASURABLE Value Carrier]          [b13_after: PRESENT Value Carrier]         [b12_after: OBSERVED Value Carrier]
    [b11_after: COMPARABLE Value Carrier]          [b10_after: PHYSICAL Value Carrier]        [b9_after:  REPRESENTABLE Value Carrier]
    [b8_after:  NUMERIC Value Carrier]             [b7_after:  REPEATABLE Value Carrier]      [b6_after:  BINARY Value Carrier]
    [b5_after:  RESIDUE Value Carrier]             [b4_after:  ENCODED Value Carrier]
  : COUNTABLE Prop truthCarrier := sorry

noncomputable instance COUNTABLE_ADMISSIBLE_backward
    (Value: Type i)
    (Carrier: CarrierProcess Value)
    [b1_before:  DISTINGUISHABLE Value Carrier]    [b2_before:  ADMISSIBLE Value Carrier]    [b3_before:  COUNTABLE Value Carrier]
    [b4_before:  ENCODED Value Carrier]            [b5_before:  RESIDUE Value Carrier]       [b6_before:  BINARY Value Carrier]
    [b7_before:  REPEATABLE Value Carrier]         [b8_before:  NUMERIC Value Carrier]       [b9_before:  REPRESENTABLE Value Carrier]
    [b10_before: PHYSICAL Value Carrier]           [b11_before: COMPARABLE Value Carrier]    [b12_before: OBSERVED Value Carrier]
    [b13_before: PRESENT Value Carrier]            [b14_before: MEASURABLE Value Carrier]    [b15_before: GUNGAN Value Carrier]
    [b16_before: SOURCE Value Carrier]             [b17_before: EXECUTED Value Carrier]      [b18_before: VALUE Value Carrier]
    [b19_before: MAGNITUDE Value Carrier]          [b20_before: SCALED Value Carrier]        [b21_before: LOAD Value Carrier]
    [b22_before: FINITE_ELEPHANT Value Carrier]    [b23_before: BULLSHIT Value Carrier]      [b24_before: PROPAGANDA Value Carrier]
    [b25_before: ACOLYTE Value Carrier]            [b26_before: SCIENTIFIC Value Carrier]    [b27_before: TRUTH Value Carrier]
    [b28_before: WITNESSED Value Carrier]          [b29_before: LOCAL Value Carrier]         [b30_before: UNIVERSAL Value Carrier]
    [b31_before: LOGICAL Value Carrier]            [b32_before: HALTED Value Carrier]        [b33_before: MEASURED Value Carrier]
    [b34_before: COMPILED Value Carrier]           [b35_before: TrueOutput Value Carrier]
    (truthTrueOutput : TrueOutput Value Carrier)
    [b35_after: TrueOutput Value Carrier]          [b34_after: COMPILED Value Carrier]        [b33_after: MEASURED Value Carrier]
    [b32_after: HALTED Value Carrier]              [b31_after: LOGICAL Value Carrier]         [b30_after: UNIVERSAL Value Carrier]
    [b29_after: LOCAL Value Carrier]               [b28_after: WITNESSED Value Carrier]       [b27_after: TRUTH Value Carrier]
    [b26_after: SCIENTIFIC Value Carrier]          [b25_after: ACOLYTE Value Carrier]         [b24_after: PROPAGANDA Value Carrier]
    [b23_after: BULLSHIT Value Carrier]            [b22_after: FINITE_ELEPHANT Value Carrier] [b21_after: LOAD Value Carrier]
    [b20_after: SCALED Value Carrier]              [b19_after: MAGNITUDE Value Carrier]       [b18_after: VALUE Value Carrier]
    [b17_after: EXECUTED Value Carrier]            [b16_after: SOURCE Value Carrier]          [b15_after: GUNGAN Value Carrier]
    [b14_after: MEASURABLE Value Carrier]          [b13_after: PRESENT Value Carrier]         [b12_after: OBSERVED Value Carrier]
    [b11_after: COMPARABLE Value Carrier]          [b10_after: PHYSICAL Value Carrier]        [b9_after:  REPRESENTABLE Value Carrier]
    [b8_after:  NUMERIC Value Carrier]             [b7_after:  REPEATABLE Value Carrier]      [b6_after:  BINARY Value Carrier]
    [b5_after:  RESIDUE Value Carrier]             [b4_after:  ENCODED Value Carrier]         [b3_after:  COUNTABLE Value Carrier]
  : ADMISSIBLE Prop truthCarrier := sorry

noncomputable instance SECOND_VARIATION
    (Value: Type i)
    (Carrier: CarrierProcess Value)
    [b1_before:  DISTINGUISHABLE Value Carrier]    [b2_before:  ADMISSIBLE Value Carrier]    [b3_before:  COUNTABLE Value Carrier]
    [b4_before:  ENCODED Value Carrier]            [b5_before:  RESIDUE Value Carrier]       [b6_before:  BINARY Value Carrier]
    [b7_before:  REPEATABLE Value Carrier]         [b8_before:  NUMERIC Value Carrier]       [b9_before:  REPRESENTABLE Value Carrier]
    [b10_before: PHYSICAL Value Carrier]           [b11_before: COMPARABLE Value Carrier]    [b12_before: OBSERVED Value Carrier]
    [b13_before: PRESENT Value Carrier]            [b14_before: MEASURABLE Value Carrier]    [b15_before: GUNGAN Value Carrier]
    [b16_before: SOURCE Value Carrier]             [b17_before: EXECUTED Value Carrier]      [b18_before: VALUE Value Carrier]
    [b19_before: MAGNITUDE Value Carrier]          [b20_before: SCALED Value Carrier]        [b21_before: LOAD Value Carrier]
    [b22_before: FINITE_ELEPHANT Value Carrier]    [b23_before: BULLSHIT Value Carrier]      [b24_before: PROPAGANDA Value Carrier]
    [b25_before: ACOLYTE Value Carrier]            [b26_before: SCIENTIFIC Value Carrier]    [b27_before: TRUTH Value Carrier]
    [b28_before: WITNESSED Value Carrier]          [b29_before: LOCAL Value Carrier]         [b30_before: UNIVERSAL Value Carrier]
    [b31_before: LOGICAL Value Carrier]            [b32_before: HALTED Value Carrier]        [b33_before: MEASURED Value Carrier]
    [b34_before: COMPILED Value Carrier]           [b35_before: TrueOutput Value Carrier]
    (truthTrueOutput : TrueOutput Value Carrier)
    [b35_after: TrueOutput Value Carrier]          [b34_after: COMPILED Value Carrier]        [b33_after: MEASURED Value Carrier]
    [b32_after: HALTED Value Carrier]              [b31_after: LOGICAL Value Carrier]         [b30_after: UNIVERSAL Value Carrier]
    [b29_after: LOCAL Value Carrier]               [b28_after: WITNESSED Value Carrier]       [b27_after: TRUTH Value Carrier]
    [b26_after: SCIENTIFIC Value Carrier]          [b25_after: ACOLYTE Value Carrier]         [b24_after: PROPAGANDA Value Carrier]
    [b23_after: BULLSHIT Value Carrier]            [b22_after: FINITE_ELEPHANT Value Carrier] [b21_after: LOAD Value Carrier]
    [b20_after: SCALED Value Carrier]              [b19_after: MAGNITUDE Value Carrier]       [b18_after: VALUE Value Carrier]
    [b17_after: EXECUTED Value Carrier]            [b16_after: SOURCE Value Carrier]          [b15_after: GUNGAN Value Carrier]
    [b14_after: MEASURABLE Value Carrier]          [b13_after: PRESENT Value Carrier]         [b12_after: OBSERVED Value Carrier]
    [b11_after: COMPARABLE Value Carrier]          [b10_after: PHYSICAL Value Carrier]        [b9_after:  REPRESENTABLE Value Carrier]
    [b8_after:  NUMERIC Value Carrier]             [b7_after:  REPEATABLE Value Carrier]      [b6_after:  BINARY Value Carrier]
    [b5_after:  RESIDUE Value Carrier]             [b4_after:  ENCODED Value Carrier]         [b3_after:  COUNTABLE Value Carrier]
    [b2_after:  ADMISSIBLE Value Carrier]
  : DISTINGUISHABLE Prop truthCarrier := sorry

noncomputable class ELECTRONIC
    (Value: Type i)
    (Carrier: CarrierProcess Value)
    [b1_before:  DISTINGUISHABLE Value Carrier]    [b2_before:  ADMISSIBLE Value Carrier]    [b3_before:  COUNTABLE Value Carrier]
    [b4_before:  ENCODED Value Carrier]            [b5_before:  RESIDUE Value Carrier]       [b6_before:  BINARY Value Carrier]
    [b7_before:  REPEATABLE Value Carrier]         [b8_before:  NUMERIC Value Carrier]       [b9_before:  REPRESENTABLE Value Carrier]
    [b10_before: PHYSICAL Value Carrier]           [b11_before: COMPARABLE Value Carrier]    [b12_before: OBSERVED Value Carrier]
    [b13_before: PRESENT Value Carrier]            [b14_before: MEASURABLE Value Carrier]    [b15_before: GUNGAN Value Carrier]
    [b16_before: SOURCE Value Carrier]             [b17_before: EXECUTED Value Carrier]      [b18_before: VALUE Value Carrier]
    [b19_before: MAGNITUDE Value Carrier]          [b20_before: SCALED Value Carrier]        [b21_before: LOAD Value Carrier]
    [b22_before: FINITE_ELEPHANT Value Carrier]    [b23_before: BULLSHIT Value Carrier]      [b24_before: PROPAGANDA Value Carrier]
    [b25_before: ACOLYTE Value Carrier]            [b26_before: SCIENTIFIC Value Carrier]    [b27_before: TRUTH Value Carrier]
    [b28_before: WITNESSED Value Carrier]          [b29_before: LOCAL Value Carrier]         [b30_before: UNIVERSAL Value Carrier]
    [b31_before: LOGICAL Value Carrier]            [b32_before: HALTED Value Carrier]        [b33_before: MEASURED Value Carrier]
    [b34_before: COMPILED Value Carrier]           [b35_before: TrueOutput Value Carrier]
    (truthTrueOutput : TrueOutput Value Carrier)
    [b35_after: TrueOutput Value Carrier]          [b34_after: COMPILED Value Carrier]        [b33_after: MEASURED Value Carrier]
    [b32_after: HALTED Value Carrier]              [b31_after: LOGICAL Value Carrier]         [b30_after: UNIVERSAL Value Carrier]
    [b29_after: LOCAL Value Carrier]               [b28_after: WITNESSED Value Carrier]       [b27_after: TRUTH Value Carrier]
    [b26_after: SCIENTIFIC Value Carrier]          [b25_after: ACOLYTE Value Carrier]         [b24_after: PROPAGANDA Value Carrier]
    [b23_after: BULLSHIT Value Carrier]            [b22_after: FINITE_ELEPHANT Value Carrier] [b21_after: LOAD Value Carrier]
    [b20_after: SCALED Value Carrier]              [b19_after: MAGNITUDE Value Carrier]       [b18_after: VALUE Value Carrier]
    [b17_after: EXECUTED Value Carrier]            [b16_after: SOURCE Value Carrier]          [b15_after: GUNGAN Value Carrier]
    [b14_after: MEASURABLE Value Carrier]          [b13_after: PRESENT Value Carrier]         [b12_after: OBSERVED Value Carrier]
    [b11_after: COMPARABLE Value Carrier]          [b10_after: PHYSICAL Value Carrier]        [b9_after:  REPRESENTABLE Value Carrier]
    [b8_after:  NUMERIC Value Carrier]             [b7_after:  REPEATABLE Value Carrier]      [b6_after:  BINARY Value Carrier]
    [b5_after:  RESIDUE Value Carrier]             [b4_after:  ENCODED Value Carrier]         [b3_after:  COUNTABLE Value Carrier]
    [b2_after:  ADMISSIBLE Value Carrier]          [b1_after:  DISTINGUISHABLE Value Carrier]
    (electron_model : TrueOutput Value Carrier)
    [b1_slip:  DISTINGUISHABLE Value Carrier]    [b2_slip:  ADMISSIBLE Value Carrier]    [b3_slip:  COUNTABLE Value Carrier]
    [b4_slip:  ENCODED Value Carrier]            [b5_slip:  RESIDUE Value Carrier]       [b6_slip:  BINARY Value Carrier]
    [b7_slip:  REPEATABLE Value Carrier]         [b8_slip:  NUMERIC Value Carrier]       [b9_slip:  REPRESENTABLE Value Carrier]
    [b10_slip: PHYSICAL Value Carrier]           [b11_slip: COMPARABLE Value Carrier]    [b12_slip: OBSERVED Value Carrier]
    [b13_slip: PRESENT Value Carrier]            [b14_slip: MEASURABLE Value Carrier]    [b15_slip: GUNGAN Value Carrier]
    [b16_slip: SOURCE Value Carrier]             [b17_slip: EXECUTED Value Carrier]      [b18_slip: VALUE Value Carrier]
    [b19_slip: MAGNITUDE Value Carrier]          [b20_slip: SCALED Value Carrier]        [b21_slip: LOAD Value Carrier]
    [b22_slip: FINITE_ELEPHANT Value Carrier]    [b23_slip: BULLSHIT Value Carrier]      [b24_slip: PROPAGANDA Value Carrier]
    [b25_slip: ACOLYTE Value Carrier]            [b26_slip: SCIENTIFIC Value Carrier]    [b27_slip: TRUTH Value Carrier]
    [b28_slip: WITNESSED Value Carrier]          [b29_slip: LOCAL Value Carrier]         [b30_slip: UNIVERSAL Value Carrier]
    [b31_slip: LOGICAL Value Carrier]            [b32_slip: HALTED Value Carrier]        [b33_slip: MEASURED Value Carrier]
    [b34_slip: COMPILED Value Carrier]           [b35_slip: TrueOutput Value Carrier]    [b36_slip: INFERRED Value Carrier]
  where
    sorry

noncomputable instance ELECTRON_MODEL
    (Value: Type i)
    (Carrier: CarrierProcess Value)   --This step computes <.
    [b1_before:  DISTINGUISHABLE Value Carrier]    [b2_before:  ADMISSIBLE Value Carrier]    [b3_before:  COUNTABLE Value Carrier]
    [b4_before:  ENCODED Value Carrier]            [b5_before:  RESIDUE Value Carrier]       [b6_before:  BINARY Value Carrier]
    [b7_before:  REPEATABLE Value Carrier]         [b8_before:  NUMERIC Value Carrier]       [b9_before:  REPRESENTABLE Value Carrier]
    [b10_before: PHYSICAL Value Carrier]           [b11_before: COMPARABLE Value Carrier]    [b12_before: OBSERVED Value Carrier]
    [b13_before: PRESENT Value Carrier]            [b14_before: MEASURABLE Value Carrier]    [b15_before: GUNGAN Value Carrier]
    [b16_before: SOURCE Value Carrier]             [b17_before: EXECUTED Value Carrier]      [b18_before: VALUE Value Carrier]
    [b19_before: MAGNITUDE Value Carrier]          [b20_before: SCALED Value Carrier]        [b21_before: LOAD Value Carrier]
    [b22_before: FINITE_ELEPHANT Value Carrier]    [b23_before: BULLSHIT Value Carrier]      [b24_before: PROPAGANDA Value Carrier]
    [b25_before: ACOLYTE Value Carrier]            [b26_before: SCIENTIFIC Value Carrier]    [b27_before: TRUTH Value Carrier]
    [b28_before: WITNESSED Value Carrier]          [b29_before: LOCAL Value Carrier]         [b30_before: UNIVERSAL Value Carrier]
    [b31_before: LOGICAL Value Carrier]            [b32_before: HALTED Value Carrier]        [b33_before: MEASURED Value Carrier]
    [b34_before: COMPILED Value Carrier]           [b35_before: TrueOutput Value Carrier]
    (truthTrueOutput : TrueOutput Prop Carrier)  -- Now, we can propagate THAT definition back down.
    [b35_after: TrueOutput Value Carrier]          [b34_after: COMPILED Value Carrier]        [b33_after: MEASURED Value Carrier]
    [b32_after: HALTED Value Carrier]              [b31_after: LOGICAL Value Carrier]         [b30_after: UNIVERSAL Value Carrier]
    [b29_after: LOCAL Value Carrier]               [b28_after: WITNESSED Gospel Carrier]       [b27_after: TRUTH Knowledge Carrier]
    [b26_after: SCIENTIFIC Science Carrier]          [b25_after: ACOLYTE Cult Carrier]         [b24_after: PROPAGANDA Diatribe Carrier]
    [b23_after: BULLSHIT Spline Carrier]            [b22_after: FINITE_ELEPHANT Polynomial Carrier] [b21_after: LOAD Basis Carrier]
    [b20_after: SCALED Product Carrier]              [b19_after: MAGNITUDE Sum Carrier]       [b18_after: VALUE Abstraction Carrier]
    [b17_after: EXECUTED Encoding Carrier]            [b16_after: SOURCE Equivalation Carrier]          [b15_after: GUNGAN Jar Carrier]
    [b14_after: MEASURABLE Phenomenon Carrier]          [b13_after: PRESENT Area Carrier]         [b12_after: OBSERVED Sophism Carrier]
    [b11_after: COMPARABLE Metavariable Carrier]          [b10_after: PHYSICAL ChaitinsNumberSequence Carrier]        [b9_after:  REPRESENTABLE Computation Carrier]
    [b8_after:  NUMERIC Study Carrier]             [b7_after:  REPEATABLE Trial Carrier]      [b6_after:  BINARY Sample Carrier]
    [b5_after:  RESIDUE Limit Carrier]             [b4_after:  ENCODED Sequence Carrier]         [b3_after:  COUNTABLE Rational Carrier]
    [b2_after:  ADMISSIBLE Natural Carrier]
    (electron_model : DISTINGUISHABLE Number Carrier)  --Fact.DIFFERENT? TrueOutput.Symbol? This allows us to make a distinguishable number because we have <.
                                                       --From which we infer enough math to build a nuclear weapon, and not one iota more.
    [b1_slip:  DISTINGUISHABLE Number Carrier]    [b2_slip:  ADMISSIBLE Natural Carrier]    [b3_slip:  COUNTABLE Rational Carrier]
    [b4_slip:  ENCODED Sequence Carrier]            [b5_slip:  RESIDUE Limit Carrier]       [b6_slip:  BINARY Sample Carrier]
    [b7_slip:  REPEATABLE Trial Carrier]         [b8_slip:  NUMERIC Study Carrier]       [b9_slip:  REPRESENTABLE Computation Carrier]
    [b10_slip: PHYSICAL ChaitinsNumberSequence Carrier]           [b11_slip: COMPARABLE Metavariable Carrier]    [b12_slip: OBSERVED Sophism Carrier]
    [b13_slip: PRESENT Area Carrier]            [b14_slip: MEASURABLE Phenomenon Carrier]    [b15_slip: GUNGAN Jar Carrier]
    [b16_slip: SOURCE Equivalation Carrier]             [b17_slip: EXECUTED Encoding Carrier]      [b18_slip: VALUE Abstraction Carrier]
    [b19_slip: MAGNITUDE Sum Carrier]          [b20_slip: SCALED Product Carrier]        [b21_slip: LOAD Basis Carrier]
    [b22_slip: FINITE_ELEPHANT Polynomial Carrier]    [b23_slip: BULLSHIT Spline Carrier]      [b24_slip: PROPAGANDA Diatribe Carrier]
    [b25_slip: ACOLYTE Cult Carrier]            [b26_slip: SCIENTIFIC Science Carrier]    [b27_slip: TRUTH Knowledge Carrier]
    [b28_slip: WITNESSED Gospel Carrier]          [b29_slip: LOCAL Truth Carrier]         [b30_slip: UNIVERSAL Variation Carrier]
    [b31_slip: LOGICAL SpaceTimePath Carrier]            [b32_slip: HALTED YarnTheory Carrier]        [b33_slip: MEASURED Measurement Carrier]
    [b34_slip: COMPILED CompilerTape Carrier]           [b35_slip: TrueOutput Bullshit Carrier]
    (boson: INFERRED Closure Carrier)                  -- And so we get Noether's theorem.
    [b35_model: TrueOutput Value Carrier]          [b34_model: COMPILED Value Carrier]        [b33_model: MEASURED Value Carrier]
    [b32_model: HALTED Value Carrier]              [b31_model: LOGICAL Value Carrier]         [b30_model: UNIVERSAL Value Carrier]
    [b29_model: LOCAL Value Carrier]               [b28_model: WITNESSED Value Carrier]       [b27_model: TRUTH Value Carrier]
    [b26_model: SCIENTIFIC Value Carrier]          [b25_model: ACOLYTE Value Carrier]         [b24_model: PROPAGANDA Value Carrier]
    [b23_model: BULLSHIT Value Carrier]            [b22_model: FINITE_ELEPHANT Value Carrier] [b21_model: LOAD Value Carrier]
    [b20_model: SCALED Value Carrier]              [b19_model: MAGNITUDE Value Carrier]       [b18_model: VALUE Value Carrier]
    [b17_model: EXECUTED Value Carrier]            [b16_model: SOURCE Value Carrier]          [b15_model: GUNGAN Value Carrier]
    [b14_model: MEASURABLE Value Carrier]          [b13_model: PRESENT Value Carrier]         [b12_model: OBSERVED Value Carrier]
    [b11_model: COMPARABLE Value Carrier]          [b10_model: PHYSICAL Value Carrier]        [b9_model:  REPRESENTABLE Value Carrier]
    [b8_model:  NUMERIC Value Carrier]             [b7_model:  REPEATABLE Value Carrier]      [b6_model:  BINARY Value Carrier]
    [b5_model:  RESIDUE Value Carrier]             [b4_model:  ENCODED Value Carrier]         [b3_model:  COUNTABLE Value Carrier]
    [b2_model:  ADMISSIBLE Value Carrier]
    (electron: DISTINGUISHABLE Prop Carrier)     -- If you can distinguish an electron you are in GR.  If you cannot, you are in QED.
  := ...

end Measurement
