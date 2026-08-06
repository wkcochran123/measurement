import Measurement.Episode14

set_option maxHeartbeats 4000000
set_option maxRecDepth 1000
set_option allowUnsafeReducibility true


namespace Measurement

universe i


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
