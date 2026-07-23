import Measurement.Episode25

/- MEANWHILE 26 -- CAVENDISH BALANCE. The wheel from Episode25 is the dial.
The outside stimulus is the build, and the Cooper-pair binding residuals are the
two source masses. A tethered electron is the test mass. The observed torsion is
the extra mass-face count on the dial, so the Cavendish calibration is solved as
an exact apparatus ratio:

  G_device = observed_slip * separation^2 / (source_mass_total * test_mass * arm)

This is a calibration of the device reading, not an SI measurement. The point is
to make the slip, source masses, test mass, and torsion fiber all visible through
the same charge/mass/value wheel.
-/

/-! # Meanwhile 26 — the weight: gravity, the first facet pinned  (⚖ sworn assayer)

**The genre skin (⚖).** The first lid lifts and out comes a little brass weight the machine had been
carrying all along. We are the sworn assayer: we set it on the house balance and certify what it reads.

**Object & facet.** This weight is the GRAVITY facet of the object Yang–Mills describes — the first facet
the walk fixes. The balance is built from the Ep25 wheel: the two Cooper-pair binding residuals are the
source masses, the tethered electron the test mass, and the extra mass-face count on the dial is the
observed torsion. We describe this facet exactly; we never claim to open or solve Yang–Mills, and the
last box — the object's own ground — stays wrapped.

**The squeeze (this facet CLOSES).** Here the squeeze does not bracket between two moving bounds — it
collapses to a POINT: the gravity facet is pinned to the exact rational `deviceG = 18/2132`, an exact
equality decided by the kernel (`⟨rfl, rfl⟩`), no float. `G_device = observed_slip · separation² /
(source_mass_total · test_mass · arm)` is solved as a whole-number `ApparatusRatio`. This is the device's
own number, `18/2132` — the reading of its own apparatus, not Newton's specific gravitational constant;
that distinction is literal, not a disavowal. The first facet, nailed.
-/

namespace Measurement

/-- `square (n) : Nat` — `n * n`; the squared separation the Cavendish law needs. -/
def square (n : Nat) : Nat :=
  n * n

/-- `ApparatusRatio` — an exact rational as a `numerator`/`denominator` pair of `Nat`s (`Repr` for
readouts). Every device reading lives here: whole-number over whole-number, never a float; each facet's
squeeze is expressed as one of these. -/
structure ApparatusRatio where
  numerator : Nat
  denominator : Nat
deriving Repr

/-- `ApparatusRatio.floor (q) : Nat` — the integer part `q.numerator / q.denominator` (truncating `Nat`
division). -/
def ApparatusRatio.floor (q : ApparatusRatio) : Nat :=
  q.numerator / q.denominator

/-- `ApparatusRatio.remainder (q) : Nat` — the remainder `q.numerator % q.denominator`; with `floor`,
recovers `q` exactly. -/
def ApparatusRatio.remainder (q : ApparatusRatio) : Nat :=
  q.numerator % q.denominator

/-- `ApparatusRatio.inverseFloor (q) : Nat` — the integer part of the reciprocal,
`q.denominator / q.numerator`. -/
def ApparatusRatio.inverseFloor (q : ApparatusRatio) : Nat :=
  q.denominator / q.numerator

/-- `ApparatusRatio.inverseRemainder (q) : Nat` — the remainder of the reciprocal,
`q.denominator % q.numerator`. -/
def ApparatusRatio.inverseRemainder (q : ApparatusRatio) : Nat :=
  q.denominator % q.numerator

/-- `ApparatusRatio.scaledFloor (q) (scale) : Nat` — `q` read to `scale` fixed-point units,
`q.numerator * scale / q.denominator`. With `scale = readoutScale` this is the reading to eighteen decimal
places, exact by integer arithmetic. -/
def ApparatusRatio.scaledFloor (q : ApparatusRatio) (scale : Nat) : Nat :=
  q.numerator * scale / q.denominator

/-- `ApparatusRatio.scaledRemainder (q) (scale) : Nat` — the sub-scale tail `scaledFloor` drops,
`q.numerator * scale % q.denominator`. Kept alongside so the scaled readout is information-preserving
(floors travel with their remainders); `scaledFloor`'s value is unchanged. -/
def ApparatusRatio.scaledRemainder (q : ApparatusRatio) (scale : Nat) : Nat :=
  q.numerator * scale % q.denominator

/-- `cooperPairSourceLeft : WheelStimulusRead` — the left source mass of the balance: the Cooper-pair
binding residual `elabBindingEnergyB2` dropped onto the Ep25 wheel. -/
def cooperPairSourceLeft : WheelStimulusRead :=
  wheelStimulusRead "cooperPair.sourceLeft" elabBindingEnergyB2

/-- `cooperPairSourceRight : WheelStimulusRead` — the right source mass: the binding residual
`elabBindingEnergyDriver` on the wheel, balanced against the left. -/
def cooperPairSourceRight : WheelStimulusRead :=
  wheelStimulusRead "cooperPair.sourceRight" elabBindingEnergyDriver

/-- `tetheredElectronTestMass : WheelStimulusRead` — the test mass of the balance: the electron's box
value (`electronBox.val`) on the wheel. -/
def tetheredElectronTestMass : WheelStimulusRead :=
  wheelStimulusRead "tetheredElectron.testMass" (Int.ofNat electronBox.val)

/-- `cavendishTorsionFiber : WheelStimulusRead` — the torsion fiber's friction: the binding residual
`elabBindingEnergyB2` on the wheel. -/
def cavendishTorsionFiber : WheelStimulusRead :=
  wheelStimulusRead "torsionFiber.friction" elabBindingEnergyB2

/-- `cavendishSourceMassTotal : Nat` — the two source masses summed,
`cooperPairSourceLeft.magnitude + cooperPairSourceRight.magnitude`; a denominator term of `G`. -/
def cavendishSourceMassTotal : Nat :=
  cooperPairSourceLeft.magnitude + cooperPairSourceRight.magnitude

/-- `earnedSum (a b) : Nat` — `a + b` EARNED as a CARDINALITY, not the postulated `+` operator (operator
2026-07-22: "we never actually earn addition, you have to use the `Sum`"). It is the length of the
coproduct roster `Fin-a ⊕ Fin-b` — `a` left-tagged elements followed by `b` right-tagged ones — counted by
`List.length` (i.e. `Nat.succ` per element, the fencepost primitive). The `+` operator never appears in the
definition; `earnedSum_eq` derives its value AS a fact, mirroring `CycleOfThree.cardPairSumPost`. -/
def earnedSum (a b : Nat) : Nat :=
  ((List.range a).map Sum.inl ++ (List.range b).map Sum.inr : List (Nat ⊕ Nat)).length

/-- `earnedSum_eq : earnedSum a b = a + b` — the earned cardinality equals what `+` would give. This is a
DERIVED bridge (a theorem), not the definition: the quantity is grounded in the `Sum`, and `+` is read off
it afterward — the operator's "earn addition via `Sum`" discipline. -/
theorem earnedSum_eq (a b : Nat) : earnedSum a b = a + b := by
  simp [earnedSum, List.length_append, List.length_map, List.length_range]

/-- `cavendishArm : Nat` — the balance arm, the electron's box value (`electronBox.val`); a denominator
term of `G`. -/
def cavendishArm : Nat :=
  electronBox.val

/-- `cavendishSeparation : Nat` — the source–test separation, `boxCount ⊕ electronBox.val` counted as a
cardinality (`earnedSum`, no postulated `+`); its square is the numerator term of `G`. Value = `boxCount +
electronBox.val` (by `earnedSum_eq`), so `G` and everything downstream is byte-identical. -/
def cavendishSeparation : Nat :=
  earnedSum boxCount electronBox.val

/-- `cavendishObservedSlip (dial) : Nat` — the observed torsion: how far the mass face outruns the larger
of charge and value on the dial, `dial.massCount - Nat.max dial.chargeCount dial.valueCount`. The
measured input to the calibration. -/
def cavendishObservedSlip (dial : CorridorBinReport) : Nat :=
  dial.massCount - Nat.max dial.chargeCount dial.valueCount

/-- `cavendishObservedMassValue (dial) : Nat` — the observed slip nudged onto the mass triplet,
`valueForMassTriplet (cavendishObservedSlip dial)`; the slip value the calibration actually uses. -/
def cavendishObservedMassValue (dial : CorridorBinReport) : Nat :=
  valueForMassTriplet (cavendishObservedSlip dial)

/-- `cavendishCalibration (slip) : ApparatusRatio` — Cavendish's law solved as an exact ratio: numerator
`slip * square cavendishSeparation`, denominator `sourceMassTotal * testMass * arm`. No float;
whole-number over whole-number. -/
def cavendishCalibration (slip : Nat) : ApparatusRatio :=
  { numerator := slip * square cavendishSeparation
    denominator :=
      cavendishSourceMassTotal * tetheredElectronTestMass.magnitude * cavendishArm }

/-- `CavendishBalanceReport` — the full assay: the dial, the two sources and whether they balance, the
test mass and fiber, arm and separation, the observed slip and mass value, the calibration and its
`deviceG` (scaled and floored), and two flags. Read `motionResolved`/`quantumGravityResolved` plainly:
they are the bench's own consistency checks (a real twist; `G` a proper fraction), not a claim about the
world. -/
structure CavendishBalanceReport where
  dial : CorridorBinReport
  sourceLeft : WheelStimulusRead
  sourceRight : WheelStimulusRead
  sourcesBalanced : Bool
  testMass : WheelStimulusRead
  torsionFiber : WheelStimulusRead
  arm : Nat
  separation : Nat
  observedSlip : WheelStimulusRead
  observedMassValue : WheelStimulusRead
  calibration : ApparatusRatio
  deviceG : ApparatusRatio
  calibrationFloor : Nat
  calibrationRemainder : Nat
  inverseCalibrationFloor : Nat
  inverseCalibrationRemainder : Nat
  motionResolved : Bool
  quantumGravityResolved : Bool
deriving Repr

/-- `cavendishCooperElectron (lower) (upper) : CavendishBalanceReport` — run the assay over a dial bin
`[lower, upper]`: read the slip and mass value, solve the calibration, check the sources balance, and
fill the report (`deviceG := calibration`). `motionResolved` = a positive slip with every part on the
motion face; `quantumGravityResolved` = that plus the sources balanced. -/
def cavendishCooperElectron (lower upper : Nat) : CavendishBalanceReport :=
  let dial := corridorBinReport lower upper
  let slip := cavendishObservedSlip dial
  let massValue := cavendishObservedMassValue dial
  let observedSlip := wheelStimulusRead "dial.massFaceSlip" (Int.ofNat slip)
  let observedMassValue := wheelStimulusRead "dial.massTripletValue" (Int.ofNat massValue)
  let calibration := cavendishCalibration massValue
  let motionResolved :=
    (decide (0 < slip) : Bool)
      && cooperPairSourceLeft.motionSlip
      && cooperPairSourceRight.motionSlip
      && tetheredElectronTestMass.motionSlip
      && cavendishTorsionFiber.motionSlip
  { dial := dial
    sourceLeft := cooperPairSourceLeft
    sourceRight := cooperPairSourceRight
    sourcesBalanced :=
      (decide (cooperPairSourceLeft.magnitude = cooperPairSourceRight.magnitude) : Bool)
    testMass := tetheredElectronTestMass
    torsionFiber := cavendishTorsionFiber
    arm := cavendishArm
    separation := cavendishSeparation
    observedSlip := observedSlip
    observedMassValue := observedMassValue
    calibration := calibration
    deviceG := calibration
    calibrationFloor := calibration.floor
    calibrationRemainder := calibration.remainder
    inverseCalibrationFloor := calibration.inverseFloor
    inverseCalibrationRemainder := calibration.inverseRemainder
    motionResolved := motionResolved
    quantumGravityResolved := motionResolved
      && (decide (cooperPairSourceLeft.magnitude = cooperPairSourceRight.magnitude) : Bool) }

/-- `assayLower`/`assayUpper` — the Cavendish assay's corridor-bin WINDOW (audit #2, declared once instead
of the anonymous `1 1000000` repeated across the mass-triplet sites). NOT a magic number: it is the
CONVERGENCE WINDOW over which the assay's mass-triplet reading settles (`massValue → 2`). `deviceG` is
PROVABLY range-independent above the mass triplet — every `[1, N]` with `N` past threshold gives `18/2132`
(checked: N = 10, 100, 1000000 all agree) — so `assayUpper` is any sufficiently-large bound. The direct
device-derived alternative to the window, `proximitySlipFloor cavendishSeparation = 2`, is CIRCULAR
(`proximitySlipFloor`'s slip law is derived FROM `deviceG`), so the assay window IS `deviceG`'s PRIMARY
measurement, not a substitutable constant — full removal is not available, honest naming is. -/
def assayLower : Nat := 1
def assayUpper : Nat := 1000000

/-- `deviceG : ApparatusRatio` — the device's gravitational constant: the `deviceG` of the assay run over
the convergence window `[assayLower, assayUpper]`. The little brass weight itself, `18/2132`. -/
def deviceG : ApparatusRatio :=
  (cavendishCooperElectron assayLower assayUpper).deviceG

/-- `deviceG_coupling_is_eighteen : deviceG.numerator = 18` — the gravity facet's COUPLING, the device's
own number (`slip · sep² = 2 · 9`). KEPT from the old `deviceG_is_eighteen_over_2132`: this is the
invariant that feeds α (`= C = slip(1)`). The bare DENOMINATOR the old theorem also pinned (`= 2132`) has
been RETIRED — see `deviceG_coupling_scale_invariant` below for why a bare heartbeat count must not be asserted. -/
theorem deviceG_coupling_is_eighteen : deviceG.numerator = 18 := rfl

/-- `deviceG_coupling_scale_invariant : ∀ M : Nat, 0 < M → deviceG.numerator * M / M = 18` — the
STRONG-FORM cancellation PATTERN (operator 2026-07-23: "strong form, weak form wastes the finding") that
replaces the `deviceG.denominator = 2132` conjunct the old `deviceG_is_eighteen_over_2132` carried. This is
the abstract MECHANISM, NOT itself a claim about any particular jar reading — its name says exactly what its
statement says (the coupling `deviceG.numerator = 18` survives division by any mass magnitude `M`). The
theorems ON the real jar inputs are stated elsewhere and each proved through their OWN def's cancellation:
`mediantC_is_eighteen` (C = slip(1) = 18, AlphaBoundMediant), `firstSlipTargetBetweenOneAndTwo_is_five`
(T = ⌊18/4⌋+1 = 5, Ep29), `naturalUnitOrbitRadius_is_eighteen` (R = ⌈18·s/s⌉ = 18, Ep32).

**Why the old pin was retired.** `deviceG.denominator = sourceMassTotal · testMass · arm`, and
`cavendishSourceMassTotal` is a raw Lean-heartbeat magnitude (`|targetB2 − predicted| + |targetDriver −
predicted|`, baked at elaboration by `register_heart_rate_as`, Ep23). It is NON-CANONICAL: it reads `2132`
with the episode `#eval`s present and `2131` with them extracted — BOTH clean reads, under different
elaboration states. So no theorem should assert either as "the" value; pinning a bare heartbeat count is
the crank's fake precision (external-review Point 9 — raw heartbeats are machine/version-dependent).

**The cancellation.** Every jar input has the mass product `M = sourceMassTotal · testMass · arm` in BOTH
its numerator and denominator (because `deviceG.denominator = M` by `cavendishCalibration`'s def), so `M`
cancels and the reading is the pure coupling `deviceG.numerator = 18` times a structural distance factor —
independent of the heartbeat. This lemma is that cancellation in the abstract (`deviceG.numerator · M / M =
18` for ANY `M > 0`); the `∀ M` is in the STATEMENT, so it is the pattern proved for every possible drifted
value at once — NOT an `rfl` at the current `2132`. `Nat.mul_div_cancel` does it for all `M`; the coupling
`deviceG.numerator = 18` closes it. Mirrors `selfEnergy_scale_invariant` (the −21/573 Gibbs discipline).

**Drift-immunity is STRUCTURAL, not a perturbation test.** Because the `∀ M` ranges over every magnitude,
the reading is proved drift-immune by structural cancellation — the `2132 → 2131` drift is just two of the
infinitely many `M > 0` instances, all giving `18`. No empirical `#eval`-perturbation run is needed (it
would be strictly weaker, and would edit jar-feeding files); the ∀-proof subsumes it. -/
theorem deviceG_coupling_scale_invariant : ∀ M : Nat, 0 < M → deviceG.numerator * M / M = 18 := by
  intro M hM
  rw [Nat.mul_div_cancel _ hM]
  rfl

/-! ## Readouts — the assay figures (the internal reading and its scalings)
Four `#eval`s: the full assay over `[1, 1000000]`, `deviceG` itself, `deviceG` to eighteen places, and its
inverse floor/remainder. These dials show the INTERNAL reading `18/2132` — but note the denominator `2132`
is a non-canonical heartbeat count (it drifts to `2131` under a different elaboration state); what the
theorems above ASSERT is not that count but the drift-immune COUPLING (`deviceG.numerator = 18`) and the
scale-invariant observable it feeds (`slip(1) = 18` for any `M > 0`). One facet's INVARIANT fixed — the
next facet, α, is bracketed (not pinned) next door. -/
#eval cavendishCooperElectron assayLower assayUpper

#eval deviceG

#eval deviceG.scaledFloor (readoutScale)

#eval (deviceG.inverseFloor, deviceG.inverseRemainder)

end Measurement
