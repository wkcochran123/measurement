# Book 2 - The Physical Gauge

Working title: Measurement

Subtitle: How Physical Law Emerges from the Act of Observation

Audience: physicists, scientifically curious readers, and readers who want the
speedometer version of the argument.

Claim: physical laws are not imposed on nature. They are the unique
descriptions consistent with finite, distinguishable measurement records.

The Lean code is backstage. The physics is the foreground. This is the
instrument book: calibration standards, clocks, finite records, apparatus,
repeatability, and the laws that are forced when measurement has to be honest.

Ground example: the speedometer. A car's speedometer is a Hall-effect sensor
reading magnetic teeth on the drivetrain — 36 pulses per revolution; the
pulse rate times the wheel circumference (itself a calibrated quantity,
depending on tire radius) gives speed. The speedometer thread runs through
every chapter of this book. It is not the only example, but it is always
present: a specific instrument making a specific kind of record, limited in
specific ways, requiring calibration before it can mean anything.

## Shared Frame

Source hierarchy:

```text
gauge.pdf                       source manuscript; nine chapters; all registers mixed
three_gauges.md                 extraction and architecture plan
instrument/chapters/*.tex       phenomenon source, especially for physical examples
device/Measurement/*.lean       formal artifact; cited as verification
future book drafts              audience-specific rewrites
```

Calibration is explicit physical practice: a reading without a named reference
is not a reading. Calibration is performed before measurement and carried into
measurement as a certificate.

Lean calibration reference:

- `device/Measurement/Calibration/LeanCalibration.lean`
- private `Reading` contains heartbeat `Nat`
- `EKG` exposes `Prop`-valued calibration questions
- `LOGICAL` carries `ekg : Calibration.EKG`
- `.load` initializes the baseline; `.boolean` reads it

Warnings to preserve:

- Exact Kolmogorov `K` is not implemented.
- Standard Model machinery is planned, not yet present in the Lean files.
- The physical book may discuss U(1), SU(2), SU(3), Dirac, Higgs, and related
  structures as the intended Ch 10 growth, but should not claim the current
  code already formalizes them.

## Chapter Map

| Ch | Area | Closed Question |
| --- | --- | --- |
| 1 | The Record | What is the smallest admissible mark a ledger can carry? |
| 2 | Comparison | How can an instrument compare records and repeat the result without pretending the comparison is the thing measured? |
| 3 | Phenomena | What can be said about the gap between recorded events without inventing structure not in the ledger? |
| 4 | Structure | How do multiple records combine without collapsing into one undifferentiated record? |
| 5 | Distance | How does a finite count of distinctions become an admissible notion of distance? |
| 6 | Motion | What selects one admissible continuation as the history actually carried forward? |
| 7 | Transport | How can information move between histories while preserving admissibility? |
| 8 | Stress | What reference structure lets distinct observers compare their counts as one physical record? |
| 9 | Strain | What records the failure of transport to commute? |
| 10 | Symmetry | What remains invariant under admissible relabeling or recompilation? |
| 11 | Entropy | Why does the record only grow, and when is it closed enough to support inference? |

---

## Generation Budget

Generate every chapter with the shared ritual from `three_gauges.md`:

- Unnumbered essay: about 1,500 words.
- Five numbered sections: use the table below.
- Phenomenon arcs: 1/3 setup, phenomenon box, 2/3 structural interpretation.
- Bridge: Short.
- Coda: about 2,000 words, using the coda candidate named in the chapter.

Book 2 is the heaviest volume. Medium sections usually carry apparatus,
numerical detail, calibration practice, or a physical derivation. All unlisted
numbered sections are Short.

| Ch | §1 | §2 | §3 | §4 | §5 |
| --- | --- | --- | --- | --- | --- |
| 1 | Short | Short | Short | Short | Short |
| 2 | Short | Medium | Medium | Short | Short |
| 3 | Short | Short | Short | Short | Short |
| 4 | Short | Short | Short | Short | Short |
| 5 | Short | Medium | Short | Short | Short |
| 6 | Short | Medium | Short | Short | Medium |
| 7 | Short | Medium | Short | Short | Medium |
| 8 | Medium | Medium | Short | Medium | Short |
| 9 | Medium | Short | Short | Medium | Short |
| 10 | Medium | Short | Short | Short | Short |
| 11 | Short | Short | Short | Short | Short |

Medium sections:

- Ch 2 §2 — The Radar Gun: Doppler Shift. Doppler derivation and relation to
  the speedometer thread.
- Ch 2 §3 — The GPS: Time of Flight. Four-satellite triangulation and the third
  instrument that agrees with the first two.
- Ch 5 §2 — Interferometry. Fringe counting as distance definition and the NIST
  meter standard.
- Ch 6 §2 — Euler-Lagrange from Data. The planet-at-two-positions argument
  against free continuation.
- Ch 6 §5 — Kepler's Orbits. `T^2 ∝ a^3` as a consequence, not an assumption.
- Ch 7 §2 — The Causal Doublet and Decoherence. Core quantum transport
  structure.
- Ch 7 §5 — Qubit Decoherence. `T_2` and the environment-as-ledger argument.
- Ch 8 §1 — Calibration Across Frames. GPS relativistic correction and the
  `38.7 μs/day` frame adjustment.
- Ch 8 §2 — The Pound-Rebka Experiment. Gravitational redshift data and the
  cleanest direct test in the chapter set.
- Ch 8 §4 — The Schwarzschild Metric. Two-frame admissibility and reference
  structure.
- Ch 9 §1 — Strain as Transport Failure. Gravity Probe B and the chapter
  definition.
- Ch 9 §4 — Gravitational Waves from LIGO. `h = ΔL/L` as direct curvature
  record.
- Ch 10 §1 — Noether's Theorem. Load-bearing mathematical argument before the
  Standard Model examples.

Post-pass candidate: Ch 10 §4 — Yang-Mills and Confinement may be promoted to
Medium if the Standard Model chapter becomes structurally dense. Keep the first
draft compressed and fix in post if needed.

---

## Ch 1 - What a Measurement Is

Closed question: What is the smallest admissible mark a ledger can carry?

Chapter job: make the event, instrument, mark, carrier, and distinction
physical. The reader should understand what a measurement does and what it
cannot contain.

Speedometer thread: the Hall-effect sensor fires once per magnetic tooth — 36
times per wheel revolution. Each firing is one event, one mark in the ledger.

### Sections and Key Examples

1. **The Event.** Key example: the Hall-effect sensor in a speedometer fires when
   a magnetic tooth passes — a voltage spike that lasts microseconds; this is
   the physical event that enters the ledger; events smaller than one tooth
   spacing are invisible to the instrument.

2. **The Carrier.** Key example: the voltage spike travels by wire to the ECU,
   which counts it as one tick; the ECU display carries the accumulated count as
   a number on the dashboard; the carrier (wire → ECU → display) is distinct from
   the event it carries.

3. **Distinguishability.** Key example: 36 teeth on the ring gear produce 36
   pulses per revolution; at 60 mph, a typical wheel completes about 13
   revolutions per second, producing ~470 pulses per second; two adjacent teeth
   are distinguishable because the sensor recovers between firings.

4. **Threshold and Noise.** Key example: at very low speed (below ~1 mph), the
   interval between pulses exceeds the display's update rate — the reading stays
   zero even though the car is moving; below the threshold, no event enters the
   ledger; the threshold is not a defect, it is the instrument's resolution limit.

5. **Calibration Before Measurement.** Key example: the speedometer is calibrated
   to a specific tire radius; if the driver switches to wider aftermarket tires,
   the pulse count per distance changes, and the display reads too low; the
   calibration certificate is the tire circumference, and it must be named before
   the measurement can be trusted.

Lean anchors:

- `device/Measurement/Episode1.lean`
- `Fact`, `Fact.Truth`, `Number`, `Number.le`
- `CarrierProcess`, `DISTINGUISHABLE`
- `Natural`, `CountingProcess`, `ADMISSIBLE`
- `Rational`, `IndexingProcess`, `COUNTABLE`
- `Sequence`, `LimitProcess`, `ENCODED`
- `Limit`, `CauchyProcess`, `RESIDUE`, `Sample`

Phenomena to place:

- Hume Effect: measurement always carries noise and induction pressure.
- da Vinci-Coulomb Effect: static friction as a threshold where distinction
  fails until burden is large enough.
- Pythagoras-Planck Effect should stay in Book 1 unless this chapter needs one
  very simple physical hook for "unit."

### Coda Candidate

Metaphor: a turnstile at a transit station.

The turnstile does not know the passenger. It records one admissible passage
when a threshold is crossed — a valid tap of a transit card against the
reader. Events smaller than one passage (the card hovering near the reader,
the passenger hesitating) are invisible to the instrument. The carrier is the
tap record, not the passenger. Two adjacent passengers are distinguishable
because the turnstile resets between firings. Below a certain tap speed,
the reader does not register — the event falls below threshold. The calibration
certificate is the current fare — named before the turnstile will accept a
passage. The turnstile performs event, carrier, distinguishability, resolution,
and calibration without knowing anything about where the passenger is going.

Overlap warning: none. The chapter's examples (Hall-effect sensor, ECU,
tooth spacing, threshold at low speed, tire calibration) are all specific to
the speedometer. The turnstile is urban transit — a completely different
physical domain. The five measurement primitives perform identically in both.

---

## Ch 2 - Three Ways to Measure

Closed question: How can an instrument compare records and repeat the result
without pretending the comparison is the thing measured?

Chapter job: speedometer, radar, and GPS as three instruments that tell the
same story about speed. The point is not that comparison is reality; it is
that comparison is the instrument's admissible interface with reality.

Speedometer thread: this chapter is where the three instruments are introduced
side by side — the speedometer counts pulses, the radar gun reads Doppler shift,
the GPS reads time-of-flight. All three give the same number. None of them
touch the speed itself.

### Sections and Key Examples

1. **The Speedometer: Pulse Counting.** Key example: 36 teeth × N revolutions/
   second × wheel circumference in meters = speed in m/s; the instrument never
   touches the speed — it counts magnetic events and multiplies by a calibration
   constant.

2. **The Radar Gun: Doppler Shift.** Key example: a police radar gun emits
   microwave radiation at f₀ ≈ 24 GHz; the reflected signal from a car moving
   at speed v is shifted to f_r = f₀ × (c + v)/(c - v); the gun measures the
   difference f_r - f₀ and recovers v; no physical contact with the car.

3. **The GPS: Time of Flight.** Key example: a GPS receiver reads timestamps
   from four satellites; each satellite's signal takes a known time to arrive;
   four distances triangulate the receiver's position; two positions separated
   by one second give speed; no wheel rotation involved.

4. **Repeatability.** Key example: a driver on a closed test track reads the
   same speed from all three instruments simultaneously; the agreement confirms
   that repeatability is not an accident but a structural consequence of the
   axioms; any discrepancy is instrument error, not a new physical fact.

5. **The Binary Interface.** Key example: the speedometer's ECU outputs exactly
   one number — it cannot say "the car feels fast" or "the road is slippery";
   the admissible output is a ratio; comparison is the only thing the instrument
   can do.

Lean anchors:

- `device/Measurement/Episode2.lean`
- `ObservationProcess`, `BINARY`
- `Trial`, `Trial.le`, `Trial.lt`
- `RepeatableProcess`, `REPEATABLE`
- `Study`, `Study.le`
- `ComputationalProcess`, `NUMERIC`

Phenomena to place:

- Kant Effect: measurement frame and admissible observation.
- Einstein Effect from `instrument/chapters/02.tex`: operational clock and
  synchronization.
- Fessenden-Shannon Effect: channel and instrument signal.
- Archimedes-Proust Effect: discrete ratio and physical proportion.
- Gosset Effect: keep here if framed as physical/industrial inference from
  small samples.
- Gauss's First Effect may appear as statistical regularity if not claimed by
  Book 1.

### Coda Candidate

Metaphor: three clocks in a railway control room.

The wall clock, the dispatch computer, and the stationmaster's pendulum
clock all compare the same train schedule through different instruments.
The wall clock counts seconds mechanically from a quartz oscillator; the
dispatch computer counts CPU ticks and converts to schedule time; the
stationmaster's pendulum clock counts swings of a calibrated rod. When all
three agree, the comparison is repeatable and the reading is admissible. When
they disagree, the disagreement is the diagnosis, not a new physical fact.
None of the three clocks touches the train's position — each carries a
different encoding of elapsed time, and the agreement is the measurement.
The control room performs `BINARY` (on time / not on time), `REPEATABLE`
(same train produces same comparison), `Study.le` (one schedule compared
against another), and `NUMERIC` (the count of on-time departures).

Overlap warning: none. The chapter's instruments are speedometer (magnetic
pulse count), radar gun (Doppler frequency), and GPS (satellite time-of-flight).
All three clocks in this coda are mechanical or electronic time-keepers, a
completely different instrument family. No overlap.

---

## Ch 3 - What Happens Between Measurements

Closed question: What can be said about the gap between recorded events without
inventing structure not in the ledger?

Chapter job: make interpolation a physical constraint, not a choice.

Speedometer thread: between two tooth pulses, the speedometer has no
information; if the car brakes hard and then accelerates between two pulses,
the display missed it; the instrument cannot say what happened in the gap.

### Sections and Key Examples

1. **The Gap.** Key example: a speedometer at 60 mph produces ~470 pulses per
   second; a hard braking event lasting 50ms falls entirely between two pulses
   and leaves no record; the gap is a physical fact about the instrument's
   resolution, not a defect to be repaired.

2. **Interpolation as Physical Constraint.** Key example: a bubble chamber
   photograph shows particle tracks as a sequence of bubbles; between bubbles,
   the track is not chosen freely — it is constrained by conservation of momentum
   and energy; the interpolation is forced by physics.

3. **The Minimum Admissible Continuation.** Key example: a seismologist has
   5 pressure readings at 5 times; the natural cubic spline is the unique
   continuation that introduces no structure beyond what the readings require;
   choosing a different interpolation would be asserting unrecorded structure.

4. **Noise and Signal.** Key example: a seismometer records ground motion
   continuously with ambient noise at -40 dB; the signal is the part that exceeds
   the noise floor and produces a distinguishable event; the noise floor defines
   the threshold below which the ledger cannot record.

5. **Metavariable in Measurement.** Key example: a clinical trial reports "the
   drug reduces systolic blood pressure by X mmHg" where X is still being
   analyzed; X is a metavariable carried in the record until the study closes;
   acting on X before the study closes is using an unresolved placeholder as a
   resolved result.

Lean anchors:

- `device/Measurement/Episode3.lean`
- `Computation`, `TuringProcess`, `REPRESENTABLE`
- `ChaitinsNumberSequence`
- `NoisyProcess`, `PHYSICAL`
- `Metavariable`, `PhysicalProcess`, `COMPARABLE`
- `Sophism`, `SlipProcess`, `OBSERVED`, `Area`
- `device/Measurement/Episode4.lean`: `Phenomenon`

Phenomena to place:

- Celsius-Lagrange Effect: future work. Inside here if source box argues
  interpolation as physical instrument practice. Outside if it is mathematical.
- Adams Effect: future work. Inside here if source box argues burden of
  physical representation. Disposition requires reading the source box.

Disposition: Galileo-Abel Effect is inside Book 1 Ch 3 (mathematical
topological constraint). It does not move to Book 2.

### Coda Candidate

Metaphor: security camera footage with missing frames.

A forensic investigator reviews camera footage of a corridor. The camera
records at 10 frames per second; an event of interest lasted 80 milliseconds
— it falls between two frames and leaves no direct record. The investigator
may not freely invent what happened between the frames. The visible frames
constrain admissible reconstructions: motion blur, the positions of objects
at frames N and N+2, and the known frame rate bound what could have occurred
at frame N+1. The gap is a physical fact about the camera's resolution, not
a defect to be repaired. The investigator performs only `Metavariable`
inference — the missing frame is a placeholder whose resolution is constrained
by the boundary data.

Overlap warning: the chapter's examples (speedometer gap at 50 ms, bubble
chamber track, seismometer noise floor, clinical trial metavariable) are all
scientific instruments. The security camera is surveillance and forensic —
a completely different institutional context. The interpolation constraint
performs without collision.

---

## Ch 4 - The Grammar of Experiments

Closed question: How do multiple records combine without collapsing into one
undifferentiated record?

Chapter job: experimental compatibility, apparatus grammar, and unresolved
states held without premature closure.

Speedometer thread: the speedometer, odometer, and clock form a compatible
experimental state — if the speedometer reads 60 mph for one hour, the odometer
must show 60 more miles; a disagreement between them is the error, not a new
discovery.

### Sections and Key Examples

1. **Experimental State.** Key example: a weather station — barometer,
   thermometer, anemometer, and rain gauge form a compatible experimental state;
   they measure the same atmosphere at the same moment; the state is the
   conjunction of all four readings.

2. **Apparatus Accountability.** Key example: LIGO's two 4-km arms measure
   gravitational wave strain at h ~ 10⁻²¹; the apparatus grammar specifies
   which disturbances count as signal (differential arm length change) and which
   are noise (seismic, thermal, laser shot noise); without this grammar, any
   reading could be attributed to anything.

3. **Compatible Records.** Key example: speedometer + GPS + odometer must agree
   — if the speedometer reads 60 mph but GPS shows 40 mph, one instrument is
   miscalibrated; the disagreement is the diagnosis, not a new measurement.

4. **Unresolved States Held Open.** Key example: a double-slit experiment before
   a detector is placed — both paths are open simultaneously; collapsing the
   state prematurely (by peeking at which slit the particle used) destroys the
   interference pattern; the unresolved state must be held open.

5. **Source / Compile / Execute.** Key example: a measurement protocol is the
   source document (how to run the experiment); a calibrated instrument is the
   compiled version (the protocol instantiated in hardware); the actual
   measurement run is the execution; all three are distinct physical objects.

Lean anchors:

- `device/Measurement/Episode4.lean`
- `Area`, `SensingProcess`, `PRESENT`
- `Phenomenon`, `Phenomenon.le`
- `GaugeProcess`, `MEASURABLE`
- `Jar`, `MeesaProcess`, `GUNGAN`
- `device/Measurement/Episode5.lean`
- `Equivalation`, `DigitalProcess`, `SOURCE`
- `Encoding`, `CompiledProcess`, `EXECUTED`, `Abstraction`

Phenomena to place:

- Stoichiometry Effect: move here from overloaded Ch 7; chemical ratios are a
  discrete structural constraint on experimental records.
- Hall-Einstein-Podolsky-Rosen Effect: compatible/incompatible records and
  correlation pressure.
- Markov-Conway Effect: use if the source box emphasizes experimental state
  transition or grammar.

### Coda Candidate

Metaphor: a hospital operating room checklist.

Before surgery begins, the team runs a structured pre-operative checklist:
patient identity confirmed, correct procedure named, site marked, anesthesia
check complete, imaging reviewed, instruments counted. Each item is a distinct
record — patient ID, imaging, anesthesia log, instrument count — and they
must all be in a compatible state before action is admissible. Skipping a
checklist item, or completing it out of order, does not merely introduce risk;
it breaks the experimental grammar of the procedure. The checklist performs
`GaugeProcess` (the ordered process of readying the experimental state),
`MEASURABLE` (each item must have an admissible reading before it is checked),
`SOURCE` (the protocol, prior to instantiation), `Encoding` (the completed
checklist, instantiated for this patient), `EXECUTED` (the surgery itself),
and `Abstraction` (the principle that these five record types must compose
before any action is admissible).

Overlap warning: none. The chapter's examples (weather station, LIGO grammar,
speedometer/GPS/odometer agreement, double-slit, measurement protocol) are all
scientific or physical. The OR checklist is medical and procedural. The record
composition performs without collision.

---

## Ch 5 - Distance

Closed question: How does a finite count of distinctions become an admissible
notion of distance?

Chapter job: distance as finite refinement count, not metaphysical continuum.

Speedometer thread: the odometer integrates the speedometer — distance equals
the sum of speed × time over each pulse interval; the odometer is the Riemann
sum, and the true distance is its Cauchy limit.

### Sections and Key Examples

1. **Distance as Refinement Count.** Key example: a laser rangefinder counts
   round-trip photon travel time in nanoseconds; at 3 × 10⁸ m/s, one nanosecond
   = 30 cm; distance is the count of nanoseconds, not a laid-down ruler; no
   ruler touches the target.

2. **Interferometry.** Key example: the Michelson interferometer counts
   interference fringes — each fringe is one half-wavelength of path difference;
   at 633 nm (HeNe laser), one fringe = 316.5 nm; NIST uses this to define the
   meter in terms of wavelengths counted.

3. **The Heisenberg Trade-off.** Key example: to measure an electron's position
   to within Δx, a photon of wavelength ≤ Δx must be used; that photon carries
   momentum ≥ h/Δx; the act of measurement disturbs the thing measured; the
   trade-off is built into the structure of distinguishable events, not into
   the theory of quantum mechanics as an add-on.

4. **Malus Effect.** Key example: polarized light through a polarizer at angle θ
   — intensity ∝ cos²θ; at 90°, nothing passes; the polarizer is a distance
   gate: it measures the angular separation between the light's polarization and
   the filter's axis, and passes only the aligned fraction.

5. **Odometer as Spline.** Key example: a car travels at variable speed; the
   odometer accumulates distance = Σᵢ speedᵢ × Δtᵢ over each pulse interval;
   as the pulse interval shrinks (higher tooth count), the sum converges to the
   integral ∫v dt; the integral is the spline limit of the Riemann sum.

Lean anchors:

- `device/Measurement/Episode6.lean`
- `MathematicalProcess`, `VALUE`
- `Sum`, `AddingProcess`, `MAGNITUDE`
- `Product`, `MultiplyingProcess`, `SCALED`
- `Basis`, `BASICProcess`, `LOAD`
- `Polynomial`, `GalerkinProcess`, `FINITE_ELEPHANT`
- `Spline`, `Spline.le`

Phenomena from Claude:

- Heisenberg Effect as Trade-off
- Malus Effect

Disposition: Pareto Effect is outside Book 2. It is inside Book 3 Ch 6
(informational weight concentration / compressibility reading). If the source
box is later rewritten as a physical power-law example it may return, but
that requires a rewrite of the source box, not a reassignment.

### Coda Candidate

Metaphor: a tailor measuring a suit with a calibrated tape.

The tailor takes a chest measurement: tape around the chest at a named
posture (arms relaxed at sides), at a named moment (end of breath), using a
calibrated linen tape (not a steel rule, which would not bend, and not a
string, which would stretch). The measurement is `MAGNITUDE` (the number
of centimeters), `SCALED` (relative to the tape's calibrated unit), and
`LOAD` (the amount of tape stretched across the chest — the resource budget
for the measurement). A Heisenberg-like tradeoff appears in the posture
constraint: measuring chest and waist simultaneously at the same tension is
not possible — the posture required for one distorts the other. The admissibility
gate is the tailor's professional judgment that this tape, at this tension,
in this posture, is the calibrated reference.

Overlap warning: the chapter's examples (laser rangefinder, Michelson
interferometer, Heisenberg trade-off, Malus polarizer, odometer as Riemann sum)
are all instrument-based. The tailor is craft and commerce — a physical
practice, but not a laboratory. The distance structures perform without
collision. Do not use the phrase "Malus-like gating" in the coda prose;
write "admissibility gate" or "resolution threshold" instead, since Malus is
assigned to this same chapter.

---

## Ch 6 - Classical Mechanics

Closed question: What selects one admissible continuation as the history
actually carried forward?

Chapter job: least action as a measurement consequence, not a postulate.

Speedometer thread: a car's trajectory between two measured positions is the
path of least action — no superfluous acceleration is introduced between the
measured events; the speedometer's interpolation assumption (constant speed
between pulses) is the minimal-information extension.

### Sections and Key Examples

1. **Least Action.** Key example: a ball rolls off a table; given its position
   at t = 0 and t = 1 second, Lagrangian mechanics predicts the parabola — no
   other path with those two endpoint positions has stationary action; the
   selection is unique and forced.

2. **Euler-Lagrange from Data.** Key example: a planet observed at two positions
   six months apart — Newton's law plus the observation data forces the ellipse;
   no other conic section is consistent with both the inverse-square law and
   both position measurements.

3. **Repeatability of Invisible Motion.** Key example: Galileo's inclined plane
   — two observers timing a ball with different clocks both recover the same
   parabolic trajectory, because it is the only path consistent with both
   endpoint measurements regardless of which clock is used.

4. **The Free Parameter.** Key example: given the two endpoint positions of a
   thrown ball, the trajectory has one remaining free parameter — the initial
   speed (equivalently, the launch angle for fixed endpoints); in the spline,
   this is Ψ''', the constant third derivative; one measurement resolves it.

5. **Kepler's Orbits.** Key example: Mars observed at opposition and six months
   later — the two positions plus the elapsed time force an ellipse with the Sun
   at one focus; Kepler's third law (T² ∝ a³) is a consequence, not an
   assumption; the orbit is the minimal-information continuation.

Lean anchors:

- `device/Measurement/Episode6.lean`: `GalerkinProcess`, `Spline`,
  `FINITE_ELEPHANT`
- `device/Measurement/Episode7.lean`: `ArmWaveProcess`, `BULLSHIT`,
  `Diatribe`, `CrusadeProcess`, `PROPAGANDA`, `Cult`, `InitiationProcess`,
  `ACOLYTE`
- `device/Measurement/Calibration/LeanCalibration.lean`: `EKG`

Phenomena from Claude:

- Repeatability of Invisible Motion

Phenomena moved here from Ch 7 (distribution pass, confirmed):

- Brownian Motion Effect
- Casimir Effect
- Momentum Effect
- Harmonic Oscillator
- First Effect of Gibbs
- Thermostat Effect
- Kepler Effect

These are inside Book 2 Ch 6. They are not a "suggested move" — they are
the classical dynamics canon that was overloading Ch 7.

### Coda Candidate

Metaphor: a figure skater tracing one clean arc between two chalk marks.

The marks are fixed on the ice. Many paths are imaginable — the skater could
spiral, stutter, cross-step. But the ice, the blade geometry, the skater's
speed, and the endpoint constraints together admit one arc that minimizes
wasted motion: the path of least added curvature given the constraints. Any
other path would require force not recorded in the setup data. The skater's
arc is the least-action solution performed in a physical register completely
distinct from Lagrangian mechanics. The selection is unique and forced — not
chosen from preferences but extracted from constraints.

Overlap warning: the chapter's examples (ball rolling off a table, planet
at two positions, Galileo's inclined plane, Kepler ellipse) are all explicitly
Newtonian or astronomical. The ice rink is sporting, kinesthetic, and
immediately visual. The selection principle performs without collision.

---

## Ch 7 - Quantum Mechanics

Closed question: How can information move between histories while preserving
admissibility?

Chapter job: quantum transport as physical measurement — clocks, correlations,
decoherence, and the Causal Doublet.

Speedometer thread: the speedometer has a one-tooth resolution floor —
analogous to ℏ; below the floor, the position of a tooth event cannot be
further refined; quantum effects describe what happens when two admissible
paths cannot be distinguished even in principle.

### Sections and Key Examples

1. **The Wittgenstein Effect: After is Free.** Key example: a photon passes
   through a beam splitter in a Mach-Zehnder interferometer; the "which path"
   relationship between the two arms costs nothing informationally until a
   detector is placed; the "after" connective is syntactic, not physical.

2. **The Causal Doublet and Decoherence.** Key example: a two-slit experiment
   — both slits are open (doublet state); a detector at one slit collapses the
   doublet; the decoherence rate γ = λ²/2D quantifies how quickly the
   environment records which slit was used.

3. **Spooky Action at a Distance.** Key example: the Bell-Aspect test (1982) —
   two entangled photons measured at polarizers separated by 13 meters; the
   correlation violates Bell's inequality by 5 standard deviations; no local
   hidden variable can reproduce it; the uncorrelant collapses non-locally when
   either photon is measured.

4. **Davisson-Germer.** Key example: electrons at 54 eV fired at a nickel
   crystal diffract at 50°, exactly as predicted for de Broglie wavelength
   λ = h/p; the electron has no definite path between the gun and the crystal;
   the diffraction pattern is the sum over all admissible paths.

5. **Qubit Decoherence.** Key example: a superconducting transmon qubit at 15 mK
   has a coherence time T₂ ~ 100 μs; each interaction with the environment
   records partial "which state" information; the doublet collapses to a definite
   state at rate 1/T₂ as the environment accumulates admissible records.

Lean anchors:

- `device/Measurement/Episode8.lean`
- Instance cascade `STEP_1` through `ACOLYTE_PROPAGANDA`
- `device/Measurement/Episode9.lean`
- `Science`, `LearningProcess`, `SCIENTIFIC`
- `Knowledge`, `Knowledge.le`, `ScientificProcess`, `TRUTH`
- `Gospel`, `ReligiousProcess`
- `device/Measurement/Episode10.lean`: `WITNESSED`

Core keep list from Claude:

- Wittgenstein Effect
- LiDAR
- Davisson-Germer Effect
- Entanglement Effect
- Mach-Zehnder Effect
- Bell-Aspect Tests
- Hawking Radiation Revisited as the physical particle-pair version
- Qubit Decoherence
- Spooky Action at a Distance

Disposition: Paradoxes of Time Travel is outside the phenomenon set. It
becomes a single cautionary \NB in the chapter prose only. Do not write a
phenomenon box for it.

Disposition: Shadow Tomography is outside Book 2 Ch 7. It belongs to Book 3
Ch 7 (quantum algorithm).

Disposition: Alpha-Decay and Gamma Decay are outside Book 2 Ch 7. They are
inside Book 3 Ch 7 (stochastic transition algorithms).

Disposition: Cause-Effect Effect (Wigner's friend) is inside Book 2 Ch 7.
The observer-as-part-of-the-record argument is a physical measurement question,
not a structural one.

### Coda Candidate

Metaphor: a sealed routing room for diplomatic pouches.

Diplomatic pouches move through a routing room: each pouch is sealed and
numbered on entry, logged at each transfer, and arrives at its destination
with a chain-of-custody record. The routing room cannot open the pouches
without breaking the seal — inspecting the contents changes the record
(decoherence). Two pouches from the same sender may be correlated (same
origin, same day, same key) in a way that is not visible from the outside
of either pouch individually; their correlation is only detectable when both
arrive and are compared — the Causal Doublet. The `WITNESSED` certificate is
the unbroken seal on delivery: proof that the pouch was transported through
an admissible process. When the seal is broken (measurement), the correlation
either holds or it does not.

Overlap warning: none. The chapter's examples (Mach-Zehnder interferometer,
two-slit doublet, Bell-Aspect test, Davisson-Germer diffraction, superconducting
qubit) are all laboratory quantum experiments. The diplomatic routing room is
institutional, administrative, and human-scale. The transport and witnessing
structures perform without collision.

---

## Ch 8 - General Relativity

Closed question: What reference structure lets distinct observers compare their
counts as one physical record?

Chapter job: reference structure, calibration, metric, and frame comparison.

Speedometer thread: a GPS-equipped speedometer requires relativistic correction
— satellite clocks run fast by 38.7 μs/day relative to Earth-surface clocks
(special relativity slows by 7.2, general relativity speeds by 45.9); without
correction, GPS position drifts ~10 km/day; the calibration certificate must
carry the frame correction.

### Sections and Key Examples

1. **Calibration Across Frames.** Key example: GPS satellites at 20,200 km
   altitude moving at 3.9 km/s require two relativistic corrections to their
   onboard cesium clocks; the net correction is +38.7 μs/day; without it, GPS
   position drifts 10 km/day; the calibration certificate is the relativistic
   frame adjustment.

2. **The Pound-Rebka Experiment.** Key example: a Mössbauer gamma-ray source at
   the base of a 22.6 m tower at Harvard (1959); the signal received at the top
   is blueshifted by Δf/f = gh/c² = 2.46 × 10⁻¹⁵; this matches GR to 1%;
   the blueshift is the bookkeeping adjustment that maintains consistent
   refinement counts across the height difference.

3. **Michelson-Morley.** Key example: the 1887 experiment searched for the
   luminiferous ether by comparing light speed in perpendicular directions; the
   null result — no fringe shift at any orientation — proved the speed of light
   is the same in all directions; the informational metric is Lorentz-invariant.

4. **The Schwarzschild Metric.** Key example: the event horizon at r_s = 2GM/c²
   is where the gravitational time dilation becomes infinite — clocks stop; from
   outside, nothing is seen to cross the horizon in finite time; from inside, the
   horizon has already been crossed; the two frame-dependent descriptions are
   both admissible.

5. **The Atomic Clock as EKG.** Key example: the cesium-133 atom defines the
   SI second as 9,192,631,770 oscillations of its ground-state hyperfine
   transition; this is a physical EKG — a heartbeat-like reference whose count
   rate all other measurements are compared against; the atom is the calibration.

Lean anchors:

- `device/Measurement/Episode10.lean`
- `Truth`, `Truth.le`, `UniverseTensor`, `REAL`
- `Variation`, `BigRedDogProcess`, `LOCAL`
- `device/Measurement/Calibration/LeanCalibration.lean`: `EKG`

Phenomena from Claude:

- Precision
- Richardson Effect
- von Neumann Effect
- Compact Disc Encoding
- Bacon Effect
- Galileo Effect
- Einstein Effect from `instrument/chapters/08.tex`
- Michelson-Morley Effect
- Sagnac Effect
- Foucault Effect
- Bayes Effect
- Pound-Rebka Effect
- Schwarzschild Effect
- Event Horizon Effect

Notes:

- Pound-Rebka belongs here, not Ch 6.

Disposition: Message Effect is outside Book 2 Ch 8. Inside Book 3 Ch 9
(algorithmic communication/transport failure).

Note: Ch 8 has 14 phenomena assigned. The chapter budget supports 8--10 arcs.
At draft time, cut to the core: Precision, Pound-Rebka, Einstein Effect,
Michelson-Morley, Sagnac, Schwarzschild, Event Horizon, and one of (Bacon /
Galileo / Foucault) as the repeatability/frame anchor. The remaining 5--6 are
inside the book but should be compressed into prose references rather than
full phenomenon boxes.

### Coda Candidate

Metaphor: an international time-standard conference.

Representatives from national metrology institutes (NIST, PTB, BIPM) meet to
compare their cesium clocks. Each institute keeps a local clock: locally it
runs perfectly, but they drift apart over months. The conference establishes
TAI (International Atomic Time) — a weighted average that all clocks are
compared against. Before the conference, each clock's reading is a `LOCAL`
claim; after calibration across frames, the agreed reading is `REAL` (a
shared reference). `EKG` is the heartbeat-like reference that each clock
contributes; `UniverseTensor` is the consistency matrix that closes the
comparison (clock A vs. clock B vs. clock C must be mutually consistent);
the reference certificates are the calibration adjustments distributed after
the conference.

Overlap warning: the chapter's examples (GPS relativistic correction, Pound-
Rebka gravitational redshift, Michelson-Morley null result, Schwarzschild
metric, cesium-133 SI definition) are all specific physical experiments. The
time-standard conference is institutional and metrological — the politics and
bureaucracy of calibration, not the physics. The reference structures perform
without collision.

---

## Ch 9 - The Einstein Equations

Closed question: What records the failure of transport to commute?

Chapter job: strain, curvature, balance, and physical consequences.

Speedometer thread: when a car turns, the inner and outer wheels travel
different distances for the same steering angle; the speedometer reads from
one wheel and is miscalibrated during turns; the mismatch is the physical
signature of curvature in the odometer record.

### Sections and Key Examples

1. **Strain as Transport Failure.** Key example: Gravity Probe B (2011) measured
   geodetic precession of 6,606 mas/yr and frame-dragging of 37.2 mas/yr for a
   gyroscope in polar orbit; the precession angle is the curvature accumulated
   by parallel-transporting a gyroscope around a closed orbit; it is nonzero
   because spacetime is curved.

2. **The Navier-Stokes Third Parameter.** Key example: turbulence in a river
   becomes chaotic when the velocity gradient (second derivative) grows large
   enough to feed the third parameter Θ = ∇(∇²v); the millennium prize question
   is whether Θ can blow up in finite time; the answer determines whether smooth
   global solutions exist.

3. **Flat Rotation Curves.** Key example: stars at 30 kpc from the Milky Way's
   center orbit at the same speed as stars at 8 kpc; for a visible-matter disk,
   speed should fall as 1/√r beyond the disk; the flat curve requires five times
   more mass than is visible; the curvature budget does not balance without dark
   matter.

4. **Gravitational Waves from LIGO.** Key example: GW150914 (2015) — two black
   holes of 36 and 29 solar masses merged 1.3 billion years ago; the wave
   stretched and compressed the LIGO arms by 10⁻¹⁸ m (~1/1000 of a proton
   radius); the strain h = ΔL/L is the direct physical record of curvature
   carried as a wave.

5. **Neutrino Oscillations.** Key example: solar neutrinos produced as electron
   flavor arrive at Super-Kamiokande as a mixture of all three flavors; the
   oscillation length is set by the mass-squared differences; the flavor is not
   conserved under transport through space — it is the physical signature of
   curvature in the neutrino mass matrix.

Lean anchors:

- `device/Measurement/Episode11.lean`
- `SpaceTimePath`, `SpaceTimePath.le`
- `CalculusProcess`, `UNIVERSAL`
- `YarnTheory`, `YarnTheory.le`
- `HeartbeatProcess`

Phenomena from Claude:

- Time Effect
- Navier-Stokes Effect
- Arago Effect
- Flat Rotation Curve Effect
- Angular Momentum Effect
- Neutrino Effect
- Strong Interaction Effect
- Hawking Effect as black-hole area/entropy.

Disposition: Hawking Effect (area/entropy) — keep a distinct box here only
if the curvature argument is independent from the particle-pair argument in
Ch 7. If the Ch 9 source box recaps Ch 7, merge the area/entropy content
into Book 2 Ch 11 and remove the Ch 9 box.

### Coda Candidate

Metaphor: a bridge deck with expansion joints under changing heat.

A steel bridge deck is divided into segments joined by expansion joints. When
temperature rises, each segment expands; when temperature falls, it contracts.
The joints record the mismatch: if segment A expands more than segment B (due
to different sun exposure, different alloy composition), the joint gap changes.
Transporting a structural load across the bridge fails if the strain is ignored
— bolts shear, welds crack. The joint gap is the physical record of transport
failure. `SpaceTimePath` is the load's path across the bridge; `YarnTheory`
is the stress analysis that tracks how force propagates from joint to joint;
`HeartbeatProcess` is the monitoring sensor recording thermal cycles; curvature
as recorded transport failure is the visible in the joint gap measurements.

Overlap warning: none. The chapter's examples (Gravity Probe B, Navier-Stokes
turbulence, flat rotation curves, LIGO gravitational waves, neutrino oscillation)
are all cosmological, quantum, or fluid-mechanical. The bridge deck is civil
engineering and materials science. The transport-failure structure performs
without collision.

---

## Ch 10 - The Standard Model

Closed question: What remains invariant under admissible relabeling or
recompilation?

Chapter job: physical invariants, Noether, gauge fields, spin, matter, and
future Standard Model expansion.

Speedometer thread: the speedometer reading is invariant under rotation of the
car — speed does not depend on which direction you drive; the odometer is not
invariant under time reversal (it always adds, never subtracts); these two
symmetries (spatial and temporal) correspond to different conservation laws.

### Sections and Key Examples

1. **Noether's Theorem.** Key example: the hydrogen spectrum — energy levels are
   exactly predictable because U(1) gauge invariance forces conservation of
   electric charge; the symmetry of the action (invariance under phase rotation)
   implies the conserved current (electric charge).

2. **The Photoelectric Effect.** Key example: Einstein (1905) — light below a
   threshold frequency ejects no electrons, regardless of intensity; light above
   threshold ejects electrons with energy E = hf - φ; the quantization is forced
   by U(1) gauge symmetry of electromagnetism, not by an assumption about photons.

3. **Spin-1/2 and the Stern-Gerlach Experiment.** Key example: silver atoms
   passed through an inhomogeneous magnetic field split into exactly two beams —
   not a continuous spread; spin is an invariant under SU(2) that takes exactly
   two values (±ℏ/2); no intermediate values are admissible.

4. **Yang-Mills and Confinement.** Key example: quarks are permanently confined
   inside protons and neutrons — no free quark has ever been observed; the SU(3)
   gauge group of the strong force produces a potential that grows with distance
   rather than falling; at large separation, it is energetically cheaper to
   create a new quark pair than to separate the originals.

5. **Chirality and Parity Violation.** Key example: the Wu experiment (1957) —
   cobalt-60 nuclei aligned by a magnetic field decay preferentially in one
   direction; the weak force violates parity; the universe distinguishes left-
   handed from right-handed fermions at the fundamental level; chirality is the
   invariant that the weak force does not preserve.

Lean anchors:

- `device/Measurement/Episode12.lean`
- `LOGICAL`, `ComputerProgram.le`, `ElaborationProcess`, `HALTED`
- `device/Measurement/Episode13.lean`
- `Measurement`, `Measurement.le`, `LeanProcess`, `MEASURED`
- `device/Measurement/Episode14.lean`
- `CompilerTape`, `CompilerOutput`, `COMPILED`

Phenomena from Claude:

- Photoelectric Effect
- Compton Scattering Effect
- Conservation of Energy / Noether
- Spin-1/2 Effect
- Sombrero Potential
- Yang-Mills Effect
- 't Hooft-Susskind Effect
- Dirac Operator
- Chirality Effect

Phenomenon to merge:

- Harmonic Oscillator Revisited should merge back into Ch 6 or Ch 7, not stand
  alone here.

### Coda Candidate

Metaphor: a choreographed performance surviving costume and stage changes.

A company of dancers performs a work that was choreographed twenty years ago.
The original cast has retired; the costumes have been redesigned; the stage
is smaller. The choreography is invariant: it specifies the relationships
between bodies, the timing, the spatial patterns — not the specific dancers,
not the costumes, not the stage dimensions. When a dance work is "the same
performance," it is because the relational invariant survived the substitution.
When it is not — when parity is violated, when the choreography's left-handed
gestures are mirrored without authorization — the invariant breaks and
detectable asymmetry appears. The performance enacts symmetry (the
choreographic structure survives relabeling), conserved motion (the energy
of the form is preserved), broken symmetry (when an unauthorized mirroring
occurs, the original choreography distinguishes left from right), chirality
(the weak-force analog: this choreography is left-handed at the structural
level), and gauge constraint (the choreographic notation is the admissibility
rule).

Overlap warning: the chapter's examples (Noether/U(1)/hydrogen spectrum,
photoelectric effect, Stern-Gerlach/SU(2), Yang-Mills/confinement, Wu
experiment/chirality) are specific particle physics experiments. The
choreography is performing arts and institutional memory. Explicitly avoid
claiming the current Lean code formalizes Standard Model gauge groups; the
choreography metaphor carries this gracefully without pretending.

---

## Ch 11 - Thermodynamics

Closed question: Why does the record only grow, and when is it closed enough to
support inference?

Chapter job: irreversibility, erasure, physical memory, horizon, and closure.

Speedometer thread: the odometer is a physical example of an append-only
record — every mile driven adds to the total; driving in reverse adds more
miles, not fewer; the record is physically irreversible; you cannot un-drive
a mile any more than you can unburn a log.

### Sections and Key Examples

1. **Irreversibility.** Key example: the odometer counts only forward — driving
   one mile forward and one mile backward gives an odometer reading of 2 miles,
   not 0; the physical act of moving has left an irreversible mark in the record;
   the second law says the total mark (entropy) never decreases.

2. **Landauer's Principle and Erasure Cost.** Key example: IBM researchers (2012)
   confirmed Landauer's principle experimentally — erasing one bit of information
   in a colloidal particle system required at minimum k_B T ln 2 = 2.87 × 10⁻²¹
   J; the cost of erasure is physical, not just informational.

3. **Maxwell's Demon.** Key example: a demon sorts fast and slow gas molecules
   into two sides of a box, appearing to decrease entropy for free; Bennett (1982)
   showed the demon must erase its memory after each measurement, paying k_B T ln 2
   per erasure; the odometer of the demon's memory cannot go backward.

4. **Dark Energy.** Key example: type Ia supernovae at z ≈ 1 are fainter than
   expected — the expansion of the universe is accelerating; the cosmological
   constant Λ acts as a repulsive dark energy; the record of cosmological
   expansion is append-only (the universe cannot contract back to its initial
   state while accelerating).

5. **The Meissner Effect.** Key example: a superconductor cooled below T_c expels
   all magnetic flux from its interior — the Meissner effect; the exclusion is
   not just a consequence of zero resistance but a topological closure; the
   flux cannot enter because the winding number of the order parameter around
   any loop must be an integer, and the transition closes the record of flux
   threading.

Lean anchors:

- `device/Measurement/Episode15.lean`
- `Bullshit`, `Bullshit.le`, `Bullshit.lt`
- `AtreyuProcess`, `TrueOutput`
- `truthCarrier`, `DISTINGUISHABLE_PROP`, `truthDistinct`
- `Fact.SAME`
- `Closure`, `Closure.le`, `EquivalenceProcess`
- `INFERRED`, `INFERRED_TRUE`
- `theory_true?`

Phenomena from Claude:

- Entropic Cost of Acceleration
- Thermodynamic Cost of Erasure
- Maxwell's Demon
- Meissner Effect
- Dark Energy Effect
- White Hole Effect

Disposition: Thermostat Effect is outside Book 2 Ch 11 as a full phenomenon.
It may be referenced here only as feedback/control vocabulary; its main
placement is Book 2 Ch 6.

### Coda Candidate

Metaphor: a bakery cash register at closing time.

The register records every sale, refund, spoilage entry, and till count
during the day. At closing, the baker reconciles: every loaf sold is a credit;
every returned loaf (too hard, wrong order) is a debit; every loaf thrown out
at end of day is a spoilage entry. The register cannot simply un-sell bread —
each transaction leaves a physical record in the ledger, and the ledger is
append-only. The till count at closing is the physical record of every thermal
event (baking, cooling, selling) that occurred during the day. Erasing a sale
from the register requires a refund entry — a physical act that costs as much
as the original entry. The bakery performs append-only record, erasure cost
(Landauer: you cannot erase the spoilage without entering a write-off),
memory (the day's transactions are the demon's memory), closure (the register
closes when the till is counted), and physical entropy (the bread is gone,
the heat is dissipated, the energy cannot be recovered as unbaked dough).

Overlap warning: none. The chapter's examples (odometer as append-only,
Landauer experiment with colloidal particle, Maxwell's Demon/Bennett, dark
energy/supernovae, Meissner effect) are all physical experiments or
cosmological observations. The bakery is commercial, quotidian, and food-based.
The entropy structures perform without collision. "Can't un-sell bread" is the
right note to end the coda on.

---

## Resolved Placements

- Cause-Effect Effect (Wigner's friend): inside Book 2 Ch 7. The observer-as-
  part-of-the-record argument is a physical measurement question. Do not move
  it to Ch 4.
- Message Effect: outside Book 2. Inside Book 3 Ch 9 (algorithmic transport
  failure).
- Ch 9 Hawking Effect: keep a distinct box only if the curvature/area argument
  is independent from the Ch 7 particle-pair argument. If the source box
  recaps Ch 7, merge the area/entropy material into Ch 11 and remove the Ch 9
  box.
