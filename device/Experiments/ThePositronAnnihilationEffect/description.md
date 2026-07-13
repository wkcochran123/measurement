# The Positron Annihilation Effect

**Register.** Physical experiment, treated as a *representation* of the device's roster, on the near side: the electron (minus), the positron (plus), and the null (zero) they meet at are read as the three roles the calibration rotates through --- a model of the roster, never a claim about what an electron and a positron are in themselves when they meet (that stays on the far side). In electron-scope: the positron is the +1 role of the electron's own calibration, not an extrapolation past it. Used in Vol5 Ch4 §4.2 as the physical face of the sign-fold's roster. Build verified: `claim_holds` depends on `[propext]`.

**Source phenomenon.** A positron is detected by its *annihilation*. When a positron meets an
electron the two signed charges cancel and the rest energy leaves as two 511 keV gamma photons,
emitted **back-to-back** (momentum balance). A coincidence detector confirms a positron was
present when it registers two photons, both within a finite window around the 511 keV line (the
noise floor) and travelling in opposite directions.

In a superconducting realisation the annihilation deposits its energy by **breaking Cooper pairs
into quasiparticles**, which is how superconducting single-quantum calorimeters (TES / MKID /
SNSPD) detect single events. (The *holonomy* reading of the same physics — the signed phase a
Cooper-pair loop accumulates around a flux — is the device-episode counterpart; this experiment
is the annihilation/coincidence face.)

**What the model is.** A finite ledger model of the coincidence logic: `Photon` (energy + a
direction slot on a finite ring), `Detector` (the 511 keV line, an acceptance window, a slot
count), and the rule `registers = onLine p ∧ onLine q ∧ backToBack p q`. The annihilation half —
that the electron and positron readings cancel, and that a positron is what an asymmetric
baseline yields — is taken **directly from the device** (`Measurement.split_cancels`,
`Measurement.positron_over_tiltedPath`, Episodes 82–83), so a device regression breaks this test.

**Claim ceiling:** `finiteLedgerModel`.

**Explicitly NOT claimed:** that this detects real antimatter; that 511 keV is derived (it is a
labelled constant — the electron rest energy); any QED amplitude; anything about the *rate* of
annihilation. The model proves the finite coincidence logic and inherits the device's
charge-cancellation theorem — nothing more.

**This file is also the EXEMPLAR** the testing team should copy (see `../FEEDBACK2.md`): an
effect-specific domain type, genuinely falsifiable quantified lemmas
(`not_backToBack_not_registered`, `offLine_not_registered`), a content-bearing claim, an honest
tag, explicit `Decidable` instances so `decide`/`#eval` work, and a real coupling to
`Measurement`.
