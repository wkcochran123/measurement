# 011 — The throw

The author's: the Compton time is the time it takes to throw a bent card. The device's bent card is `Quot.sound`. This
experiment puts one throw of it on the meter, beside the same statement with nothing thrown, and asks whether the throw
costs the floor, the step that belongs to the device's truth, or neither.

- `probe_sound.lean`, `probe_sound_control.lean`: `Quot.sound` applied once, and the same statement by `rfl`.
- `probe_propext.lean`, `probe_propext_control.lean`: the other axiom, and its control.
- `probe_truth.lean`: the click of the device's truth read as a term. `probe_named.lean`: Episode 8's own throw by name.
  Output of each: `BLANK 0 hb`, then `READ pass label beat blank` twice.
- `run_throw.sh <CARD_2> <this folder> <runs>`; `analyze_throw.py <raw dir>`; `probes.list`.
- `SEALED_PREDICTION.txt`: written before any output was read. The repository ignores `*.txt`, so the seal is
  reproduced in full below.

Observable: heartbeats of elaborating a term and reducing it to weak head normal form, read by `the_ekg_reads`
(Episode 8). Baseline: the blank drawn in the same call.

Source: `cc347cb`. Status: set up; not yet read.

## The seal

```
Experiment 011, the throw. Sealed Tue Nov 17 21:36:34 EST 2026, before any output of these probes was read.
The probes were not put on the meter before sealing. Their six terms were checked to elaborate, in a separate file with
no meter in it. If a probe fails to compile, the repair is reported with the readings, and a repair that changes what
is measured voids the seal for that probe.

The author's statement, 17 November 2026: "i see, compton time is the time it takes to throw a bent card." Beside it
stand two earlier ones: one floor is one Compton time (Experiment 003, "compton time is rfl"), and the bent card in the
device is Quot.sound.

From 009b and 009c (setups d9e0ab3, b3ff7c3): on its second reading the click of the device's truth reads 2162 and the
click of any other fact 1141; the step, 1021, belongs to the device's truth alone. The registered floor is 3016.

The probes, each read twice in one process by the_ekg_reads of Episode 8, each reading beside its blank:
  sound            Quot.sound applied once, proving that one point of Episode 8's box is itself
  sound_control    the same statement by rfl, with nothing thrown
  propext          propext applied once, proving that the truth of the device's truth is itself
  propext_control  the same statement by rfl
  truth            the click of the device's truth, read as a term
  named            Episode 8's own throw, a_partitioning_of_quotients 1 1, read by its name
Five runs per probe, one fresh process per run. Source: cc347cb. Machine: Apple M2.
The throw is the second reading of sound less the second reading of sound_control.

S1. Heartbeat counts are identical across the five runs of every probe.
S2. (the throw of the bent card.) Three rules, which exclude one another:
      AUTHOR-FLOOR  as Claude takes it, and the author may correct it: the throw costs one floor: it is within one part
                    in ten of the blank read beside the sound's second reading.
      AUTHOR-STEP   the other way Claude can take it: the throw costs the step: it is 1021, to within 50.
      CLAUDE        neither: the throw is under 500 heartbeats, either sign. Applying an axiom to arguments already
                    elaborated is one more application for the elaborator, and nothing is reduced.
S3. CLAUDE: the throw of propext, net of its control, is also under 500, and within 300 of the throw of the sound: the
    meter does not tell the two axioms apart by cost.
S4. CLAUDE: read by its name, Episode 8's own throw costs less than the sound written out (as 009c found of cards read by
    name).

Would refute: S1, any two runs of a probe that differ. S2, each rule by another's outcome; a throw that is none of the
three refutes all and is reported as found. S3 and S4, the contrary.
```
