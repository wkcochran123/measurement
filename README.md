# Measurement

```
measurement % cd device/Measurement/
Measurement % grep EPISODE *.lean
Episode01.lean:__EPISODE 1__: _Counting_
Episode02.lean:__EPISODE 2__: _Time_
Episode03.lean:__EPISODE 3__: _Convergence_
Episode04.lean:__EPISODE 4__: _The Gamble_
Episode05.lean:__EPISODE 5__: _The Ante_
Episode06.lean:__EPISODE 6__: _The Trick_
Episode07.lean:__EPISODE 7__: _The Patter_
Episode08.lean:__EPISODE 8__: _The Macguffin_
Episode09.lean:__EPISODE 9__: _The Misdirection_
Episode10.lean:__EPISODE 10__: _The Accomplice_
Episode11.lean:__EPISODE 11__: _The Force_
Episode12.lean:__EPISODE 12__: _Let Him Cook. . . . . . . Levin_
Measurement % cd ..
device % time lake build > build_log && cat build_log
lake build > build_log  1426.14s user 11.61s system 99% cpu 24:06.75 total
✔ [2/16] Built Measurement.Episode01 (1.9s)
✔ [3/16] Built Measurement.ComputerProgram (236ms)
✔ [4/16] Built Measurement.Episode02 (1.5s)
✔ [5/16] Built Measurement.Calibration.LeanCalibration (1.9s)
✔ [6/16] Built Measurement.Episode03 (4.5s)
✔ [7/16] Built Measurement.Episode04 (1337s)
✔ [8/16] Built Measurement.Episode05 (19s)
✔ [9/16] Built Measurement.Episode07 (22s)
ℹ [10/16] Built Measurement.Episode08 (802ms)
info: Measurement/Episode08.lean:592:0: "137.011290548979457087737300"
info: Measurement/Episode08.lean:593:0: 'Measurement.theReadingScaled' depends on axioms: [propext, Quot.sound]
info: Measurement/Episode08.lean:594:0: 'Measurement.theReadingCertified' depends on axioms: [propext, Quot.sound]
✔ [11/16] Built Measurement.Episode09 (15s)
✔ [12/16] Built Measurement.Episode10 (39s)
✔ [13/16] Built Measurement.Episode11 (2.7s)
ℹ [14/16] Built Measurement.Episode12 (1.7s)
info: Measurement/Episode12.lean:1118:0: 'Measurement.cook_levin_on_the_mechanism' depends on axioms: [propext]
info: Measurement/Episode12.lean:1119:0: 'Measurement.cook_levin_on_the_meter' depends on axioms: [propext]
info: Measurement/Episode12.lean:1144:0: 'Measurement.the_division_was_quot_sound' depends on axioms: [propext, Quot.sound]
info: Measurement/Episode12.lean:1176:0: "TRUE = TRUE"
info: Measurement/Episode12.lean:1177:0: 'Measurement.the_box_has_one_point' depends on axioms: [Quot.sound]
✔ [15/16] Built Measurement (283ms)
Build completed successfully (16 jobs).
device % cd ..
measurement % vim README.md
```
