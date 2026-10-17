# Measurement

```
measurement % cd device/Measurement
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
lake build > build_log  1413.08s user 11.30s system 99% cpu 23:47.97 total
✔ [2/16] Built Measurement.Episode01 (1.0s)
✔ [3/16] Built Measurement.ComputerProgram (193ms)
✔ [4/16] Built Measurement.Episode02 (1.4s)
✔ [5/16] Built Measurement.Calibration.LeanCalibration (1.8s)
✔ [6/16] Built Measurement.Episode03 (4.4s)
✔ [7/16] Built Measurement.Episode04 (1326s)
✔ [8/16] Built Measurement.Episode05 (19s)
✔ [9/16] Built Measurement.Episode07 (16s)
ℹ [10/16] Built Measurement.Episode08 (6.9s)
info: Measurement/Episode08.lean:765:0: "137.011290548979457087737300"
✔ [11/16] Built Measurement.Episode09 (20s)
✔ [12/16] Built Measurement.Episode10 (29s)
✔ [13/16] Built Measurement.Episode11 (2.6s)
ℹ [14/16] Built Measurement.Episode12 (3.7s)
info: Measurement/Episode12.lean:1190:0: 'Measurement.the_box_has_one_point' depends on axioms: [Quot.sound]
info: Measurement/Episode12.lean:1251:0: "137.011290548979457087737300"
info: Measurement/Episode12.lean:1252:0: 'Measurement.the_other_machine_reads' depends on axioms: [propext]
✔ [15/16] Built Measurement (640ms)
Build completed successfully (16 jobs).
device %
```
