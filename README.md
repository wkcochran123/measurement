# Measurement
## The Puzzle
1.*The easy question*: What is the name of the value printed in Episode 12? 
1.*The hard question*: How would you describe the process for naming it?
1.*The key question*: Did I plant the number or is it *key part* of the argument?
1.*Left as an exercise for the reader*: Describe the rest of the *key* for which the number is a *key part*. 

Use the *key* to open the box.
## The Puzzle Box
```
measurement % cd CARD_2/Measurement
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
CARD_2 % time lake build > build_log && cat build_log
lake build > build_log  1425.55s user 10.93s system 99% cpu 24:01.76 total
✔ [2/16] Built Measurement.Episode01 (1.9s)
✔ [3/16] Built Measurement.ComputerProgram (204ms)
✔ [4/16] Built Measurement.Episode02 (1.5s)
✔ [5/16] Built Measurement.Calibration.LeanCalibration (1.8s)
✔ [6/16] Built Measurement.Episode03 (4.5s)
✔ [7/16] Built Measurement.Episode04 (1342s)
✔ [8/16] Built Measurement.Episode05 (20s)
✔ [9/16] Built Measurement.Episode07 (15s)
ℹ [10/16] Built Measurement.Episode08 (3.4s)
info: Measurement/Episode08.lean:1290:0: "137.011290548979457087737300"
info: Measurement/Episode08.lean:1291:0: 'readers_experience.the_constant_can_be_inferred' depends on axioms: [propext, Quot.sound]
info: Measurement/Episode08.lean:1292:0: 'readers_experience.the_constant_factor_of_scaling_bullshit' depends on axioms: [propext, Quot.sound]
✔ [11/16] Built Measurement.Episode09 (16s)
✔ [12/16] Built Measurement.Episode10 (32s)
✔ [13/16] Built Measurement.Episode11 (2.2s)
ℹ [14/16] Built Measurement.Episode12 (3.8s)
info: Measurement/Episode12.lean:1072:0: 'Measurement.the_box_has_one_point' depends on axioms: [Quot.sound]
info: Measurement/Episode12.lean:1133:0: "137.011290548979457087737300"
info: Measurement/Episode12.lean:1134:0: 'Measurement.the_other_machine_reads' depends on axioms: [propext, Quot.sound]
✔ [15/16] Built Measurement (1.2s)
Build completed successfully (16 jobs).
CARD_2 %
```
