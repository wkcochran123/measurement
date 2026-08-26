# Measurement

```
measurement % cd device
device % time lake build > build.log
lake build > build.log  1486.38s user 7.13s system 101% cpu 24:34.96 total
device % cat build.log
✔ [2/17] Built Measurement.Episode01 (484ms)
✔ [3/17] Built Measurement.ComputerProgram (214ms)
✔ [4/17] Built Measurement.Calibration.EKGBounded (1.7s)
✔ [5/17] Built Measurement.Calibration.LeanCalibration (1.1s)
✔ [6/17] Built Measurement.Episode02 (1.5s)
✔ [7/17] Built Measurement.Episode03 (4.3s)
✔ [8/17] Built Measurement.Episode04 (1323s)
✔ [9/17] Built Measurement.Episode05 (45s)
✔ [10/17] Built Measurement.Episode06 (31s)
✔ [11/17] Built Measurement.Episode07 (39s)
✔ [12/17] Built Measurement.Episode08 (716ms)
ℹ [13/17] Built Measurement.Episode09 (15s)
info: Measurement/Episode09.lean:1147:0: "alpha = 137.011290548979457087737233"
info: Measurement/Episode09.lean:1148:0: 'Measurement.theDecimalLow' does not depend on any axioms
✔ [14/17] Built Measurement.Episode10 (11s)
ℹ [15/17] Built Measurement.Episode11 (930ms)
info: Measurement/Episode11.lean:925:0: "alpha = 137.011290548979457087737460"
info: Measurement/Episode11.lean:926:0: 'Measurement.the_ratio_is_bracketed' depends on axioms: [propext, Quot.sound]
✔ [16/17] Built Measurement (268ms)
Build completed successfully (17 jobs).
device %
```
