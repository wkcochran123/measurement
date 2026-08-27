# Measurement

```
measurement % cd device
device % time lake build > build_log
lake build > build_log  1509.67s user 7.95s system 101% cpu 25:00.69 total
device % cat build_log
✔ [3/17] Built Measurement.Episode01 (502ms)
✔ [4/17] Built Measurement.ComputerProgram (209ms)
✔ [5/17] Built Measurement.Calibration.LeanCalibration (486ms)
✔ [6/17] Built Measurement.Episode02 (1.4s)
✔ [7/17] Built Measurement.Episode03 (4.5s)
✔ [8/17] Built Measurement.Episode04 (1346s)
✔ [9/17] Built Measurement.Episode05 (46s)
✔ [10/17] Built Measurement.Episode06 (33s)
✔ [11/17] Built Measurement.Episode07 (40s)
✔ [12/17] Built Measurement.Episode08 (690ms)
ℹ [13/17] Built Measurement.Episode09 (14s)
info: Measurement/Episode09.lean:1147:0: "alpha = 137.011290548979457087737233"
info: Measurement/Episode09.lean:1148:0: 'Measurement.theDecimalLow' does not depend on any axioms
✔ [14/17] Built Measurement.Episode10 (10s)
ℹ [15/17] Built Measurement.Episode11 (932ms)
info: Measurement/Episode11.lean:925:0: "alpha = 137.011290548979457087737460"
info: Measurement/Episode11.lean:926:0: 'Measurement.the_ratio_is_bracketed' depends on axioms: [propext, Quot.sound]
✔ [16/17] Built Measurement (273ms)
Build completed successfully (17 jobs).
device %
```
