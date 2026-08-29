# Measurement

```
measurement % cd device
device % time lake build > build_log
lake build > build_log  1370.81s user 5.02s system 100% cpu 22:48.82 total
device % cat build_log
✔ [2/12] Built Measurement.Episode01 (1.7s)
✔ [3/12] Built Measurement.ComputerProgram (205ms)
✔ [4/12] Built Measurement.Episode02 (1.4s)
✔ [5/12] Built Measurement.Calibration.LeanCalibration (1.6s)
✔ [6/12] Built Measurement.Episode03 (4.4s)
✔ [7/12] Built Measurement.Episode04 (1310s)
✔ [8/12] Built Measurement.Episode05 (19s)
✔ [9/12] Built Measurement.Episode08 (14s)
ℹ [10/12] Built Measurement.Episode11 (16s)
info: Measurement/Episode11.lean:1288:0: "alpha = 137.011290548979457087737233"
info: Measurement/Episode11.lean:1289:0: 'Measurement.theDecimalLow' does not depend on any axioms
✔ [11/12] Built Measurement (268ms)
Build completed successfully (12 jobs).
device %
```
