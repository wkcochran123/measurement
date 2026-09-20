# Measurement

```
measurement % cd device
device % time lake build > build_log && cat build_log
lake build > build_log  1437.09s user 11.14s system 100% cpu 23:59.00 total
✔ [2/17] Built Measurement.Episode01 (1.9s)
✔ [3/17] Built Measurement.ComputerProgram (214ms)
✔ [4/17] Built Measurement.Episode02 (1.5s)
✔ [5/17] Built Measurement.Calibration.LeanCalibration (1.8s)
✔ [6/17] Built Measurement.Episode03 (4.4s)
✔ [7/17] Built Measurement.Episode04 (1319s)
✔ [8/17] Built Measurement.Episode05 (19s)
✔ [9/17] Built Measurement.Episode07 (21s)
ℹ [10/17] Built Measurement.Episode08 (19s)
info: Measurement/Episode08.lean:1560:0: "137.011290548979457087737300"
info: Measurement/Episode08.lean:1561:0: 'Measurement.theReadingScaled' depends on axioms: [propext]
✔ [11/17] Built Measurement.Episode09 (14s)
✔ [12/17] Built Measurement.Episode10 (33s)
✔ [13/17] Built Measurement.Episode11 (1.2s)
✔ [14/17] Built Measurement.Episode12 (1.2s)
✔ [15/17] Built Measurement.Episode13 (478ms)
✔ [16/17] Built Measurement (273ms)
Build completed successfully (17 jobs).
device %
```
