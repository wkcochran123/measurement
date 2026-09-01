# Measurement

```
measurement % cd device
device % time lake build > build_log
lake build > build_log  1447.97s user 9.24s system 100% cpu 24:13.19 total
device % cat build_log
✔ [2/12] Built Measurement.Episode01 (1.9s)
✔ [3/12] Built Measurement.ComputerProgram (205ms)
✔ [4/12] Built Measurement.Episode02 (1.5s)
✔ [5/12] Built Measurement.Calibration.LeanCalibration (1.8s)
✔ [6/12] Built Measurement.Episode03 (5.2s)
✔ [7/12] Built Measurement.Episode04 (1352s)
✔ [8/12] Built Measurement.Episode05 (21s)
✔ [9/12] Built Measurement.Episode07 (49s)
ℹ [10/12] Built Measurement.Episode08 (20s)
info: Measurement/Episode08.lean:1469:0: "137.011290548979457087737300"
info: Measurement/Episode08.lean:1470:0: 'Measurement.theReadingScaled' depends on axioms: [propext]
✔ [11/12] Built Measurement (382ms)
Build completed successfully (12 jobs).
device % vim ../README.md
```
