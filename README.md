# Measurement

```
measurement % cd device
device % lake build > build_log
device % cat build_log
✔ [2/17] Built Measurement.Episode01 (1.0s)
✔ [3/17] Built Measurement.ComputerProgram (219ms)
✔ [4/17] Built Measurement.Episode02 (1.5s)
✔ [5/17] Built Measurement.Calibration.LeanCalibration (1.9s)
✔ [6/17] Built Measurement.Episode03 (4.5s)
✔ [7/17] Built Measurement.Episode04 (2595s)
✔ [8/17] Built Measurement.Episode05 (22s)
✔ [9/17] Built Measurement.Episode07 (154s)
ℹ [10/17] Built Measurement.Episode08 (27s)
info: Measurement/Episode08.lean:1560:0: "137.011290548979457087737300"
info: Measurement/Episode08.lean:1561:0: 'Measurement.theReadingScaled' depends on axioms: [propext]
✔ [11/17] Built Measurement.Episode09 (142s)
✔ [12/17] Built Measurement.Episode10 (41s)
✔ [13/17] Built Measurement.Episode11 (3.5s)
✔ [14/17] Built Measurement.Episode12 (1.2s)
✔ [15/17] Built Measurement.Episode13 (506ms)
✔ [16/17] Built Measurement (273ms)
Build completed successfully (17 jobs).
device %
```
