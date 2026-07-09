import Measurement.Formalization.TerminalUniqueness
import Measurement.Formalization.FiniteGaugeEquation
import Measurement.Formalization.Bridge
import Measurement.Formalization.QED
import Measurement.Formalization.Example

set_option autoImplicit false

/-!
# Measurement Formalization Stack

Isolated import surface for the five-layer formalization:

- `Measurement.Formalization.TerminalUniqueness` --- the serial-grammar
  backbone (`hterm_eq`, `terminal_observable_unique`,
  `terminal_observable_eq_inferredTerm`, `terminal_hterm_unique`,
  `terminal_observable_image_unique`,
  `terminal_observable_image_subsingleton`,
  `terminal_observable_image_nonempty`).
- `Measurement.Formalization.FiniteGaugeEquation` --- the default Frechet
  closure (`finiteGaugeEquation`, normal-form theorem, deterministic
  theorem, conditional bridge to `transmute`).
- `Measurement.Formalization.Bridge` --- the finite-gauge encoding
  contract (`FiniteGaugeEncoding`, `fge_observable_unique_under_encoding`,
  `fge_observable_image_subsingleton`, `fge_observable_eq_inferredTerm`,
  `fge_observable_image_eq_inferredTerm`,
  `fge_observable_unique_and_eq_inferredTerm_under_encoding`,
  `fge_observable_image_closed_under_encoding`,
  `fge_observable_image_nonempty_under_encoding`,
  `fge_observable_image_unique_under_encoding`).
- `Measurement.Formalization.QED` --- the abstract physical-experiment
  apex and the bridge-as-experiment view
  (`gauge_unique_on_device_image`, `device_gauge_image_subsingleton`,
  `gauge_eq_inferredTerm_on_device_image`,
  `device_gauge_image_eq_inferredTerm`,
  `gauge_unique_and_eq_inferredTerm_on_device_image`,
  `device_gauge_image_closed`,
  `device_gauge_image_nonempty`,
  `device_gauge_image_unique`,
  `finiteGaugePhysicalExperiment`, `finiteGaugeDeviceEncoding`,
  `fge_observable_unique_via_qed`,
  `fge_observable_image_subsingleton_via_qed`,
  `fge_observable_eq_inferredTerm_via_qed`,
  `fge_observable_image_eq_inferredTerm_via_qed`,
  `fge_observable_unique_and_eq_inferredTerm_via_qed`,
  `fge_observable_image_closed_via_qed`,
  `fge_observable_image_nonempty_via_qed`,
  `fge_observable_image_unique_via_qed`).
- `Measurement.Formalization.Example` --- structural sanity checks:
  direct terminal endpoint checks, plus Bridge and QED structural tracks
  exercising pairwise uniqueness, image subsingleton, canonical normal
  form, image normal form, combined pairwise/normal-form, image
  closure, image-nonempty existence, and nonempty image uniqueness
  theorem surfaces (with direct Bridge and via-QED routes covered at
  the shared Bridge/QED surfaces).

## Build-graph isolation

This file is **not** imported by `device/Measurement.lean` while Episode15
is active. Adding this aggregator provides a single import target the
later build gate can compile without touching the root import or the
Episode files. Until the operator opens that gate, both this aggregator
and the five files it imports remain orphan modules outside the active
build graph.

## What this module does NOT add

- no new theorems, structures, or definitions;
- no `noncomputable` declarations;
- no `sorry`;
- no axioms;
- no claim about non-encodable physical candidates or absolute physical
  uniqueness.

The aggregator is import-only.
-/
