/-
Episode 13 -- THE FOURTH POINTING, AND THE PRICE OF THE ROUTE.

Three roads have now pointed at the number.  Episode 9 counts the cards and
spells the low end of the bracket, exactly, for nothing.  Episode 11 spells the
high end, exactly, for the reader's choice.  Episode 12 emits a solver that
reaches sixteen figures and dies past a step of 5e-12.

This is the fourth, and it changes only ONE thing: where the constants come
from.  Episode 12 took them from the counted cards.  Episode 13 takes them from
the ELABORATION -- the register's own tape, measured rather than counted, read
through `alpha_0` at depth one.

THE NUMBER DOES NOT MOVE.  The coefficients are the same three integers, the
solver is the same solver, the answer is the same sixteen figures.  What moves
is the CENSUS: the counted route is axiom-free and the measured route is not,
because reading the tape goes through the machinery that costs the reader a
choice.  Same destination, two prices, and the ledger is where the difference
shows.
-/

import Measurement.Episode12

namespace Measurement.Episode13

/-- THE COUNTS, TAKEN OFF THE ELABORATION.  Not `funge` and `tange` as Episode
9 counts them -- these are read from the depth-one register's own tape. -/
def measured : Nat × Nat := alpha_0 (tapeOfJar (register Fact.Truth 1))

def tangeMeasured : Nat := measured.1
def fungeMeasured : Nat := measured.2

/-- The cards, formed from the MEASURED counts by the same three rules. -/
def couplingMeasured : Nat := fungeMeasured * tangeMeasured * tangeMeasured
def targetMeasured : Nat := couplingMeasured / (fungeMeasured * fungeMeasured) + 1
def radiusMeasured : Nat := couplingMeasured

def aM : Nat := targetMeasured * targetMeasured * (couplingMeasured - targetMeasured)
def bM : Nat := 2 * couplingMeasured * targetMeasured * radiusMeasured * radiusMeasured
def cM : Nat := couplingMeasured * radiusMeasured * radiusMeasured * radiusMeasured * radiusMeasured

/-- THE MEASURED ROUTE ARRIVES AT THE COUNTED CONSTANTS.  The elaboration and
the count agree, and this decides it rather than assuming it. -/
theorem the_measured_route_agrees :
    aM = Measurement.Episode12.a
      ∧ bM = Measurement.Episode12.b
      ∧ cM = Measurement.Episode12.c := by
  decide

/-- The emitted solver, identical in every line except where it says its
constants came from. -/
def source : String :=
  "#!/usr/bin/env python3\n" ++
  "# Episode 13 -- EMITTED BY THE MACHINE, FROM THE ELABORATION.\n" ++
  "#\n" ++
  "# Episode 12's constants were COUNTED.  These were MEASURED: read off the\n" ++
  "# depth-one register's own tape through alpha_0, then put through the same\n" ++
  "# three rules.  The integers below are identical to Episode 12's, and the\n" ++
  "# Lean build decides that they are.  What differs is the census: the counted\n" ++
  "# route costs no axioms and the measured route costs the reader a choice.\n" ++
  "#\n" ++
  "# Same number, same solver, same sixteen figures, two different prices.\n" ++
  "\n" ++
  "A = " ++ Measurement.Episode12.numeral aM ++ "\n" ++
  "B = " ++ Measurement.Episode12.numeral bM ++ "\n" ++
  "K = " ++ Measurement.Episode12.numeral cM ++ "\n" ++
  "\n" ++
  "def residual(x):\n" ++
  "    return A * x * x - B * x + K\n" ++
  "\n" ++
  "def exact_digits(places):\n" ++
  "    scale = 10 ** places\n" ++
  "    lo, hi = 137 * scale, 138 * scale\n" ++
  "    while lo + 1 < hi:\n" ++
  "        mid = (lo + hi) // 2\n" ++
  "        if A * mid * mid - B * mid * scale + K * scale * scale < 0:\n" ++
  "            lo = mid\n" ++
  "        else:\n" ++
  "            hi = mid\n" ++
  "    return lo\n" ++
  "\n" ++
  "def main():\n" ++
  "    import warnings; warnings.filterwarnings('ignore')\n" ++
  "    import numpy as np\n" ++
  "    from scipy.optimize import newton_krylov\n" ++
  "    sol = newton_krylov(lambda v: np.array([residual(v[0])]),\n" ++
  "                        np.array([137.5]), f_tol=1e-14, verbose=False)\n" ++
  "    jfnk = float(sol[0])\n" ++
  "    places = 24\n" ++
  "    d = exact_digits(places)\n" ++
  "    exact = f\"{d // 10 ** places}.{str(d % 10 ** places).zfill(places)}\"\n" ++
  "    print()\n" ++
  "    print(\"  alpha = \" + f\"{jfnk:.24f}\" + \"   (JFNK on the MEASURED constants)\")\n" ++
  "    print(\"  alpha = \" + exact + \"   (integer bisection, exact)\")\n" ++
  "    print()\n" ++
  "    print(\"  the constants came off the elaboration, not the count.\")\n" ++
  "    print(\"  the number is the same.  the census is not.\")\n" ++
  "    print()\n" ++
  "\n" ++
  "if __name__ == '__main__':\n" ++
  "    main()\n"

end Measurement.Episode13

-- Emit the fourth pointing.  Returns Unit; prints nothing.
#eval IO.FS.writeFile "Measurement/Episode13.py" Measurement.Episode13.source

#print axioms Measurement.Episode13.the_measured_route_agrees
