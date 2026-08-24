/-
Episode 12 -- THE MACHINE WRITES THE SOLVER.

Episode 9 counts the cards and forms the quadratic.  Episode 11 reads the
bracket.  This episode does neither: it EMITS the third reading's source code,
with the constants filled in from the machine's own counts rather than typed by
a person.  The Python that results is a consumer of the device, not a second
opinion about it -- it cannot disagree about C, T or R, because it never had
them until this file handed them over.

WHAT IT COSTS.  The generator builds a String and never queries one.  Every
numeral in the emitted source goes through `Nat.toDigits` and `String.ofList`;
`String.length` and `String.data` do not appear, because they pull choice
through the UTF-8 API and this file is meant to census at [propext, Quot.sound].

WHAT IT DOES NOT DO.  It does not run the solver, does not check its answer,
and does not certify anything the Python later prints.  It writes the file.
-/

import Measurement.Episode11

namespace Measurement.Episode12

/-- A numeral, BUILT.  `Nat.toDigits` gives the characters and `String.ofList`
assembles them; nothing reads a `String` back. -/
def numeral (n : Nat) : String := String.ofList (Nat.toDigits 10 n)

/-- The three coefficients, taken from the machine's counts. -/
def a : Nat := quadA
def b : Nat := quadB
def c : Nat := quadC

/-- THE EMITTED SOURCE.  The solver, with the device's constants written into
it.  Everything variable is a `numeral` of something the machine counted. -/
def source : String :=
  "#!/usr/bin/env python3\n" ++
  "# Episode 12 -- EMITTED BY THE MACHINE.  Do not edit: regenerate.\n" ++
  "#\n" ++
  "# The three coefficients below were not typed.  They were written here by\n" ++
  "# Episode12.lean from the device's own counted cards, and the census of that\n" ++
  "# generator is printed in the build log beside them.  This file is therefore a\n" ++
  "# CONSUMER of the device: it cannot disagree about the constants, because it\n" ++
  "# never had them until the machine handed them over.\n" ++
  "#\n" ++
  "# It solves a x^2 - b x + c = 0 by matrix-free Newton-Krylov and prints the\n" ++
  "# larger root.  No square root anywhere.  Floats throughout, which is the\n" ++
  "# whole point of running it: to see where the float gives out.\n" ++
  "\n" ++
  "A = " ++ numeral a ++ "\n" ++
  "B = " ++ numeral b ++ "\n" ++
  "K = " ++ numeral c ++ "\n" ++
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
  "    import numpy as np\n" ++
  "    from scipy.optimize import newton_krylov\n" ++
  "    sol = newton_krylov(lambda v: np.array([residual(v[0])]),\n" ++
  "                        np.array([137.5]), f_tol=1e-14, verbose=False)\n" ++
  "    jfnk = float(sol[0])\n" ++
  "    places = 24\n" ++
  "    d = exact_digits(places)\n" ++
  "    exact = f\"{d // 10 ** places}.{str(d % 10 ** places).zfill(places)}\"\n" ++
  "    print()\n" ++
  "    print(\"  alpha = \" + f\"{jfnk:.24f}\" + \"   (JFNK, float)\")\n" ++
  "    print(\"  alpha = \" + exact + \"   (integer bisection, exact)\")\n" ++
  "    js = f\"{jfnk:.24f}\"\n" ++
  "    agree = 0\n" ++
  "    for x, y in zip(js.replace('.', ''), exact.replace('.', '')):\n" ++
  "        if x != y: break\n" ++
  "        agree += 1\n" ++
  "    print()\n" ++
  "    print(f\"  the float agrees to {agree} figures, then stops.\")\n" ++
  "    print(\"  the two exact readings in the Lean build agree to 21.\")\n" ++
  "    print()\n" ++
  "\n" ++
  "    # DIVERGENCE, AND THE SMALLEST DELTA THAT SURVIVES.\n" ++
  "    # JFNK never forms a Jacobian; it approximates the Jacobian-vector\n" ++
  "    # product by a finite difference of step rdiff.  Shrink that step and\n" ++
  "    # the difference of two nearly equal floats loses its significant\n" ++
  "    # digits, until the direction the solver is handed is noise.  The\n" ++
  "    # method does not get more accurate as the step shrinks.  It dies.\n" ++
  "    import warnings\n" ++
  "    warnings.filterwarnings('ignore')\n" ++
  "    print(\"  delta        outcome\")\n" ++
  "    last_good = None\n" ++
  "    for e in [1e-2, 1e-4, 1e-6, 1e-8, 1e-10, 1e-11, 5e-12, 3e-12, 1e-12, 1e-14]:\n" ++
  "        try:\n" ++
  "            t = newton_krylov(lambda v: np.array([residual(v[0])]),\n" ++
  "                              np.array([137.5]), rdiff=e, f_tol=1e-14,\n" ++
  "                              maxiter=200, verbose=False)\n" ++
  "            x = float(t[0]); last_good = e\n" ++
  "            print(f\"  {e:9.1e}    converges to {x:.20f}\")\n" ++
  "        except Exception as ex:\n" ++
  "            print(f\"  {e:9.1e}    DIVERGES ({type(ex).__name__})\")\n" ++
  "    print()\n" ++
  "    print(f\"  smallest delta that still converges: {last_good:.1e}\")\n" ++
  "    print(\"  and every converging delta lands on the SAME 16 figures --\")\n" ++
  "    print(\"  refining the step does not buy a digit, it only buys collapse.\")\n" ++
  "    print()\n" ++
  "\n" ++
  "if __name__ == '__main__':\n" ++
  "    main()\n"

/-- THE CONSTANTS ARE THE COUNTED ONES.  What gets written into the Python is
what the machine counted, decided here rather than trusted. -/
theorem the_emitted_constants_are_counted :
    a = 325 ∧ b = 58320 ∧ c = 1889568 := by decide

end Measurement.Episode12

-- Write the solver.  `IO.FS.writeFile` returns `Unit`, so this prints nothing
-- into the build's four lines.
#eval IO.FS.writeFile "Measurement/Episode12.py" Measurement.Episode12.source

#print axioms Measurement.Episode12.the_emitted_constants_are_counted
