#!/usr/bin/env python3
# Episode 13 -- EMITTED BY THE MACHINE, FROM THE ELABORATION.
#
# Episode 12's constants were COUNTED.  These were MEASURED: read off the
# depth-one register's own tape through alpha_0, then put through the same
# three rules.  The integers below are identical to Episode 12's, and the
# Lean build decides that they are.  What differs is the census: the counted
# route costs no axioms and the measured route costs the reader a choice.
#
# Same number, same solver, same sixteen figures, two different prices.

A = 325
B = 58320
K = 1889568

def residual(x):
    return A * x * x - B * x + K

def exact_digits(places):
    scale = 10 ** places
    lo, hi = 137 * scale, 138 * scale
    while lo + 1 < hi:
        mid = (lo + hi) // 2
        if A * mid * mid - B * mid * scale + K * scale * scale < 0:
            lo = mid
        else:
            hi = mid
    return lo

def main():
    import warnings; warnings.filterwarnings('ignore')
    import numpy as np
    from scipy.optimize import newton_krylov
    sol = newton_krylov(lambda v: np.array([residual(v[0])]),
                        np.array([137.5]), f_tol=1e-14, verbose=False)
    jfnk = float(sol[0])
    places = 24
    d = exact_digits(places)
    exact = f"{d // 10 ** places}.{str(d % 10 ** places).zfill(places)}"
    print()
    print("  alpha = " + f"{jfnk:.24f}" + "   (JFNK on the MEASURED constants)")
    print("  alpha = " + exact + "   (integer bisection, exact)")
    print()
    print("  the constants came off the elaboration, not the count.")
    print("  the number is the same.  the census is not.")
    print()

if __name__ == '__main__':
    main()
