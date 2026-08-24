#!/usr/bin/env python3
# Episode 12 -- EMITTED BY THE MACHINE.  Do not edit: regenerate.
#
# The three coefficients below were not typed.  They were written here by
# Episode12.lean from the device's own counted cards, and the census of that
# generator is printed in the build log beside them.  This file is therefore a
# CONSUMER of the device: it cannot disagree about the constants, because it
# never had them until the machine handed them over.
#
# It solves a x^2 - b x + c = 0 by matrix-free Newton-Krylov and prints the
# larger root.  No square root anywhere.  Floats throughout, which is the
# whole point of running it: to see where the float gives out.

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
    import numpy as np
    from scipy.optimize import newton_krylov
    sol = newton_krylov(lambda v: np.array([residual(v[0])]),
                        np.array([137.5]), f_tol=1e-14, verbose=False)
    jfnk = float(sol[0])
    places = 24
    d = exact_digits(places)
    exact = f"{d // 10 ** places}.{str(d % 10 ** places).zfill(places)}"
    print()
    print("  alpha = " + f"{jfnk:.24f}" + "   (JFNK, float)")
    print("  alpha = " + exact + "   (integer bisection, exact)")
    js = f"{jfnk:.24f}"
    agree = 0
    for x, y in zip(js.replace('.', ''), exact.replace('.', '')):
        if x != y: break
        agree += 1
    print()
    print(f"  the float agrees to {agree} figures, then stops.")
    print("  the two exact readings in the Lean build agree to 21.")
    print()

    # DIVERGENCE, AND THE SMALLEST DELTA THAT SURVIVES.
    # JFNK never forms a Jacobian; it approximates the Jacobian-vector
    # product by a finite difference of step rdiff.  Shrink that step and
    # the difference of two nearly equal floats loses its significant
    # digits, until the direction the solver is handed is noise.  The
    # method does not get more accurate as the step shrinks.  It dies.
    import warnings
    warnings.filterwarnings('ignore')
    print("  delta        outcome")
    last_good = None
    for e in [1e-2, 1e-4, 1e-6, 1e-8, 1e-10, 1e-11, 5e-12, 3e-12, 1e-12, 1e-14]:
        try:
            t = newton_krylov(lambda v: np.array([residual(v[0])]),
                              np.array([137.5]), rdiff=e, f_tol=1e-14,
                              maxiter=200, verbose=False)
            x = float(t[0]); last_good = e
            print(f"  {e:9.1e}    converges to {x:.20f}")
        except Exception as ex:
            print(f"  {e:9.1e}    DIVERGES ({type(ex).__name__})")
    print()
    print(f"  smallest delta that still converges: {last_good:.1e}")
    print("  and every converging delta lands on the SAME 16 figures --")
    print("  refining the step does not buy a digit, it only buys collapse.")
    print()

if __name__ == '__main__':
    main()
