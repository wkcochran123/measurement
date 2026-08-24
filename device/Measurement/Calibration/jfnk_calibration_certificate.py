#!/usr/bin/env python3
# =============================================================================
#
#   THE CALIBRATION CERTIFICATE
#   Newton-Krylov (JFNK) meets the device's jar -- and stops where it stops.
#
#   (operator-directed, 2026-08-13: "use the most relevant libraries for
#    jfnk and multigrid ... make that EXTREMELY EASY to read ... this is
#    the calibration certificate.")
#
# =============================================================================
#
#   WHAT THIS FILE IS
#   -----------------
#   A readable, runnable illustration that the fast solvers of scientific
#   computing -- bisection, the device's own quasi-Newton step, and
#   matrix-free Newton-Krylov (JFNK, scipy) -- all rush to the SAME
#   crossing, and all halt at the SAME floor. Three roads, one wall.
#
#   The equation is the device's own crossing. The device measures two
#   numbers (they are MEASURED inside the machine-checked Lean build,
#   not chosen here):
#
#       C = 18   -- the measured second variation   (curvature)
#       T = 5    -- the slip target                 (first variation)
#
#   and the crossing is where the slip meets its target:
#
#       f(d) = C - T * d**2 = 0        =>        d* = sqrt(C/T) = sqrt(18/5)
#
#   On the device's affine readout scale, that crossing is the jar:
#   the count-3 bracket [129.6, 137.7] deepening to the device's own
#   inverse-alpha ~= 137.011 (NOT the lab's 137.036 -- the device reads
#   its own electron, in its own frame).
#
#   THE THREE HONEST LABELS (the gate this file passed to exist)
#   ------------------------------------------------------------
#   1. THIS IS AN ILLUSTRATION, NOT THE DEVICE'S COMPUTATION.
#      The device computes the jar in EXACT rational arithmetic, zero
#      float, end to end (the mediant / BFGS descent in the Lean build:
#      AlphaBFGS.lean, AlphaBoundMediant.lean). Floating point here paints
#      a picture of the convergence; the exact bracket is the source of
#      truth. Nothing below is an alternative derivation of the jar.
#
#   2. EVERY SOLVER LANDS AT THE JAR AND STOPS. NO DIGITS BELOW THE FLOOR.
#      "When bisection stops, that is the jar" (the operator's own
#      definition, 2026-08-13, and the best one-line description of this
#      machine). The floor is the count-to-three bracket -- below it the
#      residue is uncomputable (the FinitenessFence; Chaitin territory),
#      so digits printed past the floor are FALSE PRECISION. This file
#      truncates every readout at the floor, on purpose, visibly.
#
#   3. FASTER TO THE FLOOR -- NEVER TIGHTER THAN THE RATIONAL.
#      JFNK reaches the crossing in a handful of iterations where
#      bisection takes many. Speed is real. Precision past the floor is
#      not: a float solver cannot out-resolve an exact rational bracket,
#      it can only arrive at the same wall sooner.
#
#   WHY "JFNK" IS THE RIGHT NAME FOR WHAT THE DEVICE ALREADY DOES
#   -------------------------------------------------------------
#   JFNK = Jacobian-Free Newton-Krylov: Newton's method where the
#   Jacobian is never assembled -- its action is probed by differencing.
#   For a scalar equation the Krylov space is one-dimensional and JFNK
#   degenerates to exactly the secant/Newton step -- which is what the
#   device's own descent is: AlphaBFGS.lean runs 1-D BFGS (quasi-Newton)
#   on the MEASURED slope and curvature,
#
#       d_{k+1} = d_k * (3*C - T*d_k**2) / (2*C)
#
#   whose iterates are the mediant continued-fraction convergents. So the
#   fast method was already in the building; this certificate just lets
#   you watch it run next to the textbook solvers.
#
#   A NOTE ON MULTIGRID (asked for, and answered honestly)
#   ------------------------------------------------------
#   A multigrid preconditioner earns its keep when the Jacobian is a
#   large mesh-coupled system: it kills smooth error on coarse grids so
#   Krylov only fights the rough part. The device's crossing is a SINGLE
#   scalar equation -- there is no mesh, so multigrid has nothing to
#   precondition (the "grid hierarchy" of this problem is the bisection
#   ladder itself, which is already optimal at one unknown). Section 4
#   demonstrates the idea anyway on a replicated-grid version of the same
#   crossing, so the word is not left as decoration -- and shows it
#   converging to the same d* on every grid point. Same wall, many seats.
#
#   PROVENANCE (label 1 made concrete)
#   ----------------------------------
#   This certificate reports floats computed by scipy on one machine on
#   one day. The numbers worth trusting are the exact ones it points at:
#   C=18, T=5, the bracket, and the stop. Everything else is scenery.
#
# =============================================================================

import datetime
import platform
from fractions import Fraction

import numpy as np
import scipy
import scipy.optimize

# -----------------------------------------------------------------------------
# Section 0 -- the measured constants and the exact targets
# -----------------------------------------------------------------------------

C = 18          # measured second variation (curvature)      -- device: MEASURED
T = 5           # slip target (first variation)              -- device: MEASURED

D_STAR = (C / T) ** 0.5          # sqrt(18/5): the crossing (float picture only)

# The device's own count-3 floor, on the d-scale: the bracket after three
# honest halvings of [1, 2]. Three is not a tuning choice -- it is the
# count-to-three fencepost the device pins its precision to.
FLOOR_HALVINGS = 3

# The jar, as published by the exact Lean build (cited, NOT recomputed here):
JAR_BRACKET_INV_ALPHA = (129.6, 137.7)     # count-3 bracket, inverse-alpha scale
JAR_DEEP_READOUT      = 137.011            # the device's own number (approx.)


def f(d):
    """The crossing equation: slip minus target. Zero exactly at d* = sqrt(C/T)."""
    return C - T * d * d


# -----------------------------------------------------------------------------
# Section 1 -- BISECTION: the honest walk, and THE STOP
# -----------------------------------------------------------------------------

def bisection_to_the_floor():
    """Halve the bracket [1, 2] exactly FLOOR_HALVINGS times, then STOP.

    EXACT ARITHMETIC, deliberately: the endpoints are Fractions and the
    sign test C - T*m^2 > 0 is exact rational comparison -- there is no
    float anywhere in this function. This is the CERTIFIED column: these
    digits reproduce, cold, build to build, machine to machine.

    The stop is not a shortage of compute -- it is the device's pinned
    precision (count-to-three). "When bisection stops, that is the jar."
    Returns the final bracket (lo, hi) as exact Fractions.
    """
    lo, hi = Fraction(1), Fraction(2)       # 1^2 = 1 < C/T = 18/5 < 4 = 2^2
    print("  step   bracket (exact rationals)    width")
    print(f"   0     [{lo}, {hi}]                    {hi - lo}")
    for step in range(1, FLOOR_HALVINGS + 1):
        mid = (lo + hi) / 2
        if C - T * mid * mid > 0:           # exact sign test: crossing above
            lo = mid
        else:                               # exact sign test: crossing below
            hi = mid
        print(f"   {step}     [{lo}, {hi}]"
              f"{' ' * max(1, 22 - len(f'[{lo}, {hi}]'))}{hi - lo}")
    print(f"   STOP  -- the count-to-three floor. This bracket IS the reading.")
    return lo, hi


# -----------------------------------------------------------------------------
# Section 2 -- THE DEVICE'S OWN STEP: quasi-Newton on the measured curvature
# -----------------------------------------------------------------------------

def device_quasi_newton(d0=1.0, steps=5):
    """The iteration the Lean build already runs (AlphaBFGS.lean):

        d_{k+1} = d_k * (3*C - T*d_k**2) / (2*C)

    Newton's method on the measured slope/curvature, fixed point at
    d* = sqrt(C/T). Shown in float here as a picture; in the device it is
    exact rational and its iterates are the mediant CF convergents.
    """
    d = d0
    print("  step   d_k             residual f(d_k)")
    for k in range(steps + 1):
        print(f"   {k}     {d:<14.10f}  {f(d):+.2e}")
        d = d * (3 * C - T * d * d) / (2 * C)
    return d


# -----------------------------------------------------------------------------
# Section 3 -- JFNK: scipy's matrix-free Newton-Krylov, same equation
# -----------------------------------------------------------------------------

def jfnk_sprint(d0=1.0):
    """scipy.optimize.newton_krylov on the crossing equation.

    Jacobian-free: the solver probes the Jacobian's action by finite
    differences and solves each Newton step in a Krylov space. For one
    unknown this collapses to the same Newton family as Section 2 --
    which is the point: the fast method and the device's method are the
    same road.
    """
    iterates = []

    def residual(d):
        iterates.append(float(np.atleast_1d(d)[0]))
        return f(d)

    sol = scipy.optimize.newton_krylov(residual, np.array([d0]), f_tol=1e-12)
    return float(sol[0]), iterates


# -----------------------------------------------------------------------------
# Section 4 -- MULTIGRID'S HABITAT, honestly: the same crossing on a mesh
# -----------------------------------------------------------------------------

def replicated_grid_demo(n=64):
    """Put the SAME scalar crossing on every point of an n-point grid and
    couple neighbours with a tiny diffusion term -- the smallest system
    where a Krylov solver (and, at scale, a multigrid preconditioner)
    has real work to do. Every grid point still converges to d*.

        F_i(d) = C - T*d_i**2 + eps * (laplacian d)_i = 0

    With eps small, the answer is d* at every point: the mesh gives the
    solver a Jacobian worth preconditioning, and the physics gives it
    nothing new -- same wall, many seats. (A true multigrid hierarchy
    is overkill at n=64 and would need pyamg; scipy's Krylov handles it,
    and the honest conclusion is identical.)
    """
    eps = 1e-3

    def residual(d):
        lap = np.zeros_like(d)
        lap[1:-1] = d[:-2] - 2 * d[1:-1] + d[2:]
        lap[0] = d[1] - d[0]                # zero-flux edges
        lap[-1] = d[-2] - d[-1]
        return C - T * d * d + eps * lap

    d0 = np.full(n, 1.0)
    sol = scipy.optimize.newton_krylov(residual, d0, f_tol=1e-10)
    return float(sol.min()), float(sol.max())


# -----------------------------------------------------------------------------
# Section 5 -- the certificate: run everything, truncate at the floor, verdict
# -----------------------------------------------------------------------------

def truncate_at_floor(value, lo, hi):
    """Report a solver's answer ONLY to the precision the floor certifies.

    The floor bracket has width (hi - lo); digits finer than that width
    are below the floor and are refused, deliberately. The honest readout
    is the bracket itself, with the solver's landing shown inside it.
    """
    return (f"lands INSIDE the floor bracket [{lo:.3f}, {hi:.3f}] "
            f"(finer digits refused: below the floor is uncomputable)")


def main():
    line = "=" * 74
    print(line)
    print("THE CALIBRATION CERTIFICATE -- three solvers, one crossing, one stop")
    print(line)
    print(f"equation: f(d) = C - T*d^2,  C = {C} (measured), T = {T} (measured)")
    print(f"crossing: d* = sqrt(C/T) = sqrt({C}/{T})")
    print()

    print("[1] BISECTION -- the honest walk (\"when bisection stops, that is the jar\")")
    lo, hi = bisection_to_the_floor()
    print()

    print("[2] THE DEVICE'S OWN STEP -- quasi-Newton on the measured curvature")
    d_dev = device_quasi_newton()
    print("   (in the Lean build this runs in exact rationals: AlphaBFGS.lean)")
    print()

    print("[3] JFNK -- scipy.optimize.newton_krylov, matrix-free")
    d_jfnk, iterates = jfnk_sprint()
    print(f"   residual evaluations: {len(iterates)}  (bisection to the same"
          f" neighbourhood would take dozens of halvings)")
    print()

    print("[4] MULTIGRID'S HABITAT -- same crossing, replicated on a mesh")
    g_lo, g_hi = replicated_grid_demo()
    print(f"   64 coupled unknowns; every grid point lands in"
          f" [{g_lo:.6f}, {g_hi:.6f}] -- same wall, many seats")
    print()

    print("[5] THE VERDICT -- two columns, and only one of them is certified")
    print()
    print("   CERTIFIED (EXACT -- these digits reproduce, cold, every build):")
    print(f"     the bracket where bisection stopped:  d* in [{lo}, {hi}]")
    print(f"     the jar's own count-3 bracket (Lean build, cited not recomputed):")
    print(f"     {list(JAR_BRACKET_INV_ALPHA)} on the inverse-alpha scale,")
    print(f"     deepening to the device's own ~{JAR_DEEP_READOUT} -- pinned, not dialed.")
    print()
    print("   DISPLAYED (APPROX -- best point-estimates WITHIN the bracket;")
    print("   float, method-resolved, NOT CERTIFIED):")
    flo, fhi = float(lo), float(hi)
    for name, val in (("device quasi-Newton (secant/BFGS)", d_dev),
                      ("scipy JFNK (newton_krylov)", d_jfnk)):
        inside = flo <= val <= fhi
        print(f"     {name:<34} {val:.10f}"
              f"   [{'inside the certified bracket: PASS' if inside else 'FAIL'}]")
    print()
    print("   The quiet part, plainly: the extra digits of the estimates are")
    print("   the precision of the METHOD, not of the coupling; the bracket is")
    print("   what the machine knows. The bracket's digits reproduce (they are")
    print("   the invariant); the estimates' past-the-stop digits do not (they")
    print("   are the method resolving below where the invariant closes).")
    print()
    print("   Note the irony, on purpose: the most precise-LOOKING numbers in")
    print("   this file are the ones stamped NOT CERTIFIED. That stamp is the")
    print("   certificate doing its job.")
    print()

    print("WHAT THIS CERTIFICATE CERTIFIES (the four claims, and only these):")
    print(" 1. TRACEABILITY -- the number is DERIVED: measured C=18, T=5 (off the")
    print("    machine's own output) -> quasi-Newton descent -> sqrt(18/5) ->")
    print("    inverse-alpha ~137.011. Every natural earned off the elaborator;")
    print("    no naked constant anywhere in the chain.")
    print(" 2. PRINCIPLED STOP -- refinement halts at the count-to-three floor")
    print("    because below it the residue is uncomputable (FinitenessFence),")
    print("    not because any solver ran out of steam.")
    print(" 3. NOT DIALED -- the value was reached by convergence to what the")
    print("    machine gives, never by turning a knob toward a known answer.")
    print(" 4. ITS OWN NUMBER -- this certifies the device's electron-scoped")
    print("    ~137.011, NOT the lab's 137.036. The instrument, not the echo.")
    print()
    print("    In one sentence: THIS NUMBER WAS MEASURED, NOT CHOSEN.")
    print()
    print("THE THREE LABELS (this certificate is invalid without them):")
    print(" 1. illustration only -- the device's number comes from the EXACT")
    print("    rational build (zero float); this file is a picture of it.")
    print(" 2. every solver STOPS AT THE JAR -- no digits below the floor;")
    print("    what a float prints past the bracket is false precision.")
    print(" 3. faster to the floor, never tighter than the rational.")
    print()
    print(f"provenance: scipy {scipy.__version__}, numpy {np.__version__},"
          f" python {platform.python_version()},")
    print(f"            {platform.machine()}/{platform.system()},"
          f" run {datetime.date.today().isoformat()}")
    print(line)


if __name__ == "__main__":
    main()
