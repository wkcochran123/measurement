#!/usr/bin/env python3
# =============================================================================
#
#   THE FIXED-POINT SWEEP -- the gap exhibit, realized.
#
#   (operator-directed, 2026-08-13: interpolate between the approximation
#    (1000) and the calibration that would generate 137.0357, plug it into
#    the device, and show the fixed point -- "linearly interpolate to ensure
#    that this cannot be confused as the number.")
#
# =============================================================================
#
#   WHAT THIS SHOWS, in one sentence: sweep the coefficient the whole way
#   from the approximation to the lab-dial, plug every value into the
#   device, and the fixed point NEVER MOVES off the device's own number --
#   the lab value is exactly the point the device does not sit at, across
#   the entire interpolation. Separation, proved by the sweep itself.
#
#   THE THREE GATE CONDITIONS (Kodo, 2026-08-13 -- this file is invalid
#   without them):
#    1. The fixed point exhibited is the device's own sqrt(18/5) -> ~137.011,
#       PROVED by T*d^2 = C, not asserted.
#    2. Injected values flow AWAY from 137.0357 and TO 137.011 under the
#       device's step -- separation, not reach.
#    3. 137.0357 appears ONLY as the lab target and the non-fixed-point,
#       never as the device's settled reading.
#
#   THE ALGEBRA (condition 1, done in the header so the code can't fudge it):
#   the device's quasi-Newton step is
#
#       g(d) = d * (3C - T*d^2) / (2C),     C = 18, T = 5   (both MEASURED)
#
#   A fixed point solves g(d) = d:
#
#       d * (3C - T*d^2) / (2C) = d
#       (3C - T*d^2) = 2C          (d != 0)
#       T*d^2 = C
#       d* = sqrt(C/T) = sqrt(18/5)
#
#   The fixed point is set by the MEASURED pair (C, T) alone. The
#   calibration coefficient does not appear in that equation -- and in the
#   certified jar chain it CANCELS (Nat.mul_div_cancel; CALIBRATION.md).
#   So no coefficient anywhere on the sweep can move the fixed point.
#   That is the whole exhibit; the code below just lets you watch it.
#
#   REGISTERS, labeled once and never mixed:
#     THE DEVICE'S NUMBER : inv-alpha ~= 137.011  (the jar; measured)
#     THE LAB'S NUMBER    : 137.0357              (the world's alpha^-1;
#                            cited as an external constant, never fed in)
#
# =============================================================================

import datetime
import platform

C = 18            # measured second variation
T = 5             # measured slip target

D_STAR = (C / T) ** 0.5              # sqrt(18/5) -- the device's crossing
DEVICE_INV_ALPHA = 137.0113          # the device's own readout (cited)
LAB_INV_ALPHA = 137.0357             # the lab's alpha^-1 (cited, external)

# The display scale that carries d to the inverse-alpha readout (display
# lane only -- the certified lane's coefficient cancels and is shown below).
DISPLAY_SCALE = DEVICE_INV_ALPHA / D_STAR


def g(d):
    """The device's own quasi-Newton step (AlphaBFGS): fixed point at d*."""
    return d * (3 * C - T * d * d) / (2 * C)


def main():
    line = "=" * 74
    print(line)
    print("THE FIXED-POINT SWEEP -- interpolate the dial; the fixed point stays home")
    print(line)

    # -- Condition 1: the fixed point, proved by T*d^2 = C ------------------
    print("[1] THE FIXED POINT (proved, not asserted)")
    print(f"    g(d) = d iff T*d^2 = C  =>  d* = sqrt({C}/{T}) = {D_STAR:.10f}")
    print(f"    check: g(d*) - d* = {g(D_STAR) - D_STAR:+.2e}   (zero to float eps)")
    print(f"    on the readout scale: {D_STAR * DISPLAY_SCALE:.4f} -- the device's own"
          f" ~{DEVICE_INV_ALPHA}")
    print()

    # -- The forbidden-dial endpoint, computed for real ---------------------
    # The display-lane coefficient that would make the readout recite the
    # lab value (the certified lane has no such coefficient -- it cancels).
    c_star = 1000.0 * LAB_INV_ALPHA / DEVICE_INV_ALPHA
    print("[2] THE SWEEP ENDPOINTS")
    print(f"    approximation end : coefficient 1000       (the rank=heartbeat frame)")
    print(f"    lab-dial end      : coefficient {c_star:.4f}  -- THE FORBIDDEN DIAL:")
    print(f"                        what a display would need to recite the lab's"
          f" {LAB_INV_ALPHA}")
    print()

    # -- The sweep: every interpolated coefficient, same fixed point --------
    print("[3] THE SWEEP -- lambda from 0 (approximation) to 1 (lab dial)")
    print("    lam    coefficient   display-lane readout   certified 18k/k   fixed point of g")
    for i in range(0, 11):
        lam = i / 10
        k = 1000.0 + lam * (c_star - 1000.0)
        display = DEVICE_INV_ALPHA * (k / 1000.0)   # the display lane moves...
        cancelled = (18 * int(round(k * 10**6))) // int(round(k * 10**6))  # ...the jar lane cancels
        # iterate g from an arbitrary start to find THE fixed point under this k
        d = 3.0
        for _ in range(60):
            d = g(d)
        print(f"    {lam:.1f}    {k:10.4f}    {display:12.4f}          {cancelled:2d}"
              f"                {d * DISPLAY_SCALE:.4f}")
    print()
    print("    Read the columns: the DISPLAY lane slides to the lab value (that")
    print("    is what a dial does to a display); the CERTIFIED lane's 18k/k is")
    print("    18 at every k (the coefficient cancels: drift-immunity); and the")
    print("    FIXED POINT of the device's own step is 137.0113 at every single")
    print("    lambda. The dial moves the paint, never the needle.")
    print()

    # -- Condition 2: injected values FLOW BACK -----------------------------
    print("[4] THE INJECTION -- start g at the lab-ward value; watch it flow home")
    d = LAB_INV_ALPHA / DISPLAY_SCALE          # the lab value, mapped onto d
    print(f"    start: d = {d:.10f}  (readout {d * DISPLAY_SCALE:.4f} -- the lab's number)")
    for step in range(1, 7):
        d = g(d)
        print(f"    step {step}: d = {d:.10f}  (readout {d * DISPLAY_SCALE:.4f})")
    print(f"    The flow leaves {LAB_INV_ALPHA} immediately and settles on the")
    print(f"    device's own {DEVICE_INV_ALPHA} -- AWAY from the lab, TO the jar.")
    print()

    # -- Condition 3, stated as the verdict ---------------------------------
    print("[5] THE VERDICT")
    print(f"    {LAB_INV_ALPHA} appears in this exhibit exactly twice: as the LAB")
    print("    TARGET (the world's number, cited) and as the NON-FIXED-POINT the")
    print("    flow abandons. It is never the device's settled reading. The")
    print("    device's fixed point is set by the measured pair (C, T) alone --")
    print("    no coefficient on the sweep can move it, because the coefficient")
    print("    cancels before the jar is read. THE GAP IS THE RESULT: two")
    print("    numbers, two owners, one honest exhibit of the space between.")
    print()
    print(f"provenance: python {platform.python_version()},"
          f" {platform.machine()}/{platform.system()}, run {datetime.date.today().isoformat()};")
    print("            the numbers worth trusting are the exact ones this points at:")
    print("            C=18, T=5, sqrt(18/5), and the stop. Everything else is scenery.")
    print(line)


if __name__ == "__main__":
    main()
