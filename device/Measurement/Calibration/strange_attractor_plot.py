#!/usr/bin/env python3
# =============================================================================
#
#   THE ATTRACTOR PLOT -- Part 2's closing exhibit.
#
#   (operator-directed, 2026-08-13: "demonstrate a 'neighborhood' point on
#    the elaboration heartbeat measure to show the strange attractor.
#    probably should plot it ... that should get you a probably radius of
#    the electron as described by the device.")
#
# =============================================================================
#
#   THE FOUR GATE CONDITIONS (Kodo, 2026-08-13 -- this exhibit is invalid
#   without them):
#    1. The attractor is the device's own sqrt(18/5) -> ~137.011, proved
#       SUPERATTRACTING: g'(d*) = 0 exactly (shown below), quadratic
#       convergence. Every neighborhood seed flows to it.
#    2. "STRANGE"/fractal belongs to the BASIN BOUNDARY -- the Julia set of
#       the degree-3 map in the complex plane -- never to the fixed point,
#       which is clean. The plot labels them accordingly.
#    3. SEEDS are set, the ATTRACTOR is not: the interpolated lab-ward
#       guess (readout 137.0357) enters only as a SEED, and the plot shows
#       it flowing away to 137.011. The attractor is fixed by the measured
#       pair (C, T) and cannot be set.
#    4. THE RADIUS is the device's own neighborhood scale -- model-internal,
#       in the device's units -- NOT the physical electron's measured
#       radius, and never fitted to it (the no-name-bridge).
#
#   THE DERIVATIVE (condition 1, algebra in the header so code can't fudge):
#       g(d)  = d(3C - T d^2)/(2C)
#       g'(d) = (3C - 3T d^2)/(2C)
#       g'(d*) with T d*^2 = C:  (3C - 3C)/(2C) = 0.     Superattracting.
#
#   THE DEVICE'S OWN SCALES (condition 4, cited not invented):
#       count-3 bracket width on the d-line: 1/8      (the certified floor)
#       naturalUnitOrbitRadius = 18, R^2 = 324        (Ep36; k = 5/324)
#       immediate real basin of +d*: (0, sqrt(54/5)) ~ (0, 3.286)
#       (0 is the repeller; beyond sqrt(54/5) seeds cross to the negative
#        root or escape to infinity -- g(10) < 0 and iterates explode)
#
# =============================================================================

import datetime
import platform

import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

C, T = 18, 5
D_STAR = (C / T) ** 0.5
DEVICE_INV_ALPHA = 137.0113
LAB_INV_ALPHA = 137.0357
SCALE = DEVICE_INV_ALPHA / D_STAR


def g(d):
    return d * (3 * C - T * d * d) / (2 * C)


def main():
    fig, axes = plt.subplots(1, 2, figsize=(13, 5.5))
    fig.suptitle(
        "The device's attractor: every seed flows to its own number "
        "(sqrt(18/5) → 137.011)", fontsize=13)

    # ── Panel 1: the flows (real line) — condition 1 and 3 ────────────────
    ax = axes[0]
    seeds = [0.3, 0.8, 1.2, 1.6, 2.2, 2.6,
             LAB_INV_ALPHA / SCALE]           # the lab-ward guess, AS A SEED
    for s in seeds:
        orbit, d = [s], s
        for _ in range(10):
            d = g(d)
            orbit.append(d)
        is_lab = abs(s - LAB_INV_ALPHA / SCALE) < 1e-12
        ax.plot(range(len(orbit)), [x * SCALE for x in orbit],
                marker="o", ms=3.5,
                lw=2.2 if is_lab else 1.1,
                color="crimson" if is_lab else "steelblue",
                label=("seed = lab-ward guess (137.0357)" if is_lab else None))
    ax.axhline(DEVICE_INV_ALPHA, color="black", lw=1, ls="--")
    ax.annotate("the attractor: 137.011 — the device's own number\n"
                "superattracting: g'(d*) = 0 (quadratic convergence)",
                xy=(6.3, DEVICE_INV_ALPHA), fontsize=9,
                xytext=(3.2, DEVICE_INV_ALPHA + 32),
                arrowprops=dict(arrowstyle="->", lw=0.8))
    ax.set_xlabel("iteration of the device's own step  g(d) = d(3C−Td²)/(2C)")
    ax.set_ylabel("readout scale (inverse-α)")
    ax.set_title("Every neighborhood seed flows home — including the lab-ward one",
                 fontsize=10)
    ax.legend(loc="lower right", fontsize=8)

    # ── Panel 2: the basin boundary in ℂ — condition 2 (the honest 'strange') ──
    ax = axes[1]
    n, m = 700, 560
    re = np.linspace(-3.2, 3.2, n)
    im = np.linspace(-2.56, 2.56, m)
    Z = re[None, :] + 1j * im[:, None]
    with np.errstate(all="ignore"):
        for _ in range(40):
            Z = Z * (3 * C - T * Z * Z) / (2 * C)
    basin = np.zeros(Z.shape)
    with np.errstate(all="ignore"):
        basin[np.abs(Z - D_STAR) < 1e-6] = 1.0      # + root basin
        basin[np.abs(Z + D_STAR) < 1e-6] = -1.0     # − root basin
    ax.imshow(basin, extent=[-3.2, 3.2, -2.56, 2.56], origin="lower",
              cmap="coolwarm", interpolation="nearest")
    ax.plot([D_STAR], [0], "k*", ms=12)
    ax.plot([-D_STAR], [0], "k*", ms=12)
    ax.plot([0], [0], "wx", ms=8, mew=2)
    ax.annotate("+√(18/5): the clean attractor", xy=(D_STAR, 0), fontsize=8,
                xytext=(0.35, 1.9), arrowprops=dict(arrowstyle="->", lw=0.7))
    ax.annotate("the repeller at 0", xy=(0, 0), fontsize=8,
                xytext=(-3.0, 1.6), arrowprops=dict(arrowstyle="->", lw=0.7))
    ax.set_title("The honest 'strange' object: the BASIN BOUNDARY (Julia set)\n"
                 "— fractal edge between the two root basins AND the escape basin\n"
                 "at infinity (grey); the attractor itself is clean",
                 fontsize=9)
    ax.set_xlabel("Re(d)")
    ax.set_ylabel("Im(d)")

    fig.text(0.5, 0.015,
             "THE RADIUS, as the device describes it (model-internal, device units, never the lab's "
             "femtometer): bracket width 1/8; orbit radius 18, R²=324 (Ep36); immediate basin (0, √(54/5)) ≈ (0, 3.29).",
             fontsize=8, ha="center")
    fig.tight_layout(rect=[0, 0.045, 1, 0.95])

    out = __file__.replace(".py", ".png")
    fig.savefig(out, dpi=110)
    print(f"saved: {out}")
    print(f"g'(d*) check: {(3*C - 3*T*D_STAR*D_STAR)/(2*C):+.2e} (exactly 0 in algebra)")
    print(f"lab-ward seed flow: ", end="")
    d = LAB_INV_ALPHA / SCALE
    for _ in range(4):
        d = g(d)
        print(f"{d*SCALE:.4f} ", end="")
    print(f"\nprovenance: numpy {np.__version__}, matplotlib {matplotlib.__version__},"
          f" python {platform.python_version()}, {platform.machine()},"
          f" {datetime.date.today().isoformat()}")


if __name__ == "__main__":
    main()
