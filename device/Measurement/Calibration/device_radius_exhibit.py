#!/usr/bin/env python3
# =============================================================================
#
#   THE RADIUS OF THE ELECTRON, AS DESCRIBED BY THE DEVICE
#   (Part 2, final exhibit -- operator-directed, 2026-08-13: "that should
#    get you a probably radius of the electron as described by the device.
#    should be out the door from there.")
#
# =============================================================================
#
#   KODO'S GATE CONDITIONS (2026-08-13, this exhibit is invalid without them):
#    - The radius is the device's OWN, and it is THEOREM-BACKED: cited from
#      the proved build, never recomputed toward any target.
#    - THE NO-NAME-BRIDGE IS STRUCTURAL: the femtometer appears ONLY as the
#      forbidden crossing -- exactly as 137.0357 appears in the sweep only
#      as the forbidden dial. The device measures THE ELECTRON's orbit in
#      its own units; the world's meters are on the other side of a bridge
#      the device does not cross.
#    - Jar-inert: everything below is cited from gated artifacts.
#
# =============================================================================

LINE = "=" * 74

print(LINE)
print("THE RADIUS, AS THE DEVICE DESCRIBES IT -- cited from the proved build")
print(LINE)
print("""
THE RADIUS, PROVED (not computed here -- CITED):

    naturalUnitOrbitRadius = 18        device units, THE ELECTRON's orbit
      proof:  ForceCountSideTheorem.lean:107
              force_grade_is_eighteen := by decide     (axiom-free)
      -- the same 18 that ForceCount decided 11 =/= 18 against: a number
      -- that has already survived a public two-outcome test.

    R^2 = 18^2 = 324                   AffineConstant.lean:41 (kDen)
    k   = tau / R^2 = 5 / 324          the affine frame's constant

THE NEIGHBORHOOD SCALES AROUND IT (the dynamics' own, from tonight's
gated exhibits):

    count-3 bracket width on d : 1/8          (NewtonCrossing, certified)
    immediate basin (real line): (0, sqrt(54/5)) ~ (0, 3.29) -- bounded;
                                              seeds beyond it cross to the
                                              negative root or escape to
                                              infinity; in C the escape basin
                                              joins the two root basins at a
                                              fractal boundary (the edge, not
                                              the point)
    convergence into the radius: quadratic    (g'(d*) = 0, superattracting)

THE FORBIDDEN CROSSING (the fence, structural):

    the femtometer  --  the world's unit for the world's electron. It
    appears in this exhibit exactly once: HERE, as the crossing the
    no-name-bridge forbids. The device's 18 is not presented as, fitted
    to, or bridged to any physical length. Scope is the electron MODEL;
    the world's meters are the other side of a bridge this device,
    on purpose, does not cross.

IN ONE SENTENCE: the device describes its electron's radius as 18 of its
own units -- proved, decided, and already tested in public -- and says
nothing about femtometers, exactly as designed.
""")
print(LINE)
