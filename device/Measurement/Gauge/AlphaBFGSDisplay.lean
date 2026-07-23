import Measurement.AlphaBFGS

/-! # Measurement.Gauge.AlphaBFGSDisplay — the #eval readout layer for `AlphaBFGS` (Gauge phase). The BFGS
computation (`bfgsAt`/`invAlphaAt`/…, consumed by CalibrationTwoPaths + TwoSlipRecursion) STAYS upstream; only
the display moves here, importing the physics one-way (leaf). -/

open Measurement Measurement.AlphaBFGS

#eval s!"measured second variation: C=slip(1)={measuredC}  T=target={measuredT}  → crossing √({measuredC}/{measuredT})"
#eval s!"BFGS count 0 (run 1): d≈{(bfgsAt 0 d0).scaledFloor (pow10 6)}e-6   invα(×1e18)={invAlphaAt (bfgsAt 0 d0)}"
#eval s!"BFGS count 1        : d≈{(bfgsAt 1 d0).scaledFloor (pow10 6)}e-6   invα(×1e18)={invAlphaAt (bfgsAt 1 d0)}"
#eval s!"BFGS count 2        : d≈{(bfgsAt 2 d0).scaledFloor (pow10 6)}e-6   invα(×1e18)={invAlphaAt (bfgsAt 2 d0)}"
#eval s!"BFGS count 3        : d≈{(bfgsAt 3 d0).scaledFloor (pow10 6)}e-6   invα(×1e18)={invAlphaAt (bfgsAt 3 d0)}"
#eval s!"count-1 reduced fraction: {(bfgsAt 1 d0).numerator}/{(bfgsAt 1 d0).denominator}  (cf CF convergent 17/9)"
