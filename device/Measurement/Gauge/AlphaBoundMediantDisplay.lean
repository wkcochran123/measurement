import Measurement.AlphaBoundMediant

/-! # Measurement.Gauge.AlphaBoundMediantDisplay — the #eval readout layer for `AlphaBoundMediant` (Gauge
phase). The mediant/CF descent, the count-3 bracket, `mediantInvAlphaAt` — the physics that FEEDS THE JAR (via
AffineConstant) — STAYS upstream; only the display moves here, importing the physics one-way (leaf). -/

open Measurement

#eval s!"crossing = √90/5 = √(18/5) ≈ 1.897367;  partial quotients [a₀;a₁,a₂,…] (modulo realm):"

#eval s!"  {(crossingConvergents 8).map (fun t => t.1)}"

#eval s!"convergents h/k and inv-α(×1e18):"

#eval String.intercalate "\n" ((crossingConvergents 8).mapIdx (fun i t =>
  s!"  conv{i} (a={t.1}): {t.2.1}/{t.2.2}   inv-α = {mediantInvAlphaAt {numerator:=t.2.1,denominator:=t.2.2}}"))

#eval String.intercalate "\n" ((crossingConvergents 20).mapIdx (fun i t =>
  s!"RICH conv{i} a={t.1} k={t.2.2} invA18={mediantInvAlphaAt {numerator:=t.2.1,denominator:=t.2.2}}"))

#eval s!"COUNT-TO-3 (3 partial quotients) bracket:  [{count3Lo.numerator}/{count3Lo.denominator} , {count3Hi.numerator}/{count3Hi.denominator}]  inv-α ∈ [{count3InvHi} .. {count3InvLo}]"

#eval s!"COUNT-TO-4 (4 partial quotients) bracket:  [{count4Lo.numerator}/{count4Lo.denominator} , {count4Hi.numerator}/{count4Hi.denominator}]  inv-α ∈ [{mediantInvAlphaAt count4Lo} .. {mediantInvAlphaAt count4Hi}]"
