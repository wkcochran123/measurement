import Measurement.Chapter7

namespace Measurement


structure TimeSeries (σ : Type u)(τ : Type (u+1)) where
  rows: Counting σ τ
  columns: Alphabet τ

structure EventSeries (σ : Type u)(τ : Type (u+1)) where
  rows: Counting σ τ
  columns: Alphabet τ

structure Surface (σ : Type u)(τ : Type (u+1)) where
  ordintate: TimeSeries σ τ
  abscissa: EventSeries σ τ

structure Residue (σ : Type u)(τ : Type (u+1)) where
  left: Surface σ τ
  right: Surface σ τ
  distance: Statistic σ τ


abbrev Ruler := Residue Nat (ULift Nat)

/-- Column lookup: where does a `τ` land in the alphabet? -/
def Alphabet.indexOf? {τ : Type u} [DecidableEq τ] (A : Alphabet τ) (t : τ) : Option Nat :=
  Enumeration.indexOf A.symbols t

/-- Apply the counting's ArrowOfTime once. Right now this is constant-in-time. -/
def Counting.observe? {σ : Type u} {τ : Type (u+1)}
  (C : Counting σ τ) : Option (Event τ) :=
  ArrowOfTime.elapse C.events

/--
A time series "integral": turn row ticks into a Nat by
(1) observing the τ-event (post-tick),
(2) locating its column in the alphabet,
(3) returning that column index (or 0 if absent).

This is the minimal honest integral with the current `Counting`.
Later, when `Counting` becomes iterative, this becomes a fold over ticks.
-/
noncomputable def TimeSeries.integral
  {σ : Type u} {τ : Type (u+1)}
  [DecidableEq τ]
  (TS : TimeSeries σ τ) : Enumeration (Event σ) → Nat :=
  fun _ticks =>
    match Counting.observe? TS.rows with
    | none      => 0
    | some eτ   =>
        match Alphabet.indexOf? TS.columns eτ.symbol with
        | none   => 0
        | some k => k

/-- Same story for EventSeries (it is structurally identical right now). -/
noncomputable def EventSeries.integral
  {σ : Type u} {τ : Type (u+1)}
  [DecidableEq τ]
  (ES : EventSeries σ τ) : Enumeration (Event σ) → Nat :=
  fun _ticks =>
    match Counting.observe? ES.rows with
    | none      => 0
    | some eτ   =>
        match Alphabet.indexOf? ES.columns eτ.symbol with
        | none   => 0
        | some k => k

/--
Build an `Integration` snapshot from a series:
- accumulator holds the running state (here: a singleton is enough),
- integral is the series' integral functional.
-/
noncomputable def TimeSeries.toIntegration
  {σ : Type u} {τ : Type (u+1)}
  [DecidableEq τ]
  (TS : TimeSeries σ τ) : Integration σ τ :=
  let A : Accumulator σ τ :=
    { counting := TS.rows
      total    := Enumeration.len TS.rows.ticks }
  { accumulator := Enumeration.cons A Enumeration.nil
    integral    := TimeSeries.integral TS }

noncomputable def EventSeries.toIntegration
  {σ : Type u} {τ : Type (u+1)}
  [DecidableEq τ]
  (ES : EventSeries σ τ) : Integration σ τ :=
  let A : Accumulator σ τ :=
    { counting := ES.rows
      total    := Enumeration.len ES.rows.ticks }
  { accumulator := Enumeration.cons A Enumeration.nil
    integral    := EventSeries.integral ES }

/--
A residue statistic: compare left vs right by
summing the discrepancies of ordinate and abscissa integrals.

Right now we can define the discrepancy as `Nat` absolute difference.
If you already have a `Norm.distance` notion elsewhere, substitute it here.
-/
def natAbsDiff (a b : Nat) : Nat :=
  if h : a ≤ b then b - a else a - b

noncomputable def Residue.computeDistance
  {σ : Type u} {τ : Type (u+1)}
  [DecidableEq τ]
  (R : Residue σ τ) : Nat :=
  let Il_o := TimeSeries.toIntegration R.left.ordintate
  let Ir_o := TimeSeries.toIntegration R.right.ordintate
  let Il_a := EventSeries.toIntegration R.left.abscissa
  let Ir_a := EventSeries.toIntegration R.right.abscissa
  let dl := natAbsDiff Il_o.value Ir_o.value
  let da := natAbsDiff Il_a.value Ir_a.value
  dl + da


end Measurement
