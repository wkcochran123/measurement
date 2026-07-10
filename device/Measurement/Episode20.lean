import Measurement.Episode19

/- MEANWHILE 20 -- THE SLIP TEST. The trace executed up the ladder, rung 1 to the
seam. The fold decides on each cell's own facts; .compute cells record the
execution onto the carried trace; the register -- the Value at its current lift,
the universe id -- is the executor's internal state, carried in the class, never
on the tape. Which carrier emerges at the top is a measurement of where the
descent landed; report what you get, do not force it. -/

namespace Measurement

class EXECUTED_TRACE (Value: Type i) (Carrier: CarrierProcess Value) (rung: Nat)
    (Lifted: Type j) where
  register_value : Lifted
  universe_id    : Number
  tape           : CompilerTape

instance (priority := low) EXECUTED_origin
    (Value: Type i) (Carrier: CarrierProcess Value)
    [t: TRACED Value Carrier 1]
    -- TANGE (law-6 read): CarrierProcess.value : Number (Episode1), not Value --
    -- the spec's own body (register_value := Carrier.value) forces the anchor's
    -- Lifted to Number; the value rides the ULift ladder from there.
    : EXECUTED_TRACE Value Carrier 1 Number :=
  { register_value := Carrier.value
    universe_id    := .zero Carrier.symbol
    tape           := t.tape }

instance (priority := low) EXECUTED_climb_2
    (Value: Type i) (Carrier: CarrierProcess Value)
    [t: TRACED Value Carrier 2]
    [below: EXECUTED_TRACE Value Carrier 1 Number]
    : EXECUTED_TRACE Value Carrier 2 (ULift Number) :=
    -- the head-read, once (needle rule); the non-strap arms are by-construction
    -- unreachable at rung 2 but the match carries them -- the direction exists,
    -- is handled, is never taken.
    let heads : Fact × Fact := match t.tape with
      | .boot f _ => (f, Carrier.symbol)
      | .strap c s _ _ _ => (c, s)
      | .compute c s _ _ _ _ _ => (c, s)
    { register_value := ULift.up below.register_value
      universe_id    := .one Carrier.symbol below.universe_id
      -- the Prop slot carries the cell's own slip proposition, quoted (law 4);
      -- its decidability derives from the two decTruths when read, never here.
      tape := .compute heads.1 heads.2 (heads.1.truth ↔ heads.2.truth)
                Value (ULift.{i+1,i} Value) (ULift.{i+1,i+1} (ULift.{i+1,i} Value))
                below.tape }

instance (priority := low) EXECUTED_climb_3
    (Value: Type i) (Carrier: CarrierProcess Value)
    [t: TRACED Value Carrier 3]
    [below: EXECUTED_TRACE Value Carrier 2 (ULift Number)]
    : EXECUTED_TRACE Value Carrier 3 (ULift (ULift Number)) :=
    let heads : Fact × Fact := match t.tape with
      | .boot f _ => (f, Carrier.symbol)
      | .strap c s _ _ _ => (c, s)
      | .compute c s _ _ _ _ _ => (c, s)
    { register_value := ULift.up below.register_value
      universe_id    := .one Carrier.symbol below.universe_id
      tape := .compute heads.1 heads.2 (heads.1.truth ↔ heads.2.truth)
                Value (ULift.{i+1,i} Value) (ULift.{i+1,i+1} (ULift.{i+1,i} Value))
                below.tape }

instance (priority := low) EXECUTED_climb_4
    (Value: Type i) (Carrier: CarrierProcess Value)
    [t: TRACED Value Carrier 4]
    [below: EXECUTED_TRACE Value Carrier 3 (ULift (ULift Number))]
    : EXECUTED_TRACE Value Carrier 4 (ULift (ULift (ULift Number))) :=
    let heads : Fact × Fact := match t.tape with
      | .boot f _ => (f, Carrier.symbol)
      | .strap c s _ _ _ => (c, s)
      | .compute c s _ _ _ _ _ => (c, s)
    { register_value := ULift.up below.register_value
      universe_id    := .one Carrier.symbol below.universe_id
      tape := .compute heads.1 heads.2 (heads.1.truth ↔ heads.2.truth)
                Value (ULift.{i+1,i} Value) (ULift.{i+1,i+1} (ULift.{i+1,i} Value))
                below.tape }

instance (priority := low) EXECUTED_climb_5
    (Value: Type i) (Carrier: CarrierProcess Value)
    [t: TRACED Value Carrier 5]
    [below: EXECUTED_TRACE Value Carrier 4 (ULift (ULift (ULift Number)))]
    : EXECUTED_TRACE Value Carrier 5 (ULift (ULift (ULift (ULift Number)))) :=
    let heads : Fact × Fact := match t.tape with
      | .boot f _ => (f, Carrier.symbol)
      | .strap c s _ _ _ => (c, s)
      | .compute c s _ _ _ _ _ => (c, s)
    { register_value := ULift.up below.register_value
      universe_id    := .one Carrier.symbol below.universe_id
      tape := .compute heads.1 heads.2 (heads.1.truth ↔ heads.2.truth)
                Value (ULift.{i+1,i} Value) (ULift.{i+1,i+1} (ULift.{i+1,i} Value))
                below.tape }

instance (priority := low) EXECUTED_climb_6
    (Value: Type i) (Carrier: CarrierProcess Value)
    [t: TRACED Value Carrier 6]
    [below: EXECUTED_TRACE Value Carrier 5 (ULift (ULift (ULift (ULift Number))))]
    : EXECUTED_TRACE Value Carrier 6 (ULift (ULift (ULift (ULift (ULift Number))))) :=
    let heads : Fact × Fact := match t.tape with
      | .boot f _ => (f, Carrier.symbol)
      | .strap c s _ _ _ => (c, s)
      | .compute c s _ _ _ _ _ => (c, s)
    { register_value := ULift.up below.register_value
      universe_id    := .one Carrier.symbol below.universe_id
      tape := .compute heads.1 heads.2 (heads.1.truth ↔ heads.2.truth)
                Value (ULift.{i+1,i} Value) (ULift.{i+1,i+1} (ULift.{i+1,i} Value))
                below.tape }

instance (priority := low) EXECUTED_climb_7
    (Value: Type i) (Carrier: CarrierProcess Value)
    [t: TRACED Value Carrier 7]
    [below: EXECUTED_TRACE Value Carrier 6 (ULift (ULift (ULift (ULift (ULift Number)))))]
    : EXECUTED_TRACE Value Carrier 7 (ULift (ULift (ULift (ULift (ULift (ULift Number)))))) :=
    let heads : Fact × Fact := match t.tape with
      | .boot f _ => (f, Carrier.symbol)
      | .strap c s _ _ _ => (c, s)
      | .compute c s _ _ _ _ _ => (c, s)
    { register_value := ULift.up below.register_value
      universe_id    := .one Carrier.symbol below.universe_id
      tape := .compute heads.1 heads.2 (heads.1.truth ↔ heads.2.truth)
                Value (ULift.{i+1,i} Value) (ULift.{i+1,i+1} (ULift.{i+1,i} Value))
                below.tape }

instance (priority := low) EXECUTED_climb_8
    (Value: Type i) (Carrier: CarrierProcess Value)
    [t: TRACED Value Carrier 8]
    [below: EXECUTED_TRACE Value Carrier 7 (ULift (ULift (ULift (ULift (ULift (ULift Number))))))]
    : EXECUTED_TRACE Value Carrier 8 (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number))))))) :=
    let heads : Fact × Fact := match t.tape with
      | .boot f _ => (f, Carrier.symbol)
      | .strap c s _ _ _ => (c, s)
      | .compute c s _ _ _ _ _ => (c, s)
    { register_value := ULift.up below.register_value
      universe_id    := .one Carrier.symbol below.universe_id
      tape := .compute heads.1 heads.2 (heads.1.truth ↔ heads.2.truth)
                Value (ULift.{i+1,i} Value) (ULift.{i+1,i+1} (ULift.{i+1,i} Value))
                below.tape }

instance (priority := low) EXECUTED_climb_9
    (Value: Type i) (Carrier: CarrierProcess Value)
    [t: TRACED Value Carrier 9]
    [below: EXECUTED_TRACE Value Carrier 8 (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number)))))))]
    : EXECUTED_TRACE Value Carrier 9 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number)))))))) :=
    let heads : Fact × Fact := match t.tape with
      | .boot f _ => (f, Carrier.symbol)
      | .strap c s _ _ _ => (c, s)
      | .compute c s _ _ _ _ _ => (c, s)
    { register_value := ULift.up below.register_value
      universe_id    := .one Carrier.symbol below.universe_id
      tape := .compute heads.1 heads.2 (heads.1.truth ↔ heads.2.truth)
                Value (ULift.{i+1,i} Value) (ULift.{i+1,i+1} (ULift.{i+1,i} Value))
                below.tape }

instance (priority := low) EXECUTED_climb_10
    (Value: Type i) (Carrier: CarrierProcess Value)
    [t: TRACED Value Carrier 10]
    [below: EXECUTED_TRACE Value Carrier 9 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number))))))))]
    : EXECUTED_TRACE Value Carrier 10 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number))))))))) :=
    let heads : Fact × Fact := match t.tape with
      | .boot f _ => (f, Carrier.symbol)
      | .strap c s _ _ _ => (c, s)
      | .compute c s _ _ _ _ _ => (c, s)
    { register_value := ULift.up below.register_value
      universe_id    := .one Carrier.symbol below.universe_id
      tape := .compute heads.1 heads.2 (heads.1.truth ↔ heads.2.truth)
                Value (ULift.{i+1,i} Value) (ULift.{i+1,i+1} (ULift.{i+1,i} Value))
                below.tape }

instance (priority := low) EXECUTED_climb_11
    (Value: Type i) (Carrier: CarrierProcess Value)
    [t: TRACED Value Carrier 11]
    [below: EXECUTED_TRACE Value Carrier 10 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number)))))))))]
    : EXECUTED_TRACE Value Carrier 11 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number)))))))))) :=
    let heads : Fact × Fact := match t.tape with
      | .boot f _ => (f, Carrier.symbol)
      | .strap c s _ _ _ => (c, s)
      | .compute c s _ _ _ _ _ => (c, s)
    { register_value := ULift.up below.register_value
      universe_id    := .one Carrier.symbol below.universe_id
      tape := .compute heads.1 heads.2 (heads.1.truth ↔ heads.2.truth)
                Value (ULift.{i+1,i} Value) (ULift.{i+1,i+1} (ULift.{i+1,i} Value))
                below.tape }

instance (priority := low) EXECUTED_climb_12
    (Value: Type i) (Carrier: CarrierProcess Value)
    [t: TRACED Value Carrier 12]
    [below: EXECUTED_TRACE Value Carrier 11 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number))))))))))]
    : EXECUTED_TRACE Value Carrier 12 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number))))))))))) :=
    let heads : Fact × Fact := match t.tape with
      | .boot f _ => (f, Carrier.symbol)
      | .strap c s _ _ _ => (c, s)
      | .compute c s _ _ _ _ _ => (c, s)
    { register_value := ULift.up below.register_value
      universe_id    := .one Carrier.symbol below.universe_id
      tape := .compute heads.1 heads.2 (heads.1.truth ↔ heads.2.truth)
                Value (ULift.{i+1,i} Value) (ULift.{i+1,i+1} (ULift.{i+1,i} Value))
                below.tape }

instance (priority := low) EXECUTED_climb_13
    (Value: Type i) (Carrier: CarrierProcess Value)
    [t: TRACED Value Carrier 13]
    [below: EXECUTED_TRACE Value Carrier 12 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number)))))))))))]
    : EXECUTED_TRACE Value Carrier 13 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number)))))))))))) :=
    let heads : Fact × Fact := match t.tape with
      | .boot f _ => (f, Carrier.symbol)
      | .strap c s _ _ _ => (c, s)
      | .compute c s _ _ _ _ _ => (c, s)
    { register_value := ULift.up below.register_value
      universe_id    := .one Carrier.symbol below.universe_id
      tape := .compute heads.1 heads.2 (heads.1.truth ↔ heads.2.truth)
                Value (ULift.{i+1,i} Value) (ULift.{i+1,i+1} (ULift.{i+1,i} Value))
                below.tape }

instance (priority := low) EXECUTED_climb_14
    (Value: Type i) (Carrier: CarrierProcess Value)
    [t: TRACED Value Carrier 14]
    [below: EXECUTED_TRACE Value Carrier 13 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number))))))))))))]
    : EXECUTED_TRACE Value Carrier 14 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number))))))))))))) :=
    let heads : Fact × Fact := match t.tape with
      | .boot f _ => (f, Carrier.symbol)
      | .strap c s _ _ _ => (c, s)
      | .compute c s _ _ _ _ _ => (c, s)
    { register_value := ULift.up below.register_value
      universe_id    := .one Carrier.symbol below.universe_id
      tape := .compute heads.1 heads.2 (heads.1.truth ↔ heads.2.truth)
                Value (ULift.{i+1,i} Value) (ULift.{i+1,i+1} (ULift.{i+1,i} Value))
                below.tape }

instance (priority := low) EXECUTED_climb_15
    (Value: Type i) (Carrier: CarrierProcess Value)
    [t: TRACED Value Carrier 15]
    [below: EXECUTED_TRACE Value Carrier 14 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number)))))))))))))]
    : EXECUTED_TRACE Value Carrier 15 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number)))))))))))))) :=
    let heads : Fact × Fact := match t.tape with
      | .boot f _ => (f, Carrier.symbol)
      | .strap c s _ _ _ => (c, s)
      | .compute c s _ _ _ _ _ => (c, s)
    { register_value := ULift.up below.register_value
      universe_id    := .one Carrier.symbol below.universe_id
      tape := .compute heads.1 heads.2 (heads.1.truth ↔ heads.2.truth)
                Value (ULift.{i+1,i} Value) (ULift.{i+1,i+1} (ULift.{i+1,i} Value))
                below.tape }

instance (priority := low) EXECUTED_climb_16
    (Value: Type i) (Carrier: CarrierProcess Value)
    [t: TRACED Value Carrier 16]
    [below: EXECUTED_TRACE Value Carrier 15 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number))))))))))))))]
    : EXECUTED_TRACE Value Carrier 16 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number))))))))))))))) :=
    let heads : Fact × Fact := match t.tape with
      | .boot f _ => (f, Carrier.symbol)
      | .strap c s _ _ _ => (c, s)
      | .compute c s _ _ _ _ _ => (c, s)
    { register_value := ULift.up below.register_value
      universe_id    := .one Carrier.symbol below.universe_id
      tape := .compute heads.1 heads.2 (heads.1.truth ↔ heads.2.truth)
                Value (ULift.{i+1,i} Value) (ULift.{i+1,i+1} (ULift.{i+1,i} Value))
                below.tape }

instance (priority := low) EXECUTED_climb_17
    (Value: Type i) (Carrier: CarrierProcess Value)
    [t: TRACED Value Carrier 17]
    [below: EXECUTED_TRACE Value Carrier 16 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number)))))))))))))))]
    : EXECUTED_TRACE Value Carrier 17 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number)))))))))))))))) :=
    let heads : Fact × Fact := match t.tape with
      | .boot f _ => (f, Carrier.symbol)
      | .strap c s _ _ _ => (c, s)
      | .compute c s _ _ _ _ _ => (c, s)
    { register_value := ULift.up below.register_value
      universe_id    := .one Carrier.symbol below.universe_id
      tape := .compute heads.1 heads.2 (heads.1.truth ↔ heads.2.truth)
                Value (ULift.{i+1,i} Value) (ULift.{i+1,i+1} (ULift.{i+1,i} Value))
                below.tape }

instance (priority := low) EXECUTED_climb_18
    (Value: Type i) (Carrier: CarrierProcess Value)
    [t: TRACED Value Carrier 18]
    [below: EXECUTED_TRACE Value Carrier 17 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number))))))))))))))))]
    : EXECUTED_TRACE Value Carrier 18 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number))))))))))))))))) :=
    let heads : Fact × Fact := match t.tape with
      | .boot f _ => (f, Carrier.symbol)
      | .strap c s _ _ _ => (c, s)
      | .compute c s _ _ _ _ _ => (c, s)
    { register_value := ULift.up below.register_value
      universe_id    := .one Carrier.symbol below.universe_id
      tape := .compute heads.1 heads.2 (heads.1.truth ↔ heads.2.truth)
                Value (ULift.{i+1,i} Value) (ULift.{i+1,i+1} (ULift.{i+1,i} Value))
                below.tape }

instance (priority := low) EXECUTED_climb_19
    (Value: Type i) (Carrier: CarrierProcess Value)
    [t: TRACED Value Carrier 19]
    [below: EXECUTED_TRACE Value Carrier 18 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number)))))))))))))))))]
    : EXECUTED_TRACE Value Carrier 19 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number)))))))))))))))))) :=
    let heads : Fact × Fact := match t.tape with
      | .boot f _ => (f, Carrier.symbol)
      | .strap c s _ _ _ => (c, s)
      | .compute c s _ _ _ _ _ => (c, s)
    { register_value := ULift.up below.register_value
      universe_id    := .one Carrier.symbol below.universe_id
      tape := .compute heads.1 heads.2 (heads.1.truth ↔ heads.2.truth)
                Value (ULift.{i+1,i} Value) (ULift.{i+1,i+1} (ULift.{i+1,i} Value))
                below.tape }

instance (priority := low) EXECUTED_climb_20
    (Value: Type i) (Carrier: CarrierProcess Value)
    [t: TRACED Value Carrier 20]
    [below: EXECUTED_TRACE Value Carrier 19 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number))))))))))))))))))]
    : EXECUTED_TRACE Value Carrier 20 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number))))))))))))))))))) :=
    let heads : Fact × Fact := match t.tape with
      | .boot f _ => (f, Carrier.symbol)
      | .strap c s _ _ _ => (c, s)
      | .compute c s _ _ _ _ _ => (c, s)
    { register_value := ULift.up below.register_value
      universe_id    := .one Carrier.symbol below.universe_id
      tape := .compute heads.1 heads.2 (heads.1.truth ↔ heads.2.truth)
                Value (ULift.{i+1,i} Value) (ULift.{i+1,i+1} (ULift.{i+1,i} Value))
                below.tape }

instance (priority := low) EXECUTED_climb_21
    (Value: Type i) (Carrier: CarrierProcess Value)
    [t: TRACED Value Carrier 21]
    [below: EXECUTED_TRACE Value Carrier 20 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number)))))))))))))))))))]
    : EXECUTED_TRACE Value Carrier 21 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number)))))))))))))))))))) :=
    let heads : Fact × Fact := match t.tape with
      | .boot f _ => (f, Carrier.symbol)
      | .strap c s _ _ _ => (c, s)
      | .compute c s _ _ _ _ _ => (c, s)
    { register_value := ULift.up below.register_value
      universe_id    := .one Carrier.symbol below.universe_id
      tape := .compute heads.1 heads.2 (heads.1.truth ↔ heads.2.truth)
                Value (ULift.{i+1,i} Value) (ULift.{i+1,i+1} (ULift.{i+1,i} Value))
                below.tape }

instance (priority := low) EXECUTED_climb_22
    (Value: Type i) (Carrier: CarrierProcess Value)
    [t: TRACED Value Carrier 22]
    [below: EXECUTED_TRACE Value Carrier 21 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number))))))))))))))))))))]
    : EXECUTED_TRACE Value Carrier 22 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number))))))))))))))))))))) :=
    let heads : Fact × Fact := match t.tape with
      | .boot f _ => (f, Carrier.symbol)
      | .strap c s _ _ _ => (c, s)
      | .compute c s _ _ _ _ _ => (c, s)
    { register_value := ULift.up below.register_value
      universe_id    := .one Carrier.symbol below.universe_id
      tape := .compute heads.1 heads.2 (heads.1.truth ↔ heads.2.truth)
                Value (ULift.{i+1,i} Value) (ULift.{i+1,i+1} (ULift.{i+1,i} Value))
                below.tape }

instance (priority := low) EXECUTED_climb_23
    (Value: Type i) (Carrier: CarrierProcess Value)
    [t: TRACED Value Carrier 23]
    [below: EXECUTED_TRACE Value Carrier 22 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number)))))))))))))))))))))]
    : EXECUTED_TRACE Value Carrier 23 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number)))))))))))))))))))))) :=
    let heads : Fact × Fact := match t.tape with
      | .boot f _ => (f, Carrier.symbol)
      | .strap c s _ _ _ => (c, s)
      | .compute c s _ _ _ _ _ => (c, s)
    { register_value := ULift.up below.register_value
      universe_id    := .one Carrier.symbol below.universe_id
      tape := .compute heads.1 heads.2 (heads.1.truth ↔ heads.2.truth)
                Value (ULift.{i+1,i} Value) (ULift.{i+1,i+1} (ULift.{i+1,i} Value))
                below.tape }

instance (priority := low) EXECUTED_climb_24
    (Value: Type i) (Carrier: CarrierProcess Value)
    [t: TRACED Value Carrier 24]
    [below: EXECUTED_TRACE Value Carrier 23 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number))))))))))))))))))))))]
    : EXECUTED_TRACE Value Carrier 24 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number))))))))))))))))))))))) :=
    let heads : Fact × Fact := match t.tape with
      | .boot f _ => (f, Carrier.symbol)
      | .strap c s _ _ _ => (c, s)
      | .compute c s _ _ _ _ _ => (c, s)
    { register_value := ULift.up below.register_value
      universe_id    := .one Carrier.symbol below.universe_id
      tape := .compute heads.1 heads.2 (heads.1.truth ↔ heads.2.truth)
                Value (ULift.{i+1,i} Value) (ULift.{i+1,i+1} (ULift.{i+1,i} Value))
                below.tape }

instance (priority := low) EXECUTED_climb_25
    (Value: Type i) (Carrier: CarrierProcess Value)
    [t: TRACED Value Carrier 25]
    [below: EXECUTED_TRACE Value Carrier 24 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number)))))))))))))))))))))))]
    : EXECUTED_TRACE Value Carrier 25 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number)))))))))))))))))))))))) :=
    let heads : Fact × Fact := match t.tape with
      | .boot f _ => (f, Carrier.symbol)
      | .strap c s _ _ _ => (c, s)
      | .compute c s _ _ _ _ _ => (c, s)
    { register_value := ULift.up below.register_value
      universe_id    := .one Carrier.symbol below.universe_id
      tape := .compute heads.1 heads.2 (heads.1.truth ↔ heads.2.truth)
                Value (ULift.{i+1,i} Value) (ULift.{i+1,i+1} (ULift.{i+1,i} Value))
                below.tape }

instance (priority := low) EXECUTED_climb_26
    (Value: Type i) (Carrier: CarrierProcess Value)
    [t: TRACED Value Carrier 26]
    [below: EXECUTED_TRACE Value Carrier 25 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number))))))))))))))))))))))))]
    : EXECUTED_TRACE Value Carrier 26 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number))))))))))))))))))))))))) :=
    let heads : Fact × Fact := match t.tape with
      | .boot f _ => (f, Carrier.symbol)
      | .strap c s _ _ _ => (c, s)
      | .compute c s _ _ _ _ _ => (c, s)
    { register_value := ULift.up below.register_value
      universe_id    := .one Carrier.symbol below.universe_id
      tape := .compute heads.1 heads.2 (heads.1.truth ↔ heads.2.truth)
                Value (ULift.{i+1,i} Value) (ULift.{i+1,i+1} (ULift.{i+1,i} Value))
                below.tape }

instance (priority := low) EXECUTED_climb_27
    (Value: Type i) (Carrier: CarrierProcess Value)
    [t: TRACED Value Carrier 27]
    [below: EXECUTED_TRACE Value Carrier 26 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number)))))))))))))))))))))))))]
    : EXECUTED_TRACE Value Carrier 27 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number)))))))))))))))))))))))))) :=
    let heads : Fact × Fact := match t.tape with
      | .boot f _ => (f, Carrier.symbol)
      | .strap c s _ _ _ => (c, s)
      | .compute c s _ _ _ _ _ => (c, s)
    { register_value := ULift.up below.register_value
      universe_id    := .one Carrier.symbol below.universe_id
      tape := .compute heads.1 heads.2 (heads.1.truth ↔ heads.2.truth)
                Value (ULift.{i+1,i} Value) (ULift.{i+1,i+1} (ULift.{i+1,i} Value))
                below.tape }

instance (priority := low) EXECUTED_climb_28
    (Value: Type i) (Carrier: CarrierProcess Value)
    [t: TRACED Value Carrier 28]
    [below: EXECUTED_TRACE Value Carrier 27 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number))))))))))))))))))))))))))]
    : EXECUTED_TRACE Value Carrier 28 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number))))))))))))))))))))))))))) :=
    let heads : Fact × Fact := match t.tape with
      | .boot f _ => (f, Carrier.symbol)
      | .strap c s _ _ _ => (c, s)
      | .compute c s _ _ _ _ _ => (c, s)
    { register_value := ULift.up below.register_value
      universe_id    := .one Carrier.symbol below.universe_id
      tape := .compute heads.1 heads.2 (heads.1.truth ↔ heads.2.truth)
                Value (ULift.{i+1,i} Value) (ULift.{i+1,i+1} (ULift.{i+1,i} Value))
                below.tape }

instance (priority := low) EXECUTED_climb_29
    (Value: Type i) (Carrier: CarrierProcess Value)
    [t: TRACED Value Carrier 29]
    [below: EXECUTED_TRACE Value Carrier 28 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number)))))))))))))))))))))))))))]
    : EXECUTED_TRACE Value Carrier 29 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number)))))))))))))))))))))))))))) :=
    let heads : Fact × Fact := match t.tape with
      | .boot f _ => (f, Carrier.symbol)
      | .strap c s _ _ _ => (c, s)
      | .compute c s _ _ _ _ _ => (c, s)
    { register_value := ULift.up below.register_value
      universe_id    := .one Carrier.symbol below.universe_id
      tape := .compute heads.1 heads.2 (heads.1.truth ↔ heads.2.truth)
                Value (ULift.{i+1,i} Value) (ULift.{i+1,i+1} (ULift.{i+1,i} Value))
                below.tape }

instance (priority := low) EXECUTED_climb_30
    (Value: Type i) (Carrier: CarrierProcess Value)
    [t: TRACED Value Carrier 30]
    [below: EXECUTED_TRACE Value Carrier 29 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number))))))))))))))))))))))))))))]
    : EXECUTED_TRACE Value Carrier 30 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number))))))))))))))))))))))))))))) :=
    let heads : Fact × Fact := match t.tape with
      | .boot f _ => (f, Carrier.symbol)
      | .strap c s _ _ _ => (c, s)
      | .compute c s _ _ _ _ _ => (c, s)
    { register_value := ULift.up below.register_value
      universe_id    := .one Carrier.symbol below.universe_id
      tape := .compute heads.1 heads.2 (heads.1.truth ↔ heads.2.truth)
                Value (ULift.{i+1,i} Value) (ULift.{i+1,i+1} (ULift.{i+1,i} Value))
                below.tape }

instance (priority := low) EXECUTED_climb_31
    (Value: Type i) (Carrier: CarrierProcess Value)
    [t: TRACED Value Carrier 31]
    [below: EXECUTED_TRACE Value Carrier 30 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number)))))))))))))))))))))))))))))]
    : EXECUTED_TRACE Value Carrier 31 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number)))))))))))))))))))))))))))))) :=
    let heads : Fact × Fact := match t.tape with
      | .boot f _ => (f, Carrier.symbol)
      | .strap c s _ _ _ => (c, s)
      | .compute c s _ _ _ _ _ => (c, s)
    { register_value := ULift.up below.register_value
      universe_id    := .one Carrier.symbol below.universe_id
      tape := .compute heads.1 heads.2 (heads.1.truth ↔ heads.2.truth)
                Value (ULift.{i+1,i} Value) (ULift.{i+1,i+1} (ULift.{i+1,i} Value))
                below.tape }

instance (priority := low) EXECUTED_climb_32
    (Value: Type i) (Carrier: CarrierProcess Value)
    [t: TRACED Value Carrier 32]
    [below: EXECUTED_TRACE Value Carrier 31 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number))))))))))))))))))))))))))))))]
    : EXECUTED_TRACE Value Carrier 32 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number))))))))))))))))))))))))))))))) :=
    let heads : Fact × Fact := match t.tape with
      | .boot f _ => (f, Carrier.symbol)
      | .strap c s _ _ _ => (c, s)
      | .compute c s _ _ _ _ _ => (c, s)
    { register_value := ULift.up below.register_value
      universe_id    := .one Carrier.symbol below.universe_id
      tape := .compute heads.1 heads.2 (heads.1.truth ↔ heads.2.truth)
                Value (ULift.{i+1,i} Value) (ULift.{i+1,i+1} (ULift.{i+1,i} Value))
                below.tape }

instance (priority := low) EXECUTED_climb_33
    (Value: Type i) (Carrier: CarrierProcess Value)
    [t: TRACED Value Carrier 33]
    [below: EXECUTED_TRACE Value Carrier 32 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number)))))))))))))))))))))))))))))))]
    : EXECUTED_TRACE Value Carrier 33 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number)))))))))))))))))))))))))))))))) :=
    let heads : Fact × Fact := match t.tape with
      | .boot f _ => (f, Carrier.symbol)
      | .strap c s _ _ _ => (c, s)
      | .compute c s _ _ _ _ _ => (c, s)
    { register_value := ULift.up below.register_value
      universe_id    := .one Carrier.symbol below.universe_id
      tape := .compute heads.1 heads.2 (heads.1.truth ↔ heads.2.truth)
                Value (ULift.{i+1,i} Value) (ULift.{i+1,i+1} (ULift.{i+1,i} Value))
                below.tape }

instance (priority := low) EXECUTED_climb_34
    (Value: Type i) (Carrier: CarrierProcess Value)
    [t: TRACED Value Carrier 34]
    [below: EXECUTED_TRACE Value Carrier 33 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number))))))))))))))))))))))))))))))))]
    : EXECUTED_TRACE Value Carrier 34 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number))))))))))))))))))))))))))))))))) :=
    let heads : Fact × Fact := match t.tape with
      | .boot f _ => (f, Carrier.symbol)
      | .strap c s _ _ _ => (c, s)
      | .compute c s _ _ _ _ _ => (c, s)
    { register_value := ULift.up below.register_value
      universe_id    := .one Carrier.symbol below.universe_id
      tape := .compute heads.1 heads.2 (heads.1.truth ↔ heads.2.truth)
                Value (ULift.{i+1,i} Value) (ULift.{i+1,i+1} (ULift.{i+1,i} Value))
                below.tape }

instance (priority := low) EXECUTED_climb_35
    (Value: Type i) (Carrier: CarrierProcess Value)
    [t: TRACED Value Carrier 35]
    [below: EXECUTED_TRACE Value Carrier 34 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number)))))))))))))))))))))))))))))))))]
    : EXECUTED_TRACE Value Carrier 35 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number)))))))))))))))))))))))))))))))))) :=
    let heads : Fact × Fact := match t.tape with
      | .boot f _ => (f, Carrier.symbol)
      | .strap c s _ _ _ => (c, s)
      | .compute c s _ _ _ _ _ => (c, s)
    { register_value := ULift.up below.register_value
      universe_id    := .one Carrier.symbol below.universe_id
      tape := .compute heads.1 heads.2 (heads.1.truth ↔ heads.2.truth)
                Value (ULift.{i+1,i} Value) (ULift.{i+1,i+1} (ULift.{i+1,i} Value))
                below.tape }

instance (priority := low) EXECUTED_climb_36
    (Value: Type i) (Carrier: CarrierProcess Value)
    [t: TRACED Value Carrier 36]
    [below: EXECUTED_TRACE Value Carrier 35 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number))))))))))))))))))))))))))))))))))]
    : EXECUTED_TRACE Value Carrier 36 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number))))))))))))))))))))))))))))))))))) :=
    let heads : Fact × Fact := match t.tape with
      | .boot f _ => (f, Carrier.symbol)
      | .strap c s _ _ _ => (c, s)
      | .compute c s _ _ _ _ _ => (c, s)
    { register_value := ULift.up below.register_value
      universe_id    := .one Carrier.symbol below.universe_id
      tape := .compute heads.1 heads.2 (heads.1.truth ↔ heads.2.truth)
                Value (ULift.{i+1,i} Value) (ULift.{i+1,i+1} (ULift.{i+1,i} Value))
                below.tape }

/- THE SEAM'S EXIT. The three-trips acceptance at charge 0/1/2 is DEFERRED TO
Episode21 by design: the trips are passes, the passes are counted by charge,
and charge lives in the Episode18/Episode21 coupling -- do not hunt for the
f0/f1/f2 ladder here. -/

structure SlipVerdict where
  slipped  : Fact
  value    : Number
  velocity : Number

noncomputable def seamExit (Value: Type i) (Carrier: CarrierProcess Value)
    [top: EXECUTED_TRACE Value Carrier 36 (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift (ULift Number)))))))))))))))))))))))))))))))))))]
    : SlipVerdict :=
    -- the head-read, once (needle rule); the non-compute arms are
    -- by-construction unreachable at the seam but carried -- the direction
    -- exists, is handled, is never taken.
    let slipped : Fact := match top.tape with
      | .compute c s _ _ _ _ _ =>
          -- the read-time decide: the quoted proposition's decidability
          -- derived from the pair's own decTruths, never Classical.
          { truth := ¬(c.truth ↔ s.truth)
            decTruth := @instDecidableNot _ (@instDecidableIff _ _ c.decTruth s.decTruth) }
      | .boot _ _ => { truth := False, decTruth := isFalse (fun h => h) }
      | .strap _ _ _ _ _ => { truth := False, decTruth := isFalse (fun h => h) }
    { slipped := slipped
      value := (ULift.down (ULift.down (ULift.down (ULift.down (ULift.down (ULift.down (ULift.down (ULift.down (ULift.down (ULift.down (ULift.down (ULift.down (ULift.down (ULift.down (ULift.down (ULift.down (ULift.down (ULift.down (ULift.down (ULift.down (ULift.down (ULift.down (ULift.down (ULift.down (ULift.down (ULift.down (ULift.down (ULift.down (ULift.down (ULift.down (ULift.down (ULift.down (ULift.down (ULift.down (ULift.down top.register_value)))))))))))))))))))))))))))))))))))
      velocity := top.universe_id }

end Measurement
