import Measurement.Chapter3

namespace Measurement
class TWO_BITS
    (Characteristic   : Type → TOKEN Type)
    (Invariant        : Type)
    (Symbol           : Type)
    (Value            : Type 1)
    (Token            : Type 1)
    (Representative   : Prop)
    (Characterization : Prop)
    (Number           : TOKEN Invariant)
    (Ordinal          : TOKEN Symbol)
    (Truth: BOOL Bool)
    (Metaphor: TOKEN Invariant → EVENT Value  → BOOL Bool)
    (Metafive: TOKEN Symbol → EVENT Token  → BOOL Bool)
    [invariant_equality : DecidableEq (Invariant)]
    [symbol_equality : DecidableEq (Symbol)]
    [value_equality : DecidableEq (Value)]
    [token_equality : DecidableEq (Token)]
    [DISTINGUISHABLE Characteristic Invariant]
    [DISTINGUISHABLE Characteristic Symbol]
    [event: ADMISSIBLE Invariant Value Metaphor]
    [ADMISSIBLE Symbol Token fun _ t => ADMISSIBLE.admissible? Metaphor Number t]
    [ADMISSIBLE Symbol Token Metafive]
    [COUNTABLE  Characteristic Invariant Symbol Value Token Number Metaphor]
    [NUMERIC  Characteristic Invariant Symbol Value Token Number Ordinal Metaphor Metafive]
    [RELATABLE  Characteristic Invariant Symbol Value Token Number Ordinal Metaphor Metafive]
    [REPRESENTATIVE Characteristic Invariant Symbol Value Token Representative Number Ordinal (BOOL Bool) Metaphor Metafive]
    -- weird, right?  still have no idea what it is. This isn't cheating though, watch...
    [e: ENCODED Characteristic Invariant Symbol Value Token Representative Number Ordinal Truth  Metaphor Metafive]
    [COMPUTABLE Characteristic Invariant Symbol Value Token Representative Number Ordinal Truth Metaphor Metafive]
    [ENCODABLE Characteristic Invariant Symbol Value Token Representative Number Ordinal Truth Metaphor Metafive]
    [RELATED Characteristic Invariant Symbol Value Token Representative Number Ordinal Truth Metaphor Metafive]
    [BINARY Characteristic Invariant Symbol Value Token Representative Number Ordinal Truth Metaphor Metafive]
    [DECOMPOSABLE Characteristic Invariant Symbol Value Token Representative Number Ordinal Truth Metaphor Metafive]
    [DECOMPOSED Characteristic Invariant Symbol Value Token Representative Number Ordinal Truth Metaphor Metafive]
    [DISTINGUISHED Characteristic Invariant Symbol Value Token Representative Number Ordinal Truth Metaphor Metafive]
    [MEASURED Characteristic Invariant Symbol Value Token Representative Number Ordinal Truth Metaphor Metafive]
    [WRITTEN Characteristic Invariant Symbol Value Token Representative Number Ordinal Truth Metaphor Metafive]
    [carrier: OBSERVED_CARRIER Characteristic Invariant Symbol Value Token Representative Number Ordinal Truth Metaphor Metafive]
      where
  value: GAUGE Invariant Symbol (TOKEN (Symbol × Value))
  token: READING Symbol Invariant (TOKEN (Value × Symbol))
  representative: BIT Symbol Invariant (TOKEN (Symbol × Value))
  correlant: carrier.token Symbol Invariant (TOKEN (Value × Symbol))
end Measurement
