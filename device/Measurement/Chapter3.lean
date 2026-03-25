import Measurement.Chapter2

namespace Measurement

abbrev GAUGE (Symbol : Type)(Value: Type)(Reading : Type 1)   := ((TOKEN Symbol) × TOKEN Value)×(TOKEN Reading)

class MEASURED
    (Characteristic   : Type → TOKEN Type)
    (Invariant        : Type)
    (Symbol           : Type)
    (Value            : Type 1)
    (Token            : Type 1)
    (Representative   : Prop)
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
    -- Finally, the extension cord is long enough.
    [r: REPRESENTATIVE Characteristic Invariant Symbol Value Token Representative Number Ordinal (BOOL Bool) Metaphor Metafive]
    -- weird, right?  still have no idea what it is. This isn't cheating though, watch...
    [e: ENCODED Characteristic Invariant Symbol Value Token Representative Number Ordinal Truth  Metaphor Metafive]
    [COMPUTABLE Characteristic Invariant Symbol Value Token Representative Number Ordinal Truth Metaphor Metafive]
    [ENCODABLE Characteristic Invariant Symbol Value Token Representative Number Ordinal Truth Metaphor Metafive]
    [RELATED Characteristic Invariant Symbol Value Token Representative Number Ordinal Truth Metaphor Metafive]
    [BINARY Characteristic Invariant Symbol Value Token Representative Number Ordinal Truth Metaphor Metafive]
    [DECOMPOSABLE Characteristic Invariant Symbol Value Token Representative Number Ordinal Truth Metaphor Metafive]
    [DECOMPOSED Characteristic Invariant Symbol Value Token Representative Number Ordinal Truth Metaphor Metafive]
    [DISTINGUISHED Characteristic Invariant Symbol Value Token Representative Number Ordinal Truth Metaphor Metafive]
      where
  carrier: RELATING Symbol Value
  bit: NAND (ENCODING Symbol) (RELATING Symbol Value) -- You didn't even see the hat this rabbit came out of.
  swap: COMMUTING (ENCODING Symbol) (RELATING Symbol Value)
  decomposition: CHARACTERISTIC (ENCODING Symbol)
  invarant_: Invariant
  symbol_: Symbol
  number : TOKEN Invariant
  ordinal : TOKEN Symbol
  reading? : TOKEN Invariant → EVENT Value
  counted_    : TOKEN Invariant → EVENT Value → BOOL Bool := fun i v => Metaphor i v
  admitted_   : TOKEN Symbol → EVENT Token → BOOL Bool := fun s t => Metafive s t

abbrev READING (Symbol : Type)(Value: Type)(Reading : Type 1) := GAUGE Symbol Value Reading

class READABLE
    (Characteristic   : Type → TOKEN Type)
    (Invariant        : Type)
    (Symbol           : Type)
    (Value            : Type 1)
    (Token            : Type 1)
    (Representative   : Prop)
    (Number           : Type i)
    (Ordinal          : Type (i+1))
    (Truth: BOOL Bool)
    (Metaphor: TOKEN Invariant → EVENT Value  → BOOL Bool)
    (Metafive: TOKEN Symbol → EVENT Token  → BOOL Bool)
    (Metasix:  TOKEN Symbol → EVENT Reading → BOOL Bool)
    [invariant_equality : DecidableEq (Invariant)]
    [symbol_equality : DecidableEq (Symbol)]
    [value_equality : DecidableEq (Value)]
    [token_equality : DecidableEq (Token)]
    [DISTINGUISHABLE Characteristic Invariant]
    [DISTINGUISHABLE Characteristic Symbol]
    [DISTINGUISHABLE (CHARACTERISTIC Symbol \to TOKEN Symbol) Invariant]
    [event: ADMISSIBLE Invariant Value Metaphor]
    [ADMISSIBLE Symbol Token fun _ t => ADMISSIBLE.admissible? Metaphor Number t]
    [ADMISSIBLE Symbol Token Metafive]
    [COUNTABLE  Characteristic Invariant Symbol Value Token Number Metaphor]
    [NUMERIC  Characteristic Invariant Symbol Value Token Number Ordinal Metaphor Metafive]
    [RELATABLE  Characteristic Invariant Symbol Value Token Number Ordinal Metaphor Metafive]
    -- Finally, the extension cord is long enough.
    [r: REPRESENTATIVE Characteristic Invariant Symbol Value Token Representative Number Ordinal (BOOL Bool) Metaphor Metafive]
    -- weird, right?  still have no idea what it is. This isn't cheating though, watch...
    [e: ENCODED Characteristic Invariant Symbol Value Token Representative Number Ordinal Truth  Metaphor Metafive]
    [COMPUTABLE Characteristic Invariant Symbol Value Token Representative Number Ordinal Truth Metaphor Metafive]
    [ENCODABLE Characteristic Invariant Symbol Value Token Representative Number Ordinal Truth Metaphor Metafive]
    [RELATED Characteristic Invariant Symbol Value Token Representative Number Ordinal Truth Metaphor Metafive]
    [BINARY Characteristic Invariant Symbol Value Token Representative Number Ordinal Truth Metaphor Metafive]
    [DECOMPOSABLE Characteristic Invariant Symbol Value Token Representative Number Ordinal Truth Metaphor Metafive]
    [DECOMPOSED Characteristic Invariant Symbol Value Token Representative Number Ordinal Truth Metaphor Metafive]
    [DISTINGUISHED Characteristic Invariant Symbol Value Token Representative Number Ordinal Truth Metaphor Metafive]
    [m: MEASURED Characteristic Invariant Symbol Value Token Representative Number Ordinal Truth Metaphor Metafive]
      where
  carrier: RELATING Symbol Value
  bit: NAND (ENCODING Symbol) (RELATING Symbol Value) -- You didn't even see the hat this rabbit came out of.
  swap: COMMUTING (ENCODING Symbol) (RELATING Symbol Value)
  decomposition: CHARACTERISTIC (ENCODING Symbol)
  invarant_: Invariant
  symbol_: Symbol
  number : TOKEN Invariant
  ordinal : TOKEN Symbol
  reading? : m.reading
  counted_    : TOKEN Invariant → EVENT Value → BOOL Bool := fun i v => Metaphor i v
  admitted_   : TOKEN Symbol → EVENT Token → BOOL Bool := fun s t => Metafive s t

abbrev BIT (Symbol : Type)(Value: Type)(Reading : Type 1) := READING Symbol Value Reading

class OBSERVED_CARRIER
    (Characteristic   : Type → TOKEN Type)
    (Invariant        : Type)
    (Symbol           : Type)
    (Value            : Type 1)
    (Token            : Type 1)
    (Representative   : Prop)
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
      where
  carrier: Invariant
  symbol: Symbol
  value: Value
  token: Token
  representative: BIT Symbol Invariant (TOKEN (Symbol × Value))

  observed? : TOKEN Invariant → TOKEN Symbol → TOKEN Value → BOOL Bool :=
    fun i s v => token_equality i s




end Measurement
