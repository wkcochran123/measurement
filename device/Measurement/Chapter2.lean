/-
Measurement/Chapter2.lean
-/

import Measurement.Chapter1

namespace Measurement


abbrev ENCODING (Symbol: Type) := (Symbol×TOKEN Symbol)

class ENCODABLE
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
      where
  carrier: Symbol
  invariant: Value
  symbol: TOKEN Invariant
  value: TOKEN Symbol
  number: ENCODING Symbol

abbrev RELATING (Symbol : Type) (Value : Type 1) := (Value → Symbol → Bool)

class RELATED
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
      where
  carrier: Value
  invariant: TOKEN Invariant
  symbol: TOKEN Symbol
  value: ENCODING Symbol
  number: RELATING Symbol Value

abbrev NAND (Symbol : Type) (Value : Type 1) := (Value × Symbol)

class BINARY
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
    [ENCODED Characteristic Invariant Symbol Value Token Representative Number Ordinal Truth  Metaphor Metafive]
    [COMPUTABLE Characteristic Invariant Symbol Value Token Representative Number Ordinal Truth Metaphor Metafive]
    [ENCODABLE Characteristic Invariant Symbol Value Token Representative Number Ordinal Truth Metaphor Metafive]
    [RELATED Characteristic Invariant Symbol Value Token Representative Number Ordinal Truth Metaphor Metafive]
      where
  carrier: TOKEN Invariant
  invariant: TOKEN Symbol
  symbol: ENCODING Symbol
  value: RELATING Symbol Value
  bit: NAND (ENCODING Symbol) (RELATING Symbol Value) -- You didn't even see the hat this rabbit came out of.

abbrev COMMUTING (Symbol : Type) (Value : Type 1) := (Symbol × Value)

class DECOMPOSABLE
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
    [ENCODED Characteristic Invariant Symbol Value Token Representative Number Ordinal Truth  Metaphor Metafive]
    [COMPUTABLE Characteristic Invariant Symbol Value Token Representative Number Ordinal Truth Metaphor Metafive]
    [ENCODABLE Characteristic Invariant Symbol Value Token Representative Number Ordinal Truth Metaphor Metafive]
    [RELATED Characteristic Invariant Symbol Value Token Representative Number Ordinal Truth Metaphor Metafive]
    [BINARY Characteristic Invariant Symbol Value Token Representative Number Ordinal Truth Metaphor Metafive]
      where
  carrier: TOKEN Symbol
  symbol: ENCODING Symbol  -- Figured that mystery out.
  value: RELATING Symbol Value
  bit: NAND (ENCODING Symbol) (RELATING Symbol Value) -- You didn't even see the hat this rabbit came out of.
  swap: COMMUTING (ENCODING Symbol) (RELATING Symbol Value)

abbrev CHARACTERISTIC (Symbol : Type) := TOKEN Symbol

class DECOMPOSED
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
      where
  carrier: ENCODING Symbol
  value: RELATING Symbol Value
  bit: NAND (ENCODING Symbol) (RELATING Symbol Value) -- You didn't even see the hat this rabbit came out of.
  swap: COMMUTING (ENCODING Symbol) (RELATING Symbol Value)
  decomposition: CHARACTERISTIC (ENCODING Symbol)
  invariant_: Invariant
  symbol_ : Symbol

-- The hat:
abbrev DISTINCT (Symbol : Type) (Value : Type 1) := (COMMUTING (ENCODING Symbol) (RELATING Symbol Value))

class DISTINGUISHED
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
      where
  carrier: RELATING Symbol Value
  bit: NAND (ENCODING Symbol) (RELATING Symbol Value) -- You didn't even see the hat this rabbit came out of.
  swap: COMMUTING (ENCODING Symbol) (RELATING Symbol Value)
  decomposition: CHARACTERISTIC (ENCODING Symbol)
  invarant_: Invariant
  symbol_: Symbol
  token_: TOKEN Invariant
  ordinal_ : TOKEN Symbol


class ADMITTED
    (Characteristic   : Type → TOKEN Type)
    (Encoding         : Type i → TOKEN Type)
    (Input            : Type i)
    (Invariant        : Type)
    (Symbol           : Type)
    (Value            : Type 1)
    (Token            : Type 1)
    (Number           : TOKEN Invariant)
    (Ordinal          : TOKEN Symbol)
    (Metaphor: TOKEN Invariant → EVENT Value  → BOOL Bool)
    (Metafive: TOKEN Symbol → EVENT Token  → BOOL Bool)
    (Truth: BOOL Bool)
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
    -- A TRUTH survives.
    [e: ENCODED Characteristic Invariant Symbol Value Token Representative Number Ordinal TRUTH Metaphor Metafive]
    [COMPUTABLE Characteristic Invariant Symbol Value Token Representative Number Ordinal TRUTH Metaphor Metafive]
    [ENCODABLE Characteristic Invariant Symbol Value Token Representative Number Ordinal TRUTH Metaphor Metafive]
    [RELATED Characteristic Invariant Symbol Value Token Representative Number Ordinal TRUTH Metaphor Metafive]
    [BINARY Characteristic Invariant Symbol Value Token Representative Number Ordinal TRUTH Metaphor Metafive]
    [DECOMPOSABLE Characteristic Invariant Symbol Value Token Representative Number Ordinal TRUTH Metaphor Metafive]
    [DECOMPOSED Characteristic Invariant Symbol Value Token Representative Number Ordinal TRUTH Metaphor Metafive]
    [DISTINGUISHED Characteristic Invariant Symbol Value Token Representative Number Ordinal TRUTH Metaphor Metafive]
      where
  carrier: RELATING Symbol Value
  bit: NAND (ENCODING Symbol) (RELATING Symbol Value) -- You didn't even see the hat this rabbit came out of.
  swap: COMMUTING (ENCODING Symbol) (RELATING Symbol Value)
  decomposition: CHARACTERISTIC (ENCODING Symbol)
  invarant_: Invariant
  symbol_: Symbol
  token_: TOKEN Invariant
  ordinal_ : TOKEN Symbol
  glyph : DISTINGUISHABLE Characteristic Invariant

inductive Alphabet
    (Characteristic   : Type → TOKEN Type)
    (Encoding         : Type i → TOKEN Type)
    (Input            : Type i)
    (Invariant        : Type)
    (Symbol           : Type)
    (Value            : Type 1)
    (Token            : Type 1)
    (Number           : TOKEN Invariant)
    (Ordinal          : TOKEN Symbol)
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
    [e: ENCODED Characteristic Invariant Symbol Value Token Representative Number Ordinal Truth  Metaphor Metafive]
    [COMPUTABLE Characteristic Invariant Symbol Value Token Representative Number Ordinal Truth Metaphor Metafive]
    [ENCODABLE Characteristic Invariant Symbol Value Token Representative Number Ordinal Truth Metaphor Metafive]
    [RELATED Characteristic Invariant Symbol Value Token Representative Number Ordinal Truth Metaphor Metafive]
    [BINARY Characteristic Invariant Symbol Value Token Representative Number Ordinal Truth Metaphor Metafive]
    [DECOMPOSABLE Characteristic Invariant Symbol Value Token Representative Number Ordinal Truth Metaphor Metafive]
    [DECOMPOSED Characteristic Invariant Symbol Value Token Representative Number Ordinal Truth Metaphor Metafive]
    [DISTINGUISHED Characteristic Invariant Symbol Value Token Representative Number Ordinal Truth Metaphor Metafive]
    [concept: ADMITTED Characteristic Encoding Input Invariant Symbol Value Token Number Ordinal Metaphor Metafive]
  | nil : Alphabet Characteristic Encoding Input Invariant Symbol Value Token Representative Number Ordinal Truth Metaphor Metafive

end Measurement
