import Measurement.Formalization.Grammar

set_option autoImplicit false

/-!
# LocalGibberish

A deliberately silly story can still pass through the device when the only
claim is local coherence. The tokens below are not measurements, not physical
names, and not semantic claims. They are marks with a declared local read into
the serial grammar.

This file underlines a narrow point used throughout the books: a finite device
can check whether each neighboring move is licensed without granting the whole
string a global interpretation. Local sense is a relation supplied by the
apparatus; global sense is extra data, and here it is intentionally absent.
-/

namespace Measurement.LocalGibberish

open Measurement.Formalization

/-! ## Raw nonsensical marks -/

/-- Tokens with no built-in meaning. The names are intentionally gibberish. -/
inductive GibToken
  | zorp
  | quiv
  | nalm
  | brint
  | xov
  | plim
deriving DecidableEq, Repr

/-- The absolute-gibberish surface story. -/
def story : List GibToken :=
  [.zorp, .quiv, .nalm, .brint, .xov, .plim]

/-! ## A local reading into the serial grammar -/

/-- A local read, supplied by the apparatus, not by the token spellings. -/
def localRead : GibToken -> Stage
  | .zorp  => .fact
  | .quiv  => .distinguishable
  | .nalm  => .admissible
  | .brint => .countable
  | .xov   => .encoded
  | .plim  => .residue

/-- A neighboring pair makes local sense exactly when the serial grammar steps. -/
def locallySteps (a b : GibToken) : Prop :=
  Step (localRead a) (localRead b)

/-- Recursive local coherence: every adjacent pair is licensed. -/
def LocallyCoherent : List GibToken -> Prop
  | [] => True
  | [_] => True
  | a :: b :: rest => locallySteps a b /\ LocallyCoherent (b :: rest)

/-- The gibberish story is locally coherent under the declared read. -/
theorem story_locally_coherent : LocallyCoherent story := by
  repeat constructor <;> rfl

/-! ## No global interpretation is smuggled in -/

/-- A tiny menu of global readings one might try to claim. -/
inductive GlobalClaim
  | physicalMeasurement
  | truth
  | compiledResult
deriving DecidableEq, Repr

/-- No global claim is supplied for the gibberish story. -/
def globalClaim (_ : List GibToken) : Option GlobalClaim :=
  none

/-- Passing the local grammar does not create a global interpretation. -/
theorem story_has_no_global_claim :
    globalClaim story = none := rfl

/-- The combined receipt: local sense is present; global sense is absent. -/
theorem story_is_only_locally_sensible :
    LocallyCoherent story /\ globalClaim story = none :=
  ⟨story_locally_coherent, story_has_no_global_claim⟩

/-! ## The spellings are irrelevant to the local check -/

/-- A second nonsense story with different spellings but the same local read. -/
inductive OtherToken
  | blaf
  | snerk
  | vodd
  | tessel
  | murn
  | keek
deriving DecidableEq, Repr

def otherStory : List OtherToken :=
  [.blaf, .snerk, .vodd, .tessel, .murn, .keek]

def otherLocalRead : OtherToken -> Stage
  | .blaf   => .fact
  | .snerk  => .distinguishable
  | .vodd   => .admissible
  | .tessel => .countable
  | .murn   => .encoded
  | .keek   => .residue

def OtherLocallyCoherent : List OtherToken -> Prop
  | [] => True
  | [_] => True
  | a :: b :: rest =>
      Step (otherLocalRead a) (otherLocalRead b) /\
        OtherLocallyCoherent (b :: rest)

theorem other_story_locally_coherent :
    OtherLocallyCoherent otherStory := by
  repeat constructor <;> rfl

/--
Two different nonsense surfaces can carry the same local receipt. What matters
to this check is the declared adjacency through the grammar, not the English
or non-English story one tells on top of it.
-/
theorem two_gibberish_surfaces_same_local_receipt :
    LocallyCoherent story /\ OtherLocallyCoherent otherStory :=
  ⟨story_locally_coherent, other_story_locally_coherent⟩

end Measurement.LocalGibberish
