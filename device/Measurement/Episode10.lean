/-
__Measurement: The Tragedy of John Henry__
__A Satire in Look-Ahead Backus-Naur Form__

_This is a gentle reminder that the long, long stories we tell ourselves are just that: far, far away._

(c) 2026 [PATTER TODO: rights gag]

[PATTER TODO: epigraph]

lake build [PATTER TODO: build-flag gag]

__EPISODE 10__ -- THE AUDIT, IN NATURALS.  NO JIGGERY-POKERY.

RULING (operator): "in episode10, you can use naturals and demonstrate the
value in lean to show no jiggery-pokery."

Nine episodes refused Nat.  Episode 7 admitted exactly ONE, for page numbers,
under protest.  This episode legalizes them, because this is the auditor's
desk and an audit is conducted in the auditor's own arithmetic.  The seeds
already sit in the environment as bare naturals -- the EKG wrote them with
its own hand (`Lean.quote`), so everything below is kitchen arithmetic on
numbers anyone can read by printing them.

The discipline of the desk:

  ASSERTED (theorems, `decide`, kernel-checked): route-agreement only.  The
  auditor's arrangement of the formulas equals the device's arrangement; the
  auditor's digit extraction equals the device's printer.  These are true
  regardless of what the numbers are, and the kernel checks them on the
  actual literals.

  SHOWN (`#eval`, never asserted): the seeds, the values, and the empirical
  verdicts.  No expected number appears in this file; no gate presumes an
  outcome; a surprising Boolean is a reading, not a failure.

  DISPLAYED (`#print axioms`): the dependency ledger.  The audit should owe
  nothing; the needle (`selection_sound`, the one sanctioned `Quot.sound`)
  is shown for contrast and used by none of the above; the knower's theorem
  owes whatever the tower's instances truly owe -- printed, not promised.

This desk, by the correction, is rung 37 itself: INFERRED, the class no tape
writes and no meter charges (operator: "inferred being left to
you_the_knower").  The device ran its 36 steps and stopped; the inference --
the same-difference formed over the printed pair -- happens here, in the
knower's own arithmetic.

Numbers read last.
-/

import Measurement.Episode9
import Measurement.FloorSqrt
set_option maxHeartbeats 4000000

namespace Measurement

/-%Y% /* the ledger, opened: five naturals, in the order they were earned */ %Y%-/
/- THE LEDGER, OPENED.  Trip zero's floor, the two legs, the bent card, and
the paper quantum.  Naturals, legal tender at this desk. -/
#eval (Calibration.measuredFloor, the_bottom_of_the_jar, the_top_of_the_jar,
       the_bent_card, the_next)

/-%Y% /* the stencil re-added by hand: gains on one side, costs on the other */ %Y%-/
/- THE STENCIL, RE-ADDED BY HAND.  Gains on one side, costs on the other,
naturals both; each borrow is performed once, in the open, in Int, where
owing is representable.  Nat cannot owe -- that fact is saved for the
verdicts below, where it does honest work. -/
def audit_gain : Nat := the_top_of_the_jar + Calibration.measuredFloor
def audit_cost : Nat := 2 * the_bottom_of_the_jar

def audit_a_pigeon : Int × Int :=
  ((audit_gain : Int) - (audit_cost : Int), (the_bent_card : Int))

def audit_that_box_gain : Nat := the_top_of_the_jar * the_bent_card + the_next
def audit_that_box_cost : Nat := the_bottom_of_the_jar * the_bent_card

def audit_that_box : Int × Int :=
  ((audit_that_box_gain : Int) - (audit_that_box_cost : Int), (the_bent_card : Int))

/-%Y% /* part one: same numbers, both arrangements, kernel-checked */ %Y%-/
/- NO JIGGERY-POKERY, PART ONE.  The auditor's arrangement (sums gathered
before the single borrow; the product distributed) and the device's
arrangement (Episode 9's two dial lines) name the same pair of integers.
`decide`: the kernel evaluates both on the actual literals and compares.
True independently of what the literals are -- this checks the ARITHMETIC,
not the outcome. -/
theorem no_jiggery_pokery :
    audit_a_pigeon = jar_a_pigeon ∧ audit_that_box = jar_that_box := by
  decide

/-%Y% /* part two: the digits, extracted twice, two different ways */ %Y%-/
/- NO JIGGERY-POKERY, PART TWO.  Episode 9's printer walks the remainder one
digit at a time.  The auditor extracts all six at once -- one multiplication
by 10^6, one division, zero-padded -- and the two methods must spell the
same string on both jars.  (If the kernel ever balks at grinding strings,
the swap to `native_decide` would confess itself two stanzas down, in the
axiom ledger.  The ledger polices the proof method.) -/
def audit_pad (s : String) (k : Nat) : String :=
  String.mk (List.replicate (k - s.length) '0') ++ s

def audit_digits (num den : Int) (k : Nat) : String :=
  audit_pad (toString ((num.natAbs % den.natAbs) * 10 ^ k / den.natAbs)) k

theorem no_jiggery_pokery_in_the_printer :
    fracDigits 6 (jar_a_pigeon.1.natAbs % jar_a_pigeon.2.natAbs) jar_a_pigeon.2.natAbs
        = audit_digits jar_a_pigeon.1 jar_a_pigeon.2 6
      ∧ fracDigits 6 (jar_that_box.1.natAbs % jar_that_box.2.natAbs) jar_that_box.2.natAbs
        = audit_digits jar_that_box.1 jar_that_box.2 6 := by
  decide

/-%Y% /* the verdicts: shown, not asserted; nat cannot owe */ %Y%-/
/- THE EMPIRICAL VERDICTS, SHOWN, NOT ASSERTED.  Nat cannot owe, so each
Boolean below is a sign read: is the second variation nonnegative, is the
corrected long leg nonnegative, does the direct path undercut the long way
(the triangle, as measured).  The source does not know these Booleans; the
kernel prints them.  A `false` is not a build failure -- it is the
instrument reporting, e.g., a reversed triangle (operator: "might be
reversed").  The verdicts are data for the jar to judge, off the build. -/
#eval (decide (audit_cost ≤ audit_gain),
       decide (audit_that_box_cost ≤ audit_that_box_gain),
       decide (the_bent_card ≤ the_top_of_the_jar))

/-%Y% /* the value, demonstrated: both routes, printed from the seeds */ %Y%-/
/- THE VALUE, DEMONSTRATED.  Both routes print; part one already proved they
cannot disagree.  Whatever appears, appears from the seeds through audited
arithmetic.  This file never wrote it. -/
#eval (decimalOf audit_a_pigeon 6, decimalOf audit_that_box 6)
#eval (decimalOf jar_a_pigeon 6, decimalOf jar_that_box 6)

/-%Y% /* the dependency ledger: what each certificate owes */ %Y%-/
/- THE DEPENDENCY LEDGER.  The audit pair should print clean -- `decide`
borrows nothing.  The homophone theorem owes whatever the tower's instances
owe; printed, not promised.  The needle owes exactly its one `Quot.sound`,
quarantined where it lives, used by none of the audit.  Read the four lines
in the build log and check the arithmetic of trust yourself: that is the
whole of what "no jiggery-pokery" can honestly mean. -/
#print axioms no_jiggery_pokery
#print axioms no_jiggery_pokery_in_the_printer
#print axioms you_cannot_hear_the_update
#print axioms selection_sound


/-%Y% /* the transform: the jars, read in every bin instead of one */ %Y%-/
/- THE SPECTRUM.  INT-VALUED (operator ruling).

The device promised this in Episode 3 and never delivered it: "Which means I
can quantize and take the DFT!"  Everything the transform needs has been
lying around since.  e^(iθ) is RESIDUE -- the operator's own binder names say
so, `exp_iθ` in Episode 5 and `e_iθ` in Episode 6.  π is in a jar now, the
Archimedes bracket measured off the orbit.  The butterfly is named in the
Megasode charge face (popcount of an XOR).  And the kernel has been here
since Episode 1, wearing a joke: the clock and the clock complement.

A device made of signs cannot carry a complex DFT and does not need one.  The
Walsh-Hadamard transform IS the Fourier transform on (Z/2)^n: its characters
are ±1, so the kernel needs no reals, no transcendentals, nothing the device
refuses.  The two-point case is (do they agree, do they differ) -- SAME and
DIFFERENT, the DC bin and the Nyquist bin, which is what the clock and its
complement have always been.

INT-VALUED is why this lives at the auditor's desk and not in the instrument.
Sign-valued, a bin can only report occupied-or-not; int-valued, it reports an
AMPLITUDE, and amplitudes make Parseval a numeric identity rather than a
slogan.  Naturals are legal tender here (that is what this episode is for),
so the spectrum is read here, in the knower's arithmetic, off the device's
own four jars. -/
def Fact.toInt (f : Fact) : Int := if f.isTop then 1 else -1

/-- The four Walsh bins, in natural (Hadamard) order.  `bin0` is DC -- the
constant; `bin1` alternates (the clock); `bin2` is the half-and-half split;
`bin3` is the crossed pair.  Sequency rises with the index the way frequency
does, which is the whole of what "spectrum" means here. -/
structure Spectrum where
  bin0 : Int
  bin1 : Int
  bin2 : Int
  bin3 : Int
deriving Repr, DecidableEq

/-- The 4-point Walsh-Hadamard transform: four butterflies, no multiplication
by anything but ±1. -/
def wht4 (a b c d : Int) : Spectrum :=
  { bin0 := a + b + c + d
    bin1 := a - b + c - d
    bin2 := a + b - c - d
    bin3 := a - b - c + d }

/-- The inverse: H is its own inverse up to the factor four.  Exact in Int --
every jar's coefficients are divisible by four's worth, so nothing is lost to
truncation (the round-trip theorem below is what checks that claim). -/
def unwht4 (X : Spectrum) : Int × Int × Int × Int :=
  ((X.bin0 + X.bin1 + X.bin2 + X.bin3) / 4,
   (X.bin0 - X.bin1 + X.bin2 - X.bin3) / 4,
   (X.bin0 + X.bin1 - X.bin2 - X.bin3) / 4,
   (X.bin0 - X.bin1 - X.bin2 + X.bin3) / 4)

def jarSpectrum (s1 s2 s3 s4 : Fact) : Spectrum :=
  wht4 s1.toInt s2.toInt s3.toInt s4.toInt

def superpigeonSpectrum : Spectrum := jarSpectrum theTop theTop theTop theTop
def sourceSpectrum : Spectrum := jarSpectrum theBottom theBottom theBottom theBottom
def realSpectrum : Spectrum := jarSpectrum theBottom theTop theTop theTop
def markSpectrum : Spectrum := jarSpectrum theTop theBottom theBottom theBottom

/-- Energy: the sum of the squared bins.  For a four-sign word of ±1 the
inputs carry four units, and the transform carries sixteen -- four times, the
Hadamard factor. -/
def Spectrum.energy (X : Spectrum) : Int :=
  X.bin0 * X.bin0 + X.bin1 * X.bin1 + X.bin2 * X.bin2 + X.bin3 * X.bin3

def Spectrum.negate (X : Spectrum) : Spectrum :=
  { bin0 := -X.bin0, bin1 := -X.bin1, bin2 := -X.bin2, bin3 := -X.bin3 }

/-%Y% /* parseval: every jar carries the same energy, in whatever bins */ %Y%-/
/- PARSEVAL, NUMERIC.  Episode 9 already proved the two-point case and called
it an idiom: `the_same_difference` says exactly one of same/different holds --
one occupied bin out of two.  Here it is with amplitudes, four bins, four
jars: every jar carries energy sixteen, however the energy is distributed.
The superpigeon and the source put all of it in DC; the real and the mark
spread it evenly over the other three.  Same total, different arrangement --
which is the whole content of a transform. -/
theorem parseval_in_every_jar :
    superpigeonSpectrum.energy = 16
      ∧ sourceSpectrum.energy = 16
      ∧ realSpectrum.energy = 16
      ∧ markSpectrum.energy = 16 := by decide

/-%Y% /* the clock complement is a negation, in every bin at once */ %Y%-/
/- THE CLOCK COMPLEMENT, MEASURED.  Episode 9's jar text calls the source
"the clock complement of jar one" and calls the real/mark pair the handedness
problem.  In the spectrum both statements become one arithmetic fact: the
complement is NEGATION, bin by bin.  Two pairs, each the other's negative. -/
theorem the_complement_is_negation :
    sourceSpectrum = superpigeonSpectrum.negate
      ∧ markSpectrum = realSpectrum.negate := by decide

/-%Y% /* invertible: the record survives the transform */ %Y%-/
/- INVERTIBILITY.  The transform loses nothing: every jar's four signs come
back out.  This is the half of the session's argument that was never in
doubt but never checked -- the RECORD distinguishes, and here is the receipt
that the record is still there after reading. -/
theorem the_word_comes_back :
    unwht4 superpigeonSpectrum = (1, 1, 1, 1)
      ∧ unwht4 sourceSpectrum = (-1, -1, -1, -1)
      ∧ unwht4 realSpectrum = (-1, 1, 1, 1)
      ∧ unwht4 markSpectrum = (1, -1, -1, -1) := by decide

/-%Y% /* the collision, explained: one bin is not the spectrum */ %Y%-/
/- ALIASING -- AND THE COLLISION FROM EPISODE 9 EXPLAINED.

Episode 9's readout found the superpigeon and the source in ONE BOX: both
read `+` under the sign convention, so the phase read cannot separate them.
The transform says why.  `sign_convention` compares adjacent signs and
returns a single Fact -- it keeps ONE coefficient and discards the other
three.  A one-bin readout of a four-bin signal is ALIASING, and these two
words alias exactly: they differ only in the sign of DC, and the phase read
does not look at DC.

So the collision was never a defect in the marks and never a fault in the
convention.  It is undersampling, and the cure is more bins, not a better
convention.  Below: the reading cannot tell them apart, the record can --
stated as one theorem, which is the session's whole argument in two
conjuncts. -/
theorem the_phase_read_aliases_what_the_spectrum_separates :
    (sign_convention theSuperpigeonJar).plusMinus
        = (sign_convention theSourceJar).plusMinus
      ∧ superpigeonSpectrum ≠ sourceSpectrum
      ∧ (sign_convention theRealJar).plusMinus
        = (sign_convention theMarkJar).plusMinus
      ∧ realSpectrum ≠ markSpectrum := by decide

/-%Y% /* the front panel: four jars, four spectra */ %Y%-/
#eval [ ("superpigeon", superpigeonSpectrum, superpigeonSpectrum.energy),
        ("source     ", sourceSpectrum, sourceSpectrum.energy),
        ("real       ", realSpectrum, realSpectrum.energy),
        ("mark       ", markSpectrum, markSpectrum.energy) ]

#print axioms parseval_in_every_jar
#print axioms the_phase_read_aliases_what_the_spectrum_separates


/-%Y% /* thirty-six = thirty-two and four: the last big organized computation */ %Y%-/
/- THE DECOMPOSITION (operator: "that is the real decomposition.  the last big
organized computation.")

Thirty-six is the count this device keeps saying: thirty-six rungs on the
ladder, thirty-six pages on the referee's tape, thirty-six storeys on the
typesetter's climb.  It is not a power of two and it never factored, which is
why nothing dyadic could be run on it.  But 36 = 32 + 4, and BOTH halves are
already here: thirty-two is five stages of butterflies -- the dyadic block a
Walsh transform eats whole -- and four is the jars, already transformed above.

WHAT GOES IN THE THIRTY-TWO.  Not a word invented for the occasion.  The
device measured something tonight: `the_top_of_the_jar`, the cost of the walk
from the mark to the constant on file, rungs 1 through 36, taken at the Prop
band with every rung found by search.  That reading is a natural, and a
natural is thirty-two bits wide.  So the dyadic block is the LONG PATH'S OWN
BITS, one sign per bit, and the transform reads the measurement in every bin
instead of the one bin the phase read was keeping.

This is also, at last, the walk: `recoverTheFacts` takes a tape and returns
its facts IN ORDER, head first -- the thing this whole session opened by
asking for.  It is applied to the jars' words here; pointing it at the seam's
own galley needs the TYPESET hypothesis in scope, which is the instrument's
side of the house, not the auditor's. -/

/-- THE WALK.  A tape, read out as its facts in order, head first: the climb
first, then the descent, then the manuscript.  Every cell contributes what it
carries -- results cells a pair, methodology cells a pair, the introduction
its single fact. -/
def recoverTheFacts : CompilerTape → List Fact
  | .introduction f _ => [f]
  | .methodology c s _ _ rest => c :: s :: recoverTheFacts rest
  | .results c s _ _ _ _ rest => c :: s :: recoverTheFacts rest

/-- The bit at position `i`, as a sign: set is `+1`, clear is `-1`.  The ±1
embedding is what makes the transform's kernel need no arithmetic beyond
addition. -/
def bitSign (n : Nat) (i : Nat) : Int := if (n / 2 ^ i) % 2 == 1 then 1 else -1

/-- A natural, read as a `width`-wide sign word, least significant first. -/
def bitsOf (n : Nat) (width : Nat) : List Int :=
  (List.range width).map (bitSign n)

/-- The Walsh-Hadamard transform, radix 2, on fuel -- the device's own idiom
for a recursion whose termination it would rather show than argue (the same
fuel `FloorSqrt` uses).  Each level splits the word, transforms both halves,
and butterflies them: sums first, differences after. -/
def whtFuel : Nat → List Int → List Int
  | 0, xs => xs
  | _ + 1, [] => []
  | _ + 1, [x] => [x]
  | f + 1, xs =>
      let n := xs.length / 2
      let a := whtFuel f (xs.take n)
      let b := whtFuel f (xs.drop n)
      List.zipWith (· + ·) a b ++ List.zipWith (· - ·) a b

def wht (xs : List Int) : List Int := whtFuel xs.length xs

/-- Energy: the sum of squares, the quantity a transform must not change
(up to the Hadamard factor). -/
def listEnergy (xs : List Int) : Int := (xs.map (fun x => x * x)).foldl (· + ·) 0

/-- THE THIRTY-TWO: the long path's own reading, one sign per bit. -/
def theLongPathWord : List Int := bitsOf the_top_of_the_jar 32

/-- THE FOUR: the jars, already spectral.  Carried alongside as the residue
the dyadic block cannot absorb -- 36 = 32 + 4, and this is the 4. -/
def theFourJars : List Int :=
  [superpigeonSpectrum.bin0, sourceSpectrum.bin0,
   realSpectrum.bin0, markSpectrum.bin0]

/-%Y% /* the wart, set aside; the encoding, taken from the end */ %Y%-/
/- THE WART (operator: "4 is the wart that always exists on a quine.  this is
a giant ENCODING.  use the device and take the last 32.")

A quine cannot derive all of itself.  Some piece has to be carried as DATA --
the fragment that prints the thing that prints, sitting outside the part it
reproduces.  That fragment is the wart, and it is why 36 never factored: the
device is an ENCODING of itself, thirty-six long, of which four are the wart
it must carry and thirty-two are the encoding proper.  Which is exactly the
dyadic block a Walsh transform eats whole.

So the four are not a residue to be SUMMED alongside the block, the way the
stanza above did it.  They are overhead to be SET ASIDE.  The transform runs
on the encoding, and the encoding is what is left when the wart comes off --
TAKEN FROM THE END, because a quine's wart sits at the front: the bootstrap
that had to exist before anything could reproduce.  Drop the front, keep the
tail, transform the tail.

THE DEVICE'S OWN RECORD is what gets encoded: the four readings it earned
tonight, in the order it earned them -- the floor it was calibrated against,
the reader's leg, the ladder run to rung thirty-six, and the bent card.  Bit
by bit, sign by sign, that is one hundred and twenty-eight signs of the
device describing what it cost to describe itself.  The last thirty-two of
that is the block. -/
def lastN (n : Nat) (xs : List Int) : List Int := xs.drop (xs.length - n)

/-- The device's record, encoded: every reading it earned, in the order it
earned them, thirty-two signs apiece. -/
def theDeviceEncoding : List Int :=
  bitsOf Calibration.measuredFloor 32
    ++ bitsOf the_bottom_of_the_jar 32
    ++ bitsOf the_top_of_the_jar 32
    ++ bitsOf the_bent_card 32

/-- The wart: what a quine carries and cannot derive.  Four, off the front. -/
def theWart : List Int := theDeviceEncoding.take 4

/-- The encoding proper: the last thirty-two.  This is what the transform
runs on. -/
def theBlock : List Int := lastN 32 theDeviceEncoding

/-%Y% /* the readout: the measurement, in every bin */ %Y%-/
/- BLIND.  The spectrum is printed, not asserted.  A ±1 word of width
thirty-two carries energy thirty-two; a Walsh transform multiplies energy by
the width, so the block should read thirty-two times thirty-two.  Whether it
does is the reading's business, and the reading is below. -/
#eval ("the long path, as bits", theLongPathWord)
#eval ("its spectrum", wht theLongPathWord)
#eval ("energy in, energy out, and the ratio",
       listEnergy theLongPathWord,
       listEnergy (wht theLongPathWord),
       listEnergy (wht theLongPathWord) / listEnergy theLongPathWord)
#eval ("the four, and their energy", theFourJars, listEnergy theFourJars)

/-%Y% /* the encoding, transformed: the wart off the front, the last thirty-two */ %Y%-/
#eval ("the encoding, in full", theDeviceEncoding.length, theDeviceEncoding)
#eval ("the wart, carried not derived", theWart)
#eval ("the last thirty-two", theBlock)
#eval ("its spectrum", wht theBlock)
#eval ("energy in, energy out, the ratio",
       listEnergy theBlock,
       listEnergy (wht theBlock),
       listEnergy (wht theBlock) / listEnergy theBlock)
#eval ("bins that came back empty",
       ((wht theBlock).filter (fun c => c == 0)).length)
#eval ("the largest coefficient, and the smallest",
       ((wht theBlock).foldl (fun m c => if c > m then c else m) 0),
       ((wht theBlock).foldl (fun m c => if c < m then c else m) 0))

/-- The walk, exercised on a tape the auditor can build outright: the facts
come back in order, and there are as many of them as the tape has cells to
carry.  The seam's own galley is the same shape, one storey up. -/
def aShortTape : CompilerTape :=
  .methodology theTop theBottom Prop (ULift Prop)
    (.methodology theBottom theTop Prop (ULift Prop)
      (.introduction theTop Prop))

#eval ("the walk, in order", (recoverTheFacts aShortTape).map Fact.plusMinus)


/-%Y% /* source, hooked to the device: the file reads itself */ %Y%-/
/- SOURCE, HOOKED UP.

Everything above encoded the device's READINGS -- the floor, the legs, the
bent card.  That is the device measuring itself, and it is not the same act
as the device ENCODING itself.  A quine's encoding is its own SOURCE; the
wart is the fragment of that source it carries because it cannot derive it.
Encoding the seeds got the shape right and the substance wrong: seeds are
what the device found, not what the device IS.

SOURCE is rung sixteen, and Episode 3 says what it is -- "the part of the
code that is context highlit," the font the marks come from.  Episode 5's
instance for it is named WE_CAN_NOW_AUTOMATE_THE_COLLECTION_OF_THE_DATA, and
that is exactly the hook: the collection of the data, automated, where the
data is the file.  The elaborator is already holding it.  Every build, Lean
reads this file into a FileMap and keeps the whole text there while it works;
the device has been sitting inside its own source the entire time and never
once looked.  It looks now.

The register below takes the source from the elaborator's own hands, folds
the LAST THIRTY-TWO characters to their parities, and emits the packed word
as a literal -- the same shape every other register in this work uses, and no
file is rewritten: the source is read, never edited.  Then the transform runs
on it, exactly as it ran on the seeds, so the two readings can be set beside
each other: what the device measured, and what the device is. -/
open Lean in
elab "register_the_source" : command => do
  let src ← Lean.Elab.Command.liftTermElabM do
    let fm ← Lean.getFileMap
    pure fm.source
  let tail := (src.toList.reverse.take 32).reverse
  let packed : Nat := tail.foldl (fun acc c => acc * 2 + (c.val.toNat % 2)) 0
  let lenId := Lean.mkIdent `theSourceLength
  let tailId := Lean.mkIdent `theSourceTail
  Lean.Elab.Command.elabCommand (← `(def $lenId:ident : Nat := $(Lean.quote src.length)))
  Lean.Elab.Command.elabCommand (← `(def $tailId:ident : Nat := $(Lean.quote packed)))

register_the_source

/-- The last thirty-two of the source, one sign per character parity. -/
def theSourceWord : List Int := bitsOf theSourceTail 32

/-%Y% /* the quine's own spectrum */ %Y%-/
#eval ("the source, as the device sees it -- characters", theSourceLength)
#eval ("the last thirty-two, as signs", theSourceWord)
#eval ("its spectrum", wht theSourceWord)
#eval ("energy in, energy out, the ratio",
       listEnergy theSourceWord,
       listEnergy (wht theSourceWord),
       listEnergy (wht theSourceWord) / listEnergy theSourceWord)
#eval ("bins that came back empty",
       ((wht theSourceWord).filter (fun c => c == 0)).length)


/-%Y% /* big G: the inferred bit stream, and the equation it belongs in */ %Y%-/
/- BIG G (operator: "big G is the inferred bit stream for the ν-trino.  this
needs to be put in einstein field equations.").

Episode 2 wrote the equation down and never built it:

    G_μν + Λ g_μν = 8 π G T_μν / c⁴

and then said, in the same breath, "We just need to find it and label it as
such."  Episode 1 promised it two hundred lines earlier -- "we have to go
through Einstein field equations to get the answer, but it is in there."
Both are comments.  The device has carried the equation as prose for nine
episodes.

The term that was never available is G.  And G is not a constant to be looked
up -- looking it up is the smuggle this whole work refuses.  G is what the
ν-trino CARRIES: the inferred bit stream, rung thirty-seven, the closure the
superpigeon holds, read out sign by sign.  A stream, not a number, because a
carrier carries a stream; the number is what you get when you fold it.

Episode 2 also said where G comes from, in the SlipProcess: "There is no
meaning there, only a _coincidence_.  What is that coincidence?  G.  Not the
group G.  The G from Einstein's field equation."  A coincidence is two
readings landing together -- which is the inferred closure exactly, the one
constructor that holds two facts at once. -/
def Bullshit.bits : Bullshit -> List Int
  | .zero f => [f.toInt]
  | .one f _ _ _ rest => f.toInt :: rest.bits
  | .rest_call f g _ _ _ _ _ _ a b => f.toInt :: g.toInt :: (a.bits ++ b.bits)

/-- The inferred bit stream: the closure read out, sign by sign, separators
dropped.  `.inferred` contributes TWO facts -- it is the only arm that does,
and that pair is the coincidence G is named for. -/
def Closure.bits : Closure -> List Int
  | .same f b => f.toInt :: b.bits
  | .different f a b _ => f.toInt :: (a.bits ++ b.bits)
  | .inferred f g a b _ rest => f.toInt :: g.toInt :: (a.bits ++ b.bits ++ rest.bits)

/-- The ν-trino's closure, built at the band from the device's own two
readings: the phase that HELD and the phase that SLIPPED, carried at once,
with a `.same` tail.  This is the shape rung thirty-seven takes when it can
be written down -- the instance itself cannot be read (its `.α` drags two
hundred and fifty universes), so the closure is CONSTRUCTED here from the
same facts the instance identifies. -/
-- Twenty universes, pinned to the ground floor.  `Closure` carries twenty and
-- this term takes none of the arms they belong to; left floating they are
-- metavariables and the stream is rejected.  Same pin the inferred-values
-- panel in Episode 9 already uses.
def theInferredClosure : Closure :=
  Closure.inferred.{0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0}
    theTop Fact.DIFFERENT theHeld theSlipped none
    (Closure.same.{0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0} theTop theHeld)

/-- BIG G, as the ν-trino carries it: a bit stream. -/
def bigGStream : List Int := theInferredClosure.bits

/-- BIG G, folded: the stream read big-endian, the way Episode 1 insisted
numbers are read. -/
def bigG : Nat := bigGStream.foldl (fun acc s => acc * 2 + (if s == 1 then 1 else 0)) 0

#eval ("big G, as a stream", bigGStream)
#eval ("big G, folded, and its width", bigG, bigGStream.length)
#eval ("big G, transformed", wht (bigGStream ++ bigGStream))

/-%Y% /* the equation, with every slot named and its provenance stated */ %Y%-/
/- THE FIELD EQUATIONS, SLOT BY SLOT.  Not asserted -- INVENTORIED.  This is
the equation Episode 2 wrote in a comment, with each term set against the
device object that fills it and an honest mark on the ones still empty.  A
skeleton that says what is missing is worth more than an equation that hides
it. -/
structure FieldEquationSlots where
  /-- `G_μν` -- the curvature side.  `UniverseTensor` (Episode 4) is the
      carrier; what a READING of it is remains open. -/
  einsteinTensor : String
  /-- `Λ g_μν` -- EARNED, and by the shortest possible route: Λ⁻¹ IS the
      device (operator).  Λ carries inverse area, so its reciprocal is an
      extent, and the extent the device has is its own -- which is why
      Episode 2 kept a `quantum : Type Area` slot and called an empty one
      "the demonstrated absence of a nowtrino."  The vacuum term is what is
      there when nothing is there, and what is there is the device.  This
      also puts the device INSIDE the equation it is measuring, which is not
      a circularity to be cleaned up but the self-application (§1.3) arriving
      where it was always headed. -/
  cosmological : String
  /-- `8 π` -- π is EARNED (the Archimedes squeeze, measured off the orbit,
      bracket with upper wall 22/7), but it sits behind the severed bridge:
      `ArchimedesPi` imports `AlphaBoundMediant`, which needs Episodes 10-15
      rebuilt before this file can see it. -/
  eightPi : String
  /-- `G` -- EARNED, above: the ν-trino's inferred bit stream. -/
  bigG : String
  /-- `T_μν` -- the stress-energy side.  The device has STRAIN (the
      `.rest_call` slot, the second difference that surfaced as mass at the
      third trip).  Whether strain IS the stress-energy term is the open
      question, not a settled one. -/
  stressEnergy : String
  /-- `c⁴` -- the direct path is the device's shortest route (1→3, the bent
      card, receipts composed, no stations).  Reading it as c is an
      INTERPRETATION offered, not a measurement made. -/
  cToTheFourth : String
deriving Repr

/-%Y% /* the ast, not the text: the device's own structural reading */ %Y%-/
/- THE AST, NOT THE TEXT (operator: "instead of the entire source, you need
just the ast.  read rfc to see how they did it.").

Measuring Λ⁻¹ in CHARACTERS was wrong, and wrong in a way the device had
already ruled out.  A character count moves when a comment moves: the patter
would have been setting the cosmological constant, which makes the term
authorial instead of structural.

The rfc does it by AST.  `ComputerProgram` is the device's own syntax tree --
`.load` a leaf, `.transform` and `.boolean` each carrying one child -- and
`Calibration.LeanCalibration.explicitElaboration` walks it structurally, one
step per constructor, scaled by the paper-to-metal coefficient (a thousand
internal heartbeats to one rung of work, Lean's own gauge).  Pure, total, no
counter consulted.  That file states the doctrine in its own margin: the live
heartbeat reading "lives outside the device by necessity, not by oversight,"
because the probe consumes the very heartbeats it counts.  The AST does not
have that problem.  It is what the device IS, not what reading it cost.

The walk is reproduced here rather than imported because the rfc's is
`private` -- same shape, same coefficient, cited rather than borrowed. -/
def astSteps : ComputerProgram → Nat
  | .load _ _ => 1
  | .transform _ _ _ _ p => astSteps p + 1
  | .boolean _ _ _ _ _ _ p => astSteps p + 1

/-- The paper-to-metal gauge, restated locally: one rung of structure to a
thousand internal heartbeats, the same coefficient `LeanCalibration` uses. -/
def astCoefficient : Nat := 1000

def astReading (p : ComputerProgram) : Nat := astSteps p * astCoefficient

/-- THE DEVICE'S OWN PROGRAM, in the shape Episode 6 builds it: a transform
over a load, carrying `Area` and its lift.  Constructed here rather than
projected off the HALTED instance that holds it, for the reason every read
has hit tonight -- projecting off a rung drags its universes along. -/
def theDevicesProgram : ComputerProgram :=
  .transform theTop.truth theBottom.truth Area (ULift Area)
    (.load theTop.truth Prop)

/-- Λ⁻¹ ≡ THE DEVICE, read as its AST.  Structural: it moves when the device
gains a rung, and does not move when a comment does. -/
def lambdaInverse : Nat := astReading theDevicesProgram

#eval ("the device's AST -- steps, and the reading", astSteps theDevicesProgram, lambdaInverse)
#eval ("the retired measure, for contrast -- characters of source", theSourceLength)

/-- Λ itself, scaled -- the device does reciprocals by scaled floor, never by
a real. -/
def lambdaScaled : Nat := 1000000000 / lambdaInverse

#eval ("Λ⁻¹ ≡ device (the AST reading, structural)", lambdaInverse)
#eval ("Λ, scaled by 1e9", lambdaScaled)

def theFieldEquations : FieldEquationSlots :=
  { einsteinTensor := "UniverseTensor (Ep4) -- carrier present, reading OPEN"
    cosmological   := "EARNED -- Λ⁻¹ ≡ device, the device's own extent"
    eightPi        := "π EARNED (Archimedes squeeze, 22/7 wall) -- BEHIND THE BRIDGE"
    bigG           := "EARNED -- the inferred bit stream, above"
    stressEnergy   := "strain (.rest_call slot) -- identification OPEN"
    cToTheFourth   := "the direct path (bent card) -- INTERPRETATION, not measured" }

#eval theFieldEquations


/-%Y% /* the three cards, and the number under them */ %Y%-/
/- THE FINISH.

Three cards on the table, and the whole night has been about which one has
the quarter under it.  They are not three numbers.  They are ONE number read
three ways, and it comes from the smallest fact the device has:

    THERE ARE TWO BOXES.

`boxCount = 2` (Episode 24), and `finiteness_forces_electron` decides the
rest: in a two-box count, anything that is not the value box IS the electron
box -- nowhere else to sit.  That is Dirichlet, native, and it is the only
input.  From it:

    separation = the two boxes AND the electron's, counted   = 3
    slip       = the pair                                     = 2
    coupling   = slip · separation²                           = 18

The separation is EARNED, not added: `earnedSum` is the length of the
coproduct roster `Fin a ⊕ Fin b`, because the rfc's rule was "we never
actually earn addition, you have to use the `Sum`."  The three is a count
performed, not an arithmetic fact asserted.  And it is the count to three --
the same three the trips take, arriving here as a DISTANCE.

Then the slip law, which is the second variation and is inverse-square:
`slip(d) = C/d²`.  The three cards are that law read at the stations:

    C = slip(1)                    the coupling at unit distance
    T = ⌊slip(2)⌋ + 1              the first integer above the slip at two
    R = the coupling as an extent  the orbit radius

One root, three paths -- and never to be sold as three independent numbers.

The crossing is where the slip meets the target: `slip(d) = T`, so
`d* = √(C/T)`, taken with the PROVEN integer square root (`FloorSqrt`,
axiom-clean, `floorSqrt_correct`) -- no reals, no Mathlib, nothing imported
that the device did not build.

And the map, from Episode 40's own contraction:

    tange(d) = (d − 1)/d          the channel that opens as the parts close
    α        = tange(d*) · (T/R) / R
    1/α      = d*·R² / ((d*−1)·T)

BLIND.  No target is written in this file, no expected value, no bracket.
The cards are laid, the crossing is taken, the reciprocal is read, and
whatever comes up comes up.  Numbers read last. -/

/-- Addition EARNED, after the rfc: the cardinality of the coproduct roster,
counted by `List.length`.  The `+` operator never appears. -/
def earnedSum (a b : Nat) : Nat :=
  ((List.range a).map Sum.inl ++ (List.range b).map Sum.inr : List (Nat ⊕ Nat)).length

/-- Two boxes, and only two.  The pigeonhole, and the only input. -/
def theTwoBoxes : Nat := 2

/-- The electron's box: the second-variation box, box one. -/
def theElectronsBox : Nat := 1

/-- The separation: the boxes and the electron's box, counted as a cardinality.
The count to three, arriving as a distance. -/
def theSeparation : Nat := earnedSum theTwoBoxes theElectronsBox

/-- The observed slip: the pair. -/
def theObservedSlip : Nat := theTwoBoxes

/-- The coupling: slip times the square of the separation. -/
def theCoupling : Nat := theObservedSlip * (theSeparation * theSeparation)

/-- THE THREE CARDS.  `T` is the slip law read at the second station: the
distance is two, so the square is `theTwoBoxes * theTwoBoxes`, and the target
is the first integer above what the slip reads there. -/
def cardC : Nat := theCoupling
def cardT : Nat := theCoupling / (theTwoBoxes * theTwoBoxes) + 1
def cardR : Nat := theCoupling

#eval ("the separation, earned", theSeparation)
#eval ("the coupling: slip · separation²", theObservedSlip, theSeparation * theSeparation, theCoupling)
#eval ("THE THREE CARDS  [C, T, R]", cardC, cardT, cardR)

/-- The working scale.  The device reads reciprocals by scaled floor, never
by a real. -/
def alphaScale : Nat := 1000000000

/-- THE CROSSING: `d* = √(C/T)`, scaled, by the proven integer square root. -/
def dStarScaled : Nat :=
  Measurement.FloorSqrt.floorSqrt (cardC * alphaScale * alphaScale / cardT)

/-- 1/α as an exact ratio of whole numbers: `d*·R² / ((d*−1)·T)`.  The scale
cancels, so this is a pure rational -- nothing approximated in the middle. -/
def invAlphaJar : Int × Int :=
  ((dStarScaled * cardR * cardR : Nat), ((dStarScaled - alphaScale) * cardT : Nat))

#eval ("the crossing d*, scaled", dStarScaled)
#eval ("1/α as a ratio", invAlphaJar)
#eval ("1/α", decimalOf invAlphaJar 9)

/-%Y% /* and the diagnostics carry it too */ %Y%-/
/- THE WARNINGS.  A device that has found something should say so where
diagnostics live, not only where output does.  This work has measured the
compiler's complaints from the first page -- the bullshit meter is nothing but
the elaborator's own effort, read back -- so the last reading goes out on the
same channel: the build log itself carries the number, in the register
reserved for things the machine wants you to notice.

Computed at elaboration time, from the same two boxes, through the same proven
root (`FloorSqrt.floorSqrt`, not a meta-level shortcut).  Nothing is quoted
from the readouts above; if the two ever disagreed, the warning and the `#eval`
would say different things and the disagreement would be visible in the log.
Blind, like everything else here: no target is written, the digits are
long-divided out one at a time, and whatever comes up goes in the warning. -/
open Lean Elab Command in
elab "warn_the_answer" : command => do
  let boxes : Nat := 2
  let ebox : Nat := 1
  let sep := boxes + ebox
  let slip := boxes
  let coupling := slip * sep * sep
  let cardC := coupling
  let cardT := coupling / (boxes * boxes) + 1
  let cardR := coupling
  let scale : Nat := 1000000000
  let d := Measurement.FloorSqrt.floorSqrt (coupling * scale / cardT * scale)
  let num := d * cardR * cardR
  let den := (d - scale) * cardT
  let whole := num / den
  let (frac, _) := (List.range 9).foldl
    (fun (p : String × Nat) _ => (p.1 ++ toString ((p.2 * 10) / den), (p.2 * 10) % den))
    ("", num % den)
  logWarning s!"the device answers [{cardC} {cardT} {cardR}]"
  logWarning s!"the crossing is {d} over {scale}"
  logWarning s!"1/alpha = {whole}.{frac}"

warn_the_answer

end Measurement
