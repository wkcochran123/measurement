/-
The device's readings, as Mathlib reads them, and the EKG that checks it.

Episode 13 met Meanings' interfaces with its own receipts.  Here the readings it met are handed to Mathlib as `≃+*`, and
Episode 8's EKG reads what it costs to elaborate each one.  `ekg_meets` elaborates a term on the EKG and records the
reading.  If the interface is not met the term does not elaborate and the file does not compile: there is no reading of
an interface that is not met.
-/
import Calibrate.Readings
import Measurement.Episode13

namespace Calibrate
open Meanings Measurement Measurement.the_table
open Lean Elab Command in
--| THE EKG, ASKED WHETHER AN INTERFACE IS MET.  It elaborates the term on Episode 8's meter.  Met: the heartbeats and the
--| blank drawn beside them.  Not met: an error, and the build stops; no placeholder is put in its place to be read.
elab "ekg_meets " t:term : command => do
  let (beat, blank) ← liftTermElabM (Term.withoutErrToSorry (Measurement.the_ekg_reads t))
  logInfo m!"met: {beat} heartbeats against a blank of {blank}"

--| The Area up to its count is the naturals, as a ring.
def the_area_as_the_naturals : CountedAsNat.ReadAsNat Area ≃+* ℕ := countedRingEquiv
--| The Account up to its balance is the integers, as a ring.
def the_account_as_the_integers : BalancedAsInt.ReadAsInt Account ≃+* ℤ := balancedRingEquiv
--| Two Accounts up to their crossing are the rationals, as a ring.  This one bills choice.
def two_accounts_as_the_ratios : BalancedAsInt.ReadAsRat Account ≃+* Rat := ratioedRingEquiv

ekg_meets (countedRingEquiv : CountedAsNat.ReadAsNat Area ≃+* ℕ)
ekg_meets (balancedRingEquiv : BalancedAsInt.ReadAsInt Account ≃+* ℤ)
ekg_meets (ratioedRingEquiv : BalancedAsInt.ReadAsRat Account ≃+* Rat)

end Calibrate
