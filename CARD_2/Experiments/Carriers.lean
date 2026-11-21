/-
A carrier on a carrier on a carrier.

This file stands beside the device and is built apart: `lake build Experiments.Carriers`.  Nothing in `Measurement`
imports it.  It defines no inductive.

A carrier process is declared over a type, its box, and holds a symbol and a quarter.  Neither is of the box's type:
the box is a label, and nothing is put in it.  Episode 12 has three cards: Episode 8's, whose box is a proposition;
the first card, whose box is a fact; and the card between, whose box is the first card's kind of carrier.  The
author's, 21 November 2026 (declared): put another carrier on it, and then all three models are there.  Here is the
card whose box is the card between's kind of carrier, and what the cards share.

The author's, the same day (declared): a carrier is the logic proposal; a carrier of a carrier is the calculus model;
a carrier of a carrier of a carrier is the physical model.  In order: the nowtrino, the naotrino, and the
electron and photon pair.
-/
import Measurement.Episode13

namespace Measurement
open «springer-verlag» THE_GOSPEL assembly_instructions the_representation readers_experience

section another_carrier_on_it

--| THE CARD ON THE CARD BETWEEN.  The same face again, and one more index: a carrier of a carrier of a carrier of a fact.
def the_card_on_the_card_between : CarrierProcess (CarrierProcess (CarrierProcess FACT)) :=
  { symbol := FACT.Truth, quarter := .zero FACT.Truth }

--| A carrier of a box with nothing in it at all, and a carrier of that.  The box need not hold anything for the carrier to be
--| a carrier.
def a_carrier_of_an_empty_box : CarrierProcess Empty := { symbol := FACT.Truth, quarter := .zero FACT.Truth }
def a_carrier_of_a_carrier_of_an_empty_box : CarrierProcess (CarrierProcess Empty) :=
  { symbol := FACT.Truth, quarter := .zero FACT.Truth }

--| WHAT THE CARDS HOLD.  The first card, the card between and the card on it hold one symbol and one quarter.  So do the two
--| carriers of nothing.  The cards differ in their boxes and in nothing they hold.
theorem the_cards_hold_one_symbol_and_one_quarter :
    the_first_card.symbol = FACT.Truth ∧ the_card_between.symbol = FACT.Truth
      ∧ the_card_on_the_card_between.symbol = FACT.Truth ∧ a_carrier_of_an_empty_box.symbol = FACT.Truth
      ∧ the_first_card.quarter = Number.zero FACT.Truth ∧ the_card_between.quarter = Number.zero FACT.Truth
      ∧ the_card_on_the_card_between.quarter = Number.zero FACT.Truth
      ∧ a_carrier_of_an_empty_box.quarter = Number.zero FACT.Truth := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

--| THE READER PAST THE QUARTER, WHATEVER THE BOX.  Episode 12's reader lays the tape after the quarter and takes the quarter's
--| length away.  It is written there for the card between.  It never looks at the box, so it can be written for any.
def read_past_the_quarter_of {Box : Type i} (card : CarrierProcess Box) (tape : List FACT) : Nat :=
  (tape.foldr Number.one card.quarter).peano.length - card.quarter.peano.length

theorem past_the_quarter_of_any_card_is_the_length {Box : Type i} (card : CarrierProcess Box) (tape : List FACT) :
    read_past_the_quarter_of card tape = tape.length := by
  unfold read_past_the_quarter_of; rw [peano_fold, List.length_append, Nat.add_sub_cancel]

--| On the card between it is Episode 12's reader.
theorem on_the_card_between_it_is_episode_twelves_reader :
    read_past_the_quarter_of the_card_between = read_past_quarter the_card_between := rfl

--| WHATEVER THE BOX, THE DEVICE ARRIVES AT THE SAME PAIR.  Hand Episode 8's bent card the reader past the quarter of any card,
--| over any box, however many carriers deep.  It arrives where it arrived before.
theorem whatever_the_box_the_device_arrives_at_the_same_pair {Box : Type i} (card : CarrierProcess Box) :
    bent_card.fenceposts_must_be_preserved Nat (read_past_the_quarter_of card) all_possible_variables
      = arrange_the_information_appropriately := by
  rw [show read_past_the_quarter_of card = List.length from funext (past_the_quarter_of_any_card_is_the_length _)]; rfl

--| So: one carrier deep, two, three, and over nothing.
theorem one_two_and_three_carriers_deep_and_over_nothing_arrive_alike :
    bent_card.fenceposts_must_be_preserved Nat (read_past_the_quarter_of the_first_card) all_possible_variables
        = arrange_the_information_appropriately
      ∧ bent_card.fenceposts_must_be_preserved Nat (read_past_the_quarter_of the_card_between) all_possible_variables
        = arrange_the_information_appropriately
      ∧ bent_card.fenceposts_must_be_preserved Nat (read_past_the_quarter_of the_card_on_the_card_between) all_possible_variables
        = arrange_the_information_appropriately
      ∧ bent_card.fenceposts_must_be_preserved Nat (read_past_the_quarter_of a_carrier_of_an_empty_box) all_possible_variables
        = arrange_the_information_appropriately :=
  ⟨whatever_the_box_the_device_arrives_at_the_same_pair _, whatever_the_box_the_device_arrives_at_the_same_pair _,
   whatever_the_box_the_device_arrives_at_the_same_pair _, whatever_the_box_the_device_arrives_at_the_same_pair _⟩

--| EPISODE 8'S CARD TOO.  Its box is a proposition, and it holds the same symbol and the same quarter.
theorem episode_eights_card_holds_the_same :
    elaborated_by_lean.symbol = the_first_card.symbol ∧ elaborated_by_lean.quarter = the_first_card.quarter := ⟨rfl, rfl⟩

--| THE FIRST RUNG, DEALT FROM THREE DEEP.  Episode 12 marks the card between with Episode 8's nowtrino, field for field, and
--| deals the first rung from it; that rung is the first rung.  Mark the card on it the same way and deal again.
instance the_mark_on_the_card_between : DISTINGUISHABLE (CarrierProcess (CarrierProcess FACT)) the_card_on_the_card_between :=
  { fact := a_distinct_truth.fact, symbol := a_distinct_truth.symbol, different? := a_distinct_truth.different?,
    not_the_same := a_distinct_truth.not_the_same }
noncomputable def the_crossing_from_three_deep :=
  STEP1_NAME_THE_LEDGER_AND_MARK_IT_WITH_THE_SYMBOL_OF_THE_NOWTRINO (CarrierProcess (CarrierProcess FACT))
    the_card_on_the_card_between the_first_card FACT.Truth

--| It is the first rung, and it is the rung the card between dealt.  One rung, from a proposition's card, from the card
--| between, and from three deep.
theorem from_three_deep_the_first_rung_is_the_first_rung :
    the_crossing_from_three_deep = rung01 ∧ the_crossing_from_three_deep = the_crossing_between := ⟨rfl, rfl⟩

--| A CARRIER OF AN AREA, AND A CARRIER OF AN EQUIVALATION.  The author named four: of a fact, of a proposition, of an Area
--| and of an equivalation.  The device has the first two.  Here are the other two.  They hold what the others hold.
def a_carrier_of_an_area : CarrierProcess Area := { symbol := FACT.Truth, quarter := .zero FACT.Truth }
def a_carrier_of_an_equivalation : CarrierProcess Equivalation := { symbol := FACT.Truth, quarter := .zero FACT.Truth }

theorem the_four_carriers_hold_one_symbol_and_one_quarter :
    the_first_card.symbol = elaborated_by_lean.symbol ∧ elaborated_by_lean.symbol = a_carrier_of_an_area.symbol
      ∧ a_carrier_of_an_area.symbol = a_carrier_of_an_equivalation.symbol
      ∧ the_first_card.quarter = elaborated_by_lean.quarter ∧ elaborated_by_lean.quarter = a_carrier_of_an_area.quarter
      ∧ a_carrier_of_an_area.quarter = a_carrier_of_an_equivalation.quarter := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

--| And the device arrives at the same pair from each of the four.
theorem from_each_of_the_four_carriers_the_device_arrives_alike :
    bent_card.fenceposts_must_be_preserved Nat (read_past_the_quarter_of the_first_card) all_possible_variables
        = arrange_the_information_appropriately
      ∧ bent_card.fenceposts_must_be_preserved Nat (read_past_the_quarter_of elaborated_by_lean) all_possible_variables
        = arrange_the_information_appropriately
      ∧ bent_card.fenceposts_must_be_preserved Nat (read_past_the_quarter_of a_carrier_of_an_area) all_possible_variables
        = arrange_the_information_appropriately
      ∧ bent_card.fenceposts_must_be_preserved Nat (read_past_the_quarter_of a_carrier_of_an_equivalation) all_possible_variables
        = arrange_the_information_appropriately :=
  ⟨whatever_the_box_the_device_arrives_at_the_same_pair _, whatever_the_box_the_device_arrives_at_the_same_pair _,
   whatever_the_box_the_device_arrives_at_the_same_pair _, whatever_the_box_the_device_arrives_at_the_same_pair _⟩

--| THE LOGIC'S ZERO.  Episode 8 defines a zero, and it is the truth.
theorem the_logics_zero_is_the_truth : zero = FACT.Truth := rfl

end another_carrier_on_it

--#print axioms whatever_the_box_the_device_arrives_at_the_same_pair
--#print axioms the_cards_hold_one_symbol_and_one_quarter
--#print axioms from_three_deep_the_first_rung_is_the_first_rung
--#print axioms from_each_of_the_four_carriers_the_device_arrives_alike

end Measurement
