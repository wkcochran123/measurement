import Measurement.Episode23
import Measurement.NamingClose

/- MEANWHILE 24 -- THE NAMING, gate 1: the boxes. Name the electron by counting.

The naming math now lives in `Measurement/NamingClose.lean` (factored to root at
Episode16 -- ep17-loop Phase 1 -- so the loop's forward walk can reach the naming
close without the Episode18-24 tail). This file keeps its chain position (import
Episode23) and holds the #eval readout anchors: the box count, the electron's box,
and the two decided premises, fired here as before. -/

namespace Measurement

/- THE TWO BOXES ARE OURS, AND THEY ARE ENOUGH. We do not find two boxes in the
world; we BUILD two, arbitrarily -- a box called zero and a box called not-zero --
because we can build them cromulently. `Fin boxCount` at `boxCount := 2` is finite
by construction; `boxOf` is total and decides every Variation into one of the two;
the whole partition typechecks and `decide`s. Nothing forces the count to be two.
Two is a count we are ALLOWED to build, so we build it -- a perfectly cromulent
construction, ours and not the world's.

What is NOT ours to choose, once the two boxes stand: the electron MUST be in the
not-zero box. The zero box is already spoken for -- the fixed point pins it to the
value (`fixed_point_pins_zeroth`). The electron is not the value
(`recovered_ne_value`). And in a two-box house there is nowhere else to sit
(`finiteness_forces_electron`: anything that is not the value box IS the not-zero
box). So the construction is arbitrary and the placement is forced: we chose the
boxes; the boxes chose the electron's room.

We claim nothing about the world here -- only that inside a cromulent two-box
device, this is where the electron has to fall. The walk from here keeps opening
the not-zero box into finer boxes (each also ours, each also cromulent, none the
world's own), and the electron keeps the only room finiteness ever leaves it. -/
#eval boxCount                          -- the box count: 2

#eval electronBox                       -- the electron's box: 1 (second-variation box)

#eval (decide (electronBox ≠ valueBox) : Bool)   -- electron box is not the value box: true

#eval (decide (boxOf (.gateaux (.epiphany True) True True (.newton (.epiphany True) True))
              = boxOf (.frechet (.epiphany True) True True True
                        (.newton (.epiphany True) True) (.newton (.epiphany True) True))) : Bool)
                                        -- premise 2b holds: true

#eval (decide (boxOfTensor .universe = boxOfTensor .plain) : Bool)   -- premise 2a holds: true

end Measurement
