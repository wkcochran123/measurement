import Measurement.Meanwhile23
import Measurement.NamingClose

/- MEANWHILE 24 -- THE NAMING, gate 1: the boxes. Name the electron by counting.

The naming math now lives in `Measurement/NamingClose.lean` (factored to root at
Episode16 -- ep17-loop Phase 1 -- so the loop's forward walk can reach the naming
close without the Meanwhile18-24 tail). This file keeps its chain position (import
Meanwhile23) and holds the #eval readout anchors: the box count, the electron's box,
and the two decided premises, fired here as before. -/

namespace Measurement

#eval boxCount                          -- the box count: 2
#eval electronBox                       -- the electron's box: 1 (second-variation box)
#eval (decide (electronBox ≠ valueBox) : Bool)   -- electron box is not the value box: true
#eval (decide (boxOf (.gateaux (.epiphany True) True True (.newton (.epiphany True) True))
              = boxOf (.frechet (.epiphany True) True True True
                        (.newton (.epiphany True) True) (.newton (.epiphany True) True))) : Bool)
                                        -- premise 2b holds: true
#eval (decide (boxOfTensor .universe = boxOfTensor .plain) : Bool)   -- premise 2a holds: true

end Measurement
