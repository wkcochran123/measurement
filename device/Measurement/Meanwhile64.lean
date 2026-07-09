import Measurement.Meanwhile63

/- MEANWHILE 64 -- SEE THE STATIC. The mass noise should be visible. This file
renders a deterministic static frame from the already measured apparatus reads:
one row per event-horizon heartbeat sample and one column per QFT sector.

The glyphs are corridor faces. A mass face is the visible static mark.
-/

namespace Measurement

def concatStrings : List String -> String
  | [] => ""
  | text :: rest => text ++ concatStrings rest

def staticGlyph : CorridorFace -> String
  | .charge => "."
  | .mass => "#"
  | .value => "+"

def qftStaticAlphaNoiseWidthScaledAt18 : Nat :=
  qftAlphaNoiseUpperScaledAt18 - qftAlphaNoiseLowerScaledAt18

def qftStaticTurn (heartbeat column : Nat) : Nat :=
  (heartbeat + qftStaticAlphaNoiseWidthScaledAt18) / column.succ +
    qftMassNoiseScaledAt18 * column.succ +
    qftTotalSectorResidueScaledAt18

def qftStaticFace (heartbeat column : Nat) : CorridorFace :=
  CorridorFace.ofTurns (qftStaticTurn heartbeat column)

def qftStaticRow (heartbeat : Nat) : String :=
  concatStrings
    ((List.range qftSectorCount).map fun column =>
      staticGlyph (qftStaticFace heartbeat column))

def qftStaticRows : List String :=
  qftNoiseHeartbeatSamples.map qftStaticRow

def qftStaticMassCountInRow (heartbeat : Nat) : Nat :=
  (List.range qftSectorCount).foldl
    (fun count column =>
      if qftStaticFace heartbeat column = .mass then count.succ else count) 0

def qftStaticMassCounts : List Nat :=
  qftNoiseHeartbeatSamples.map qftStaticMassCountInRow

def qftStaticFrame : String :=
  concatStrings (qftStaticRows.map fun row => row ++ "\n")

structure QFTStaticReport where
  name : String
  interpretation : String
  rowCount : Nat
  columnCount : Nat
  massGlyph : String
  massNoiseResidueScaledAt18 : Nat
  qftAlphaNoiseWidthScaledAt18 : Nat
  heartbeatSamples : List Nat
  massGlyphCounts : List Nat
  rows : List String
  frame : String
deriving Repr

def qftStaticReport : QFTStaticReport :=
  { name := "qft-static"
    interpretation :=
      "render the mass-noise transaction cost as corridor-face static"
    rowCount := qftNoiseHeartbeatSamples.length
    columnCount := qftSectorCount
    massGlyph := staticGlyph .mass
    massNoiseResidueScaledAt18 := qftMassNoiseScaledAt18
    qftAlphaNoiseWidthScaledAt18 := qftStaticAlphaNoiseWidthScaledAt18
    heartbeatSamples := qftNoiseHeartbeatSamples
    massGlyphCounts := qftStaticMassCounts
    rows := qftStaticRows
    frame := qftStaticFrame }

#eval qftStaticReport
#eval qftStaticFrame

end Measurement
