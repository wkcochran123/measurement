import Measurement.Episode11

namespace Measurement

universe i

inductive ComputerProgram
| load:      Prop → Type i → ComputerProgram
| transform: Prop → Prop → Type i → Type (i+1) → ComputerProgram → ComputerProgram
| boolean:   Prop → Prop → Prop → Type i → Type (i+1) → Type (i+1) → ComputerProgram → ComputerProgram

end Measurement
