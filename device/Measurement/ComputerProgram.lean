import Measurement.Episode11

namespace Measurement

universe i

inductive ComputerProgram
| load: Fact → Prop → Type → ComputerProgram
| transform: Fact → Fact → Prop → Prop → Type → Type 1 → ComputerProgram → ComputerProgram
| boolean: Fact → Fact → Fact → Prop → Prop → Prop → Type → Type 1 → Type i → ComputerProgram → ComputerProgram

end Measurement
