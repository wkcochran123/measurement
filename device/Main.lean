import Measurement

def main : IO Unit :=
  IO.println s!"Hello, {hello}!"

def two : Nat := 2

#check two

example : two = 2 := by
  rfl
