/-! # Measurement.CovariantObservation — the covariant action `O:(N,s)→(N',s',y,Γ)`.

Vol 4 Ch 12's covariant read: the robot's observation is **not** a transparent conduit returning a
bare answer `y`. It is a transition of BOTH world and apparatus — the world answers in `N' ≠ N`
(back-action; "the world answers in N', not an untouched N"), the apparatus advances to `s'`, `y` is
read (loaded by both), and `Γ` retains the exchanged baggage — nothing sliced away.

This is the **covariant DUAL** of `NowtrinoProjection` (the contravariant nowtrino, which slices
history to a summary and so has a nontrivial fiber — lossy). Here the trace is RETAINED, so the
reading is **lossless**: with `Γ` kept, the reading determines the `(world, apparatus)` it came from.
Contravariant name slices/funges → fiber; covariant action retains/answers → no fiber.

`O(N,s)=(N',s',y,Γ)` is coined in Vol 4 Ch 12 PROSE; this file gives the MECHANISM a live code
witness (like `NowtrinoProjection`), so Vol 5 §2.1's covariant action is DERIVED off the build. The
identification "the robot's read of the book IS this covariant action" stays MARK.

Every theorem is `omega`/`simp` over a concrete finite model — axiom-clean.
(`world' : Int` = the world state N; `apparatus' : Nat ≥ 0` = the apparatus s, so the coupling
back-action `s+1` is always strictly positive.) -/

namespace Measurement.Covariant

/-- A covariant reading: the world AFTER (`N'`), the apparatus AFTER (`s'`), the answer read (`y`),
and the retained trace (`Γ` — prior world + apparatus, the back-action baggage NOT sliced away). -/
structure Reading where
  world'     : Int        -- N'
  apparatus' : Nat        -- s'
  answer     : Int        -- y
  trace      : List Int   -- Γ
deriving DecidableEq, Repr

/-- The covariant action `O:(N,s)→(N',s',y,Γ)`. The read couples: the world answers in
`N' = N + (s+1)` (back-action, coupling-dependent, never zero); the apparatus advances; `y = N+s` is
read (loaded by both world and apparatus); `Γ = [N, s]` retains what was there before — nothing sliced. -/
def observe (N : Int) (s : Nat) : Reading :=
  { world'     := N + (s + 1)
    apparatus' := s + 1
    answer     := N + s
    trace      := [N, (s : Int)] }

#eval (observe 10 0, observe 10 3)

/-- Reading DISTURBS: the world it answers in (`N'`) is never the untouched `N` — back-action always
(the covariant half the model cannot supply from inside itself). -/
theorem observe_disturbs (N : Int) (s : Nat) : (observe N s).world' ≠ N := by
  have h : (observe N s).world' = N + ((s : Int) + 1) := rfl
  rw [h]; omega

/-- `Γ` is RETAINED: the trace is never empty — the covariant baggage is kept, not sliced (contrast
the nowtrino, which slices history away). -/
theorem trace_retained (N : Int) (s : Nat) : (observe N s).trace ≠ [] := by
  have h : (observe N s).trace = [N, (s : Int)] := rfl
  rw [h]; simp

/-- LOSSLESS — the covariant DUAL of `NowtrinoProjection.nowtrino_has_nontrivial_fiber`: with its
trace retained, the reading determines the `(world, apparatus)` it came from. No fiber: the covariant
witness that RETAINS answers, where the contravariant projection that SLICES loses. -/
theorem observe_lossless (N₁ N₂ : Int) (s₁ s₂ : Nat) :
    observe N₁ s₁ = observe N₂ s₂ → N₁ = N₂ ∧ s₁ = s₂ := by
  intro h
  have hw : N₁ + ((s₁ : Int) + 1) = N₂ + ((s₂ : Int) + 1) := congrArg Reading.world' h
  have ha : s₁ + 1 = s₂ + 1 := congrArg Reading.apparatus' h
  have hs : s₁ = s₂ := Nat.add_right_cancel ha
  subst hs
  exact ⟨by omega, rfl⟩

#print axioms observe_disturbs
#print axioms observe_lossless
