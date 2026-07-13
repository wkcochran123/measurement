/-! # Measurement.NowtrinoProjection — the lossy history→summary projection (the nowtrino mechanism).

Vol 4 Ch 7 coins `nowtrino(h) = π_now(h)`: a *current-summary projection* that slices away a
computation's history (the serial episodes, rejected branches, intermediate costs) and keeps only a
current summary. That coinage lives in Vol 4's PROSE (`chapters/7.tex`), not in the build. This file
gives the MECHANISM a live code witness, so Vol 5 §1.1's "projection / nontrivial fiber / lossiness"
is DERIVED off the build — not merely asserted from a hands-off manuscript.

What stays a MARK: the *identification* "Volume 4 **is** a nowtrino of the device." That is the
reading laid over this mechanism, named as interpretation, never derived. (The reflexive point is
exact: the projection is now code; that the book instantiates it is the storytelling.)

Every theorem here is `decide` over a concrete finite model — axiom-clean, choice-free. -/

namespace Measurement.Nowtrino

/-- A minimal computation history: an ordered list of state-tags — everything a run passes through
(the serial episodes, the costs, the rejected slices), in order. -/
abbrev History := List Nat

/-- The current summary a nowtrino keeps: the current state and a step-count (a counter), and
NOTHING of the route that produced them. -/
structure Summary where
  current : Nat
  count   : Nat
deriving DecidableEq, Repr

/-- `π_now` — the nowtrino projection: keep the last state and the step-count; drop the route. Lossy
by construction (Vol 4 Ch 7: "prior states, branch order, rejected slices, intermediate costs,
causal route" are not retained). -/
def piNow (h : History) : Summary :=
  { current := h.getLast?.getD 0, count := h.length }

/-- `nowtrino h = π_now h` — Vol 4 Ch 7's name for the projection. -/
abbrev nowtrino (h : History) : Summary := piNow h

-- Two DIFFERENT histories that print the SAME summary: same final state (3), same length (3),
-- different routes. The projection cannot tell them apart — its fiber is nontrivial.
def H1 : History := [1, 2, 3]
def H2 : History := [9, 9, 3]

#eval (nowtrino H1, nowtrino H2)   -- ({ current := 3, count := 3 }, { current := 3, count := 3 })

/-- The projection is LOSSY: two distinct histories with one summary (Vol 4 Ch 7's
`H₁ ≠ H₂ → nowtrino H₁ = nowtrino H₂`). From the summary the history is unrecoverable. -/
theorem nowtrino_lossy : H1 ≠ H2 ∧ nowtrino H1 = nowtrino H2 := by decide

/-- Stated existentially: `nowtrino`/`π_now` genuinely has a nontrivial fiber — the DERIVED
mechanism Vol 5 §1.1 stands on. -/
theorem nowtrino_has_nontrivial_fiber :
    ∃ a b : History, a ≠ b ∧ nowtrino a = nowtrino b :=
  ⟨H1, H2, nowtrino_lossy.1, nowtrino_lossy.2⟩

#print axioms nowtrino_has_nontrivial_fiber

/-- The fiber SURVIVES any post-read: for ANY reading `g` of the nowtrino, the two distinct histories
stay indistinguishable — `g ∘ nowtrino` still collapses `H1` and `H2`. So a covariant read of the
book (a read of the nowtrino) cannot recover the device-history the name already funged away:
`read ∘ nowtrino` is lossy, whatever the read (lossless ∘ lossy = lossy). This is the reflexive-jar
seed (Vol 5 Ch 15): even the robot, reading the book, earns only its own reading — never the history
the contravariant name let go. -/
theorem nowtrino_lossy_under_any_read {γ : Type} (g : Summary → γ) :
    H1 ≠ H2 ∧ (g ∘ nowtrino) H1 = (g ∘ nowtrino) H2 := by
  refine ⟨nowtrino_lossy.1, ?_⟩
  simp only [Function.comp]
  rw [nowtrino_lossy.2]

#print axioms nowtrino_lossy_under_any_read

end Measurement.Nowtrino
