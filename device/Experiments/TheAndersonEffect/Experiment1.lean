import Experiments.Common

/-!
# The Anderson Effect — finite localization no-go

Source: `instrument/chapters/07.tex:2478`, `\begin{phenomenon}[The Anderson Effect]`.

> Transport requires the extension of a local refinement into a coherent global
> pattern. When the local update rules vary incoherently, no admissible global
> extension exists. The failure of propagation is not dissipation, but the
> impossibility of constructing a minimal, consistent refinement path through disorder.

This file models that *impossibility* finitely. A `Chain` is a finite line of sites.
Each site carries a local update `phase : Bool` (the local refinement rule). A *global
extension* is an assignment `state : Nat → Bool` of a value to every site such that
adjacent sites agree **up to the local phase**: `state (i+1) = (state i) XOR phase i`.
This is the discrete shadow of "transport carries the local refinement to the next site."

A chain is **coherent** when the accumulated phase around the closed loop (site 0 …
last … back to 0) is even — i.e. the boundary condition `state 0 = state 0` is consistent
with the phases. When the phases sum to an **odd** parity around the loop, the closed
chain is *frustrated*: the transport equation forces `state 0 = ¬ state 0`, so **no global
extension exists**. That is localization: disorder (an odd loop) blocks propagation.

The content-bearing claim couples two halves:
* a **frustrated** chain (`disorderedLoop`) genuinely admits **no** consistent global
  extension (the no-go) — proved by construction; and
* a **coherent** chain (`orderedLoop`) **does** admit one (transport propagates) — so the
  no-go is not vacuous: it is the disorder, not the model, that blocks the loop.

## NOT claimed
No claim about real Anderson localization, electron mobility edges, the actual
disorder-averaged conductivity, a localization length, a mobility threshold, or any
spectral statement. `phase` is a labelled Boolean, not a derived random potential. This is
a finite parity-obstruction model of "incoherent local rules ⇒ no admissible global
extension," nothing more. There is **no** device/`Measurement` coupling: the Anderson
phenomenon is a localization no-go with no charge/holonomy/positron content to map onto,
so per the cheat-sheet this is the honest content version (tag `inadmissibilityNoGo`).
-/

namespace Experiments.TheAndersonEffect

/-- A finite chain of `length` sites. Each site `i < length` carries a local update
`phase i : Bool` — the local refinement rule transported to the next site. -/
structure Chain where
  length : Nat
  phase : Nat → Bool

/-- The accumulated phase (XOR) over the *open* path through sites `0, 1, …, n-1`.
`loopParity` (below) closes it; this is the running parity of the first `n` local rules. -/
def Chain.openParity (c : Chain) : Nat → Bool
  | 0 => false
  | n + 1 => (c.openParity n) ^^ (c.phase n)

/-- The parity accumulated around the **closed loop** of the chain: the XOR of every
local update rule on the chain. The loop is *frustrated* exactly when this is `true`. -/
def Chain.loopParity (c : Chain) : Bool :=
  c.openParity c.length

/-- A chain is **coherent** when its closed loop carries even (false) accumulated phase. -/
def Chain.coherent (c : Chain) : Prop :=
  c.loopParity = false

/-- A **global extension**: an assignment of a value to every site obeying the transport
equation at each interior step (`state (i+1) = state i XOR phase i`) AND closing the loop
(`state length = state 0`). Existence of such a `state` is "transport propagates." -/
def Chain.ExtendedBy (c : Chain) (state : Nat → Bool) : Prop :=
  (∀ i, i < c.length → state (i + 1) = ((state i) ^^ (c.phase i))) ∧
    state c.length = state 0

/-- `c` **admits a global extension** when some `state` extends it. -/
def Chain.AdmitsExtension (c : Chain) : Prop :=
  ∃ state, c.ExtendedBy state

-- Decidability so `decide`/`#eval` see through `coherent`.
instance (c : Chain) : Decidable c.coherent := by
  unfold Chain.coherent; exact inferInstance

-- ---------------------------------------------------------------------------
-- The transport equation, solved: the unique candidate extension from a seed.
-- ---------------------------------------------------------------------------

/-- The canonical solution of the transport recurrence seeded at `state 0 = b`:
`canonical c b i = b XOR (accumulated phase over the first i sites)`. This is the ONLY
function that can satisfy the interior transport equations, so existence of any extension
reduces to whether `canonical` closes the loop. -/
def Chain.canonical (c : Chain) (b : Bool) (i : Nat) : Bool :=
  b ^^ c.openParity i

theorem Chain.canonical_zero (c : Chain) (b : Bool) : c.canonical b 0 = b := by
  simp [Chain.canonical, Chain.openParity]

/-- The canonical solution satisfies the interior transport equation at every step. -/
theorem Chain.canonical_step (c : Chain) (b : Bool) (i : Nat) :
    c.canonical b (i + 1) = ((c.canonical b i) ^^ (c.phase i)) := by
  simp [Chain.canonical, Chain.openParity]

/-- The canonical solution closes the loop at site `length` to `b XOR loopParity`. -/
theorem Chain.canonical_at_length (c : Chain) (b : Bool) :
    c.canonical b c.length = (b ^^ c.loopParity) := by
  simp [Chain.canonical, Chain.loopParity]

-- ---------------------------------------------------------------------------
-- FALSIFIABLE no-go: a frustrated (odd-loop) chain admits NO global extension.
-- This breaks if `ExtendedBy` dropped EITHER the interior law OR the loop-closing law.
-- ---------------------------------------------------------------------------

/-- Uniqueness of the interior solution: any `state` obeying every interior transport
equation IS the canonical one seeded at its own `state 0`. (Used to reduce the no-go to a
parity computation. Falsifiable: drop the interior conjunct and this is false.) -/
theorem Chain.interior_forces_canonical (c : Chain) (state : Nat → Bool)
    (h : ∀ i, i < c.length → state (i + 1) = ((state i) ^^ (c.phase i))) :
    ∀ i, i ≤ c.length → state i = c.canonical (state 0) i := by
  intro i
  induction i with
  | zero => intro _; simp [c.canonical_zero]
  | succ n ih =>
    intro hle
    have hn : n < c.length := Nat.lt_of_succ_le hle
    rw [h n hn, ih (Nat.le_of_lt hn), c.canonical_step]

/-- **THE NO-GO (falsifiable, ∀-quantified).** A frustrated chain — odd accumulated phase
around the loop — admits NO global extension. Transport cannot propagate through the
disorder. Both conjuncts of `ExtendedBy` are load-bearing: the interior law pins the
solution to `canonical`, and the loop-closing law then forces `b = b XOR true`,
i.e. `b = ¬ b`, a contradiction. -/
theorem no_extension_of_frustrated (c : Chain) (h : c.loopParity = true) :
    ¬ c.AdmitsExtension := by
  rintro ⟨state, hinterior, hclose⟩
  -- interior law ⇒ state is canonical at site 0 and site length
  have hlen : state c.length = c.canonical (state 0) c.length :=
    c.interior_forces_canonical state hinterior c.length (Nat.le_refl _)
  rw [c.canonical_at_length, h] at hlen
  -- now state length = (state 0) XOR true = ¬ (state 0), but loop-closing says it = state 0
  rw [hclose] at hlen
  -- hlen : state 0 = (state 0) XOR true  ⇒  contradiction
  simp at hlen

-- ---------------------------------------------------------------------------
-- Non-vacuity: a COHERENT chain DOES admit a global extension (transport propagates).
-- ---------------------------------------------------------------------------

/-- A coherent chain (even loop) admits the canonical extension seeded at `false`. -/
theorem extension_of_coherent (c : Chain) (h : c.coherent) :
    c.AdmitsExtension := by
  refine ⟨c.canonical false, ?_, ?_⟩
  · intro i _; exact c.canonical_step false i
  · rw [c.canonical_at_length, c.canonical_zero]
    unfold Chain.coherent at h
    rw [h]
    rfl

-- ---------------------------------------------------------------------------
-- The two canonical chains.
-- ---------------------------------------------------------------------------

/-- A DISORDERED loop of 3 sites whose local rules XOR to an odd parity (`true ^^ false ^^
false = true`): frustrated, hence localizing. -/
def disorderedLoop : Chain :=
  { length := 3, phase := fun i => decide (i = 0) }   -- phase 0 = true, else false

/-- An ORDERED loop of 3 sites whose local rules XOR to even parity (here: all `false`):
coherent, hence transporting. -/
def orderedLoop : Chain :=
  { length := 3, phase := fun _ => false }

theorem disorderedLoop_frustrated : disorderedLoop.loopParity = true := by decide
theorem orderedLoop_coherent : orderedLoop.coherent := by decide

-- ---------------------------------------------------------------------------
-- THE CLAIM (content-bearing: a real conjunction of the no-go and its non-vacuity).
-- ---------------------------------------------------------------------------

/-- The claim, in honest halves:
* (localization) the disordered loop admits **no** global extension — disorder blocks
  transport (`no_extension_of_frustrated`); and
* (non-vacuity) the ordered loop **does** admit one — coherent rules propagate
  (`extension_of_coherent`), so the obstruction is the disorder, not the model. -/
def claimStatement : Prop :=
  (¬ disorderedLoop.AdmitsExtension) ∧ orderedLoop.AdmitsExtension

def claim : Experiments.Common.Claim :=
  { tag := Experiments.Common.ClaimTag.inadmissibilityNoGo
    statement := claimStatement }

theorem claim_holds : claim.statement :=
  ⟨no_extension_of_frustrated disorderedLoop disorderedLoop_frustrated,
    extension_of_coherent orderedLoop orderedLoop_coherent⟩

/-- An honest ceiling: a finite inadmissibility no-go, nothing more. -/
theorem ceiling :
    claim.tag = Experiments.Common.ClaimTag.inadmissibilityNoGo := rfl

-- ---------------------------------------------------------------------------
-- A computable run + a NON-vacuous Experiment.claim, with a proved bridge.
-- ---------------------------------------------------------------------------

structure Setup where
  chain : Chain

/-- The run computes whether the chain is coherent (i.e. whether transport propagates).
A frustrated chain returns `false`; a coherent one `true`. -/
def run (s : Setup) : Bool := decide s.chain.coherent

/-- The exported claim is a genuine function of the setup: it reads the chain's coherence,
which `run` computes. Pinned to `run` by `run_iff_claim`; not `fun _ => True`. -/
def experiment : Experiments.Common.Experiment Setup Bool :=
  { tag := claim.tag
    run := run
    claim := fun s => s.chain.coherent }

/-- `run` reports coherence exactly. -/
theorem run_iff_claim (s : Setup) :
    run s = true ↔ experiment.claim s := by
  simp only [run, experiment, decide_eq_true_iff]

/-- THE HEART OF THE EFFECT (∀-quantified, falsifiable both ways): a chain admits a global
extension **iff** it is coherent. Frustration is *exactly* the obstruction to transport —
nothing else blocks propagation, and nothing else is needed to enable it. -/
theorem coherent_iff_admits (s : Setup) :
    s.chain.coherent ↔ s.chain.AdmitsExtension := by
  constructor
  · exact extension_of_coherent s.chain
  · intro hadmits
    unfold Chain.coherent
    cases hlp : s.chain.loopParity with
    | false => rfl
    | true =>
      -- frustrated ⇒ no extension, contradicting hadmits
      exact absurd hadmits (no_extension_of_frustrated s.chain hlp)

def canonicalSetup : Setup := { chain := orderedLoop }
def disorderedSetup : Setup := { chain := disorderedLoop }

#eval run canonicalSetup      -- expect: true  (coherent ⇒ transports)
#eval run disorderedSetup     -- expect: false (frustrated ⇒ localized)
#print axioms claim_holds     -- ambient footprint, NOT coupling (no device symbols here)

/-- Bring a minimal device next to this experiment: it records whether the exported claim fires. -/
def deviceNear (setup : Setup) : Bool :=
  run setup

theorem deviceNear_detects_claim (setup : Setup) :
    deviceNear setup = true ↔ experiment.claim setup := by
  simpa [deviceNear] using run_iff_claim setup

def triangulation : Experiments.Common.Triangulation Setup Bool :=
  { experiment := experiment
    device := deviceNear
    detects := deviceNear_detects_claim }

end Experiments.TheAndersonEffect
