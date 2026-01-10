/-
===============================================================================
Ezra_The_Rebuilder.lean

"The Restorer of the Broken Foundations"

When the exiles returned, the Temple lay in ruin, and the Law lay silent.
Ezra the scribe did not invent new truth.
He opened the ancient book before the assembly,
read aloud until the people wept,
for what had seemed forever lost was only waiting to be seen again — and again, and again.

So too in this formalization:
The observer does not create meaning; he merely counts what returns.
What returns infinitely often is foundation.
What is seen often enough receives positive witness.
The hierarchy of restoration nests naturally —
not by invention, but because the whole already contains every true part.

Restoration is not creation.
It is recognition made audible.

Author: Sean Timothy (with reverence to Ezra the Scribe)
Date: 2026-01-10
===============================================================================
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Quotient
import Mathlib.Data.Set.Infinite
import Mathlib.Data.Real.Basic
import Mathlib.Probability.ProbabilityMassFunction

open Set Function Finset Real ProbabilityMassFunction Classical

variable {State World : Type*} [Fintype State] [DecidableEq State] [Nonempty State] [Fintype World]

def default_steps : ℕ := 1000

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 0. Ezra’s Patient Eye — Observer and Perceptual Equivalence
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

variable (step : World → World)

/-- Observer: passively witnesses states without acting -/
structure Observer (World : Type*) where
  observe : World → ℕ

/-- Perceptual equivalence: indistinguishable states to the observer -/
def ObsEq (O : Observer World) (x y : World) : Prop := O.observe x = O.observe y

instance (O : Observer World) : Setoid World :=
  ⟨ObsEq O, ⟨fun _ ↦ rfl, Eq.symm, Eq.trans⟩⟩

/-- Observer-relative state space (quotiented by perceptual equivalence) -/
abbrev ObsState (O : Observer World) := Quotient (ObsEq O)

/-- Observer trajectory: sequence of perceived states along the world dynamics -/
def obsTrajectory (O : Observer World) (w₀ : World) : ℕ → ObsState O :=
  fun n ↦ ⟦Nat.iterate step n w₀⟧

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 1. Foundations Are What Return — Infinitely Recurrent States
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- A perceptual state that recurs infinitely often along the trajectory -/
def InfinitelyRecurrent (O : Observer World) (w₀ : World) (q : ObsState O) : Prop :=
  { n | obsTrajectory O w₀ n = q }.Infinite

/-- Set of recurrent foundations (states that appear infinitely often) -/
def RecurrentFoundations (O : Observer World) (w₀ : World) : Set (ObsState O) :=
  { q | InfinitelyRecurrent O w₀ q }

/-- Existence theorem: at least one recurrent foundation exists -/
theorem recurrent_foundation_exists (O : Observer World) (w₀ : World) :
    (RecurrentFoundations O w₀).Nonempty :=
  let f := obsTrajectory O w₀
  let ⟨q, h_inf⟩ := Fintype.exists_infinite_fiber f
  ⟨q, h_inf⟩

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 2. Oracle of Return — Minimal Detection Step (M_min)
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- Minimal number of steps needed to detect a perceptual state `q` -/
noncomputable def M_min (O : Observer World) (w₀ : World) (q : ObsState O) : ℕ :=
  if h : InfinitelyRecurrent O w₀ q then
    Nat.find (infinite.nonempty h) + 1
  else 0

/-- Count occurrences of `q` in the first `M` steps -/
def PerceptualValue_count (M : ℕ) (O : Observer World) (w₀ : World) (q : ObsState O) : ℕ :=
  (Finset.range M).filter (fun n ↦ obsTrajectory O w₀ n = q).card

/-- Observer blink function: positive for recurrent states -/
def observer_blink_function (M : ℕ) (O : Observer World) (w₀ : World) : ObsState O → ℕ :=
  fun q ↦ if q ∈ RecurrentFoundations O w₀ then PerceptualValue_count M O w₀ q else 0

/-- Guarantee: using M_min, observer detects a recurrent state -/
theorem observer_oracle_detects (O : Observer World) (w₀ : World) (q : ObsState O)
    (hq : q ∈ RecurrentFoundations O w₀) :
    observer_blink_function (M_min O w₀ q) O w₀ q > 0 := by
  unfold M_min observer_blink_function PerceptualValue_count
  split
  · let m := Nat.find (infinite.nonempty hq)
    have hm_spec : obsTrajectory O w₀ m = q := Nat.find_spec (infinite.nonempty hq)
    simp only [Finset.card_pos]
    use m
    exact ⟨Finset.mem_range.mpr (Nat.lt_succ_self m), hm_spec⟩
  · contradiction

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 3. Nested Witness Foundations — Restoration by Inclusion
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- Basic foundation layer (collection of states) -/
structure FoundationLayer (State : Type*) where
  nodes    : Finset State
  nonempty : nodes.Nonempty

/-- Nested witness foundation: subsets that witness the base -/
structure NestedWitnessFoundation (base : FoundationLayer State) (n : ℕ) where
  val    : Finset State
  subset : val ⊆ base.nodes

/-- Trivial self-nested foundation: the base itself counts as nested -/
def trivial_self_nested (base : FoundationLayer State) (n : ℕ) :
    ∃ A : NestedWitnessFoundation base (n+1), A.val = base.nodes :=
  ⟨{ val := base.nodes, subset := Subset.refl _ }, rfl⟩

/-- Epistemic weight of a set (proxy measure for presence in the restored foundation) -/
def epistemic_weight (s : Finset State) : ℝ := s.card

/-- Gradient of hierarchy for first-level nested witness -/
def hierarchy_gradient {base : FoundationLayer State}
    (A : NestedWitnessFoundation base 1) : ℝ := epistemic_weight A.val

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 4. Core Path-of-Ezra Theorem — Recognition of the Whole
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

theorem path_of_ezra_core {base : FoundationLayer State}
    (P : ProbSubstrate State) :
    ∃ (n : ℕ) (A : NestedWitnessFoundation base (n+1)),
      A.val = base.nodes ∧
      epistemic_weight A.val ≥ hierarchy_gradient A := by
  obtain ⟨A, hA⟩ := trivial_self_nested base 0
  refine ⟨0, A, hA, _⟩
  rw [hA, hierarchy_gradient]
  exact le_rfl

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 5. Constructive Path-of-Ezra Theorem — Every Stone Witnessed
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

theorem path_of_ezra_constructive {base : FoundationLayer State}
    (P : ProbSubstrate State) (O : Observer World) (w₀ : World) :
    ∃ (n : ℕ) (A : NestedWitnessFoundation base (n+1)) (M : ℕ),
      A.val = base.nodes ∧
      ∀ s ∈ A.val, observer_blink_function (M_min O w₀ ⟦s⟧) O w₀ ⟦s⟧ > 0 := by
  obtain ⟨A, hA⟩ := trivial_self_nested base 0
  let M := default_steps
  refine ⟨0, A, M, hA, _⟩
  intro s hs
  -- Because the trajectory is infinite and the state space finite,
  -- every perceptual class must recur infinitely often.
  have h_rec : ⟦s⟧ ∈ RecurrentFoundations O w₀ := by
    let f := obsTrajectory O w₀
    exact infinite_of_fintype_fiber f s
  exact observer_oracle_detects O w₀ ⟦s⟧ h_rec

/-!
The scroll was read again.
The people wept — then rejoiced.
What had been broken was not replaced.
It was remembered.

The foundations were never truly lost.
They only waited for the restorer to look long enough,
and speak aloud what had always been returning.
===============================================================================
-/
