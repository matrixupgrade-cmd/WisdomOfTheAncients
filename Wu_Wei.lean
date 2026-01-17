/-!
===============================================================================
Wu_Wei.lean
Unified Constructive Model of Effortless Adaptive Action
===============================================================================

Author: Sean Timothy
Date: 2026-01-17

Purpose:
  • Confidence preorder → observer lag
  • Rule neutrality → zones where action dissolves
  • Neutral paths → persistent uncatchability
  • Basin-indexed & multi-observer extension
  • Multi-step itinerary / steering

Interpretive Frame:
  Wu Wei is not passivity.
  Wu Wei is action that never creates a gradient for resistance.
===============================================================================
-/

namespace PathOfWuWei

/-- Abstract types -/
variable (State Basin Observer : Type)
variable (basin_of : State → Basin)

/-- Confidence is a preorder over states for each observer -/
class ConfidencePreorder (State : Type) (Observer : Type) :=
  (conf : Observer → State → State → Prop)
  (refl : ∀ o s, conf o s s)
  (trans : ∀ o s₁ s₂ s₃, conf o s₁ s₂ → conf o s₂ s₃ → conf o s₁ s₃)

variable [ConfidencePreorder State Observer]
notation s₁ " ⪯[" o "] " s₂ => ConfidencePreorder.conf o s₁ s₂

/-!
------------------------------------------------------------------------------
Wu Wei Steps and Paths
------------------------------------------------------------------------------
-/

/-- A step that does not increase observer confidence -/
def WuWeiStep (o : Observer) (s₁ s₂ : State) : Prop :=
  ¬ (s₁ ⪯[o] s₂)

/-- Wu Wei path: each step avoids reinforcing observer models -/
def WuWeiPath (o : Observer) (path : Nat → State) : Prop :=
  ∀ n, WuWeiStep o (path n) (path (n+1))

/-- Observer catch-up: eventually regains confidence ordering -/
def CatchUpTime (o : Observer) (path : Nat → State) : Prop :=
  ∃ k, ∀ n ≥ k, path n ⪯[o] path (n+1)

/-- Wu Wei advantage: infinitely many steps with no confidence increase -/
def WuWeiAdvantage (o : Observer) (path : Nat → State) : Prop :=
  ∀ k, ∃ n ≥ k, ¬ (path n ⪯[o] path (n+1))

/-- Wu Wei path implies no finite catch-up time -/
theorem no_catch_up_of_wuwei_path
  (o : Observer) (path : Nat → State) (hWu : WuWeiPath o path) :
  ¬ CatchUpTime o path := by
  intro hCatch
  rcases hCatch with ⟨k, hk⟩
  have := hWu k
  have hk' := hk k (le_rfl)
  exact this hk'

/-!
------------------------------------------------------------------------------
Rule Neutrality
------------------------------------------------------------------------------
-/

/-- Strong neutrality: no confidence gradient exists in either direction -/
def RuleNeutrality (o : Observer) (s : State) : Prop :=
  ∀ s', ¬ (s ⪯[o] s') ∧ ¬ (s' ⪯[o] s)

/-- Strict confidence increase -/
def StrictConfIncrease (o : Observer) (s s' : State) : Prop :=
  s ⪯[o] s' ∧ ¬ (s' ⪯[o] s)

/-- Weak neutrality: no strictly better next state exists -/
def WeakRuleNeutrality (o : Observer) (s : State) : Prop :=
  ∀ s', ¬ StrictConfIncrease o s s'

/-- Basin-indexed neutrality -/
def BasinNeutrality (o : Observer) (b : Basin) (s : State) : Prop :=
  basin_of s = b ∧ RuleNeutrality o s

/-- Multi-observer neutrality -/
def MultiNeutral (os : Set Observer) (s : State) : Prop :=
  ∀ o ∈ os, RuleNeutrality o s

/-- Lemma: neutrality blocks confidence increase -/
lemma neutrality_blocks_increase (o : Observer) (s s' : State)
  (hNeut : RuleNeutrality o s) : ¬ (s ⪯[o] s') :=
(hNeut s').1

/-!
------------------------------------------------------------------------------
Neutral Wu Wei Paths
------------------------------------------------------------------------------
-/

/-- Neutral Wu Wei path: avoids reinforcement and visits neutral states infinitely often -/
def NeutralWuWeiPath (o : Observer) (path : Nat → State) : Prop :=
  WuWeiPath o path ∧ ∀ k, ∃ n ≥ k, RuleNeutrality o (path n)

/-!
Central implication chain (effortless action theorem):
  NeutralWuWeiPath
→ infinitely often in RuleNeutrality
→ infinitely many steps with no confidence increase
→ WuWeiAdvantage (permanent ease / uncatchability)
-/

/-- Neutral Wu Wei paths imply Wu Wei advantage -/
theorem neutral_wuwei_implies_advantage
  (o : Observer) (path : Nat → State) (hNeutral : NeutralWuWeiPath o path) :
  WuWeiAdvantage o path := by
  intro k
  rcases hNeutral.2 k with ⟨n, hn_ge, hn_neut⟩
  have h_no_inc : ¬ (path n ⪯[o] path (n+1)) :=
    neutrality_blocks_increase o (path n) (path (n+1)) hn_neut
  exact ⟨n, hn_ge, h_no_inc⟩

/-!
------------------------------------------------------------------------------
Wu Wei Itinerary (Multi-Basin, Multi-Observer)
------------------------------------------------------------------------------
-/

/-- Abstract steering action: preserves neutrality by alignment -/
def WuWeiSteerBasin (os : Set Observer) (b : Basin) (s : State) : State := s

/-- Wu Wei itinerary: each step lands in multi-observer neutrality -/
def WuWeiItinerary (os : Set Observer) (bs : Set Basin) (path : Nat → State) : Prop :=
  ∀ n,
    ∃ b ∈ bs,
      path (n+1) = WuWeiSteerBasin os b (path n) ∧
      MultiNeutral os (path (n+1))

/-- Wu Wei itinerary preserves advantage for all observers -/
theorem WuWeiItineraryMaintainsAdvantage
  (os : Set Observer)
  (bs : Set Basin)
  (path : Nat → State)
  (hItin : WuWeiItinerary os bs path) :
  ∀ o ∈ os, WuWeiAdvantage o path := by
  intro o ho k
  -- Choose n = k+1
  have h_step := hItin k
  rcases h_step with ⟨b, hb, h_eq, h_multi⟩
  have h_neut : RuleNeutrality o (path (k+1)) := h_multi o ho
  refine ⟨k+1, Nat.le_succ k, ?_⟩
  exact neutrality_blocks_increase o (path (k+1)) (path (k+2)) h_neut

/-- Weak form: itinerary guarantees infinitely many neutral states -/
theorem WuWeiItineraryMaintainsWeakAdvantage
  (os : Set Observer) (bs : Set Basin) (path : Nat → State)
  (hItin : WuWeiItinerary os bs path) :
  ∀ o ∈ os, ∀ k, ∃ n ≥ k, MultiNeutral os (path n) := by
  intro o ho k
  refine ⟨k+1, Nat.le_succ k, ?_⟩
  have h_step := hItin k
  rcases h_step with ⟨b, hb, h_eq, h_multi⟩
  simpa using h_multi

/-!
------------------------------------------------------------------------------
Final interpretive remark:

The path of Wu Wei is not passivity.
It is the highest form of activity:
activity that never needs to announce itself,
because it never creates a gradient for resistance.
------------------------------------------------------------------------------
-/

end PathOfWuWei
