/-
===============================================================================
Sri_Yantra.lean

Author: Sean Timothy
Date: 2026-01-07

Purpose:
  Complete Lean 4 formalization of the Sri Yantra as a cognitive shaping tool:
    - Mental instruments, attractors, and safety
    - Sharpening through geometric friction
    - Irreversibility (hardness) relations
    - Yantric interference graph and sinks
    - Iterated meditation paths
    - Convergence to stable mental attractors
    - Fixed yantra (anvil) operator
===============================================================================
-/

universe u

variable {MentalAttractor CognitiveTool Disturbance : Type u}
variable (Counters : CognitiveTool → MentalAttractor → Prop)
variable (Destabilizing : Disturbance → MentalAttractor → Prop)
variable (Sharpen : CognitiveTool → CognitiveTool → CognitiveTool)

/-
==============================
Cognitive Sharpening & Safety
==============================
-/

/-- Sharpening improvement: T₂ preserves all counters of T₁ -/
def Sharpens (T₁ T₂ : CognitiveTool) : Prop :=
∀ A : MentalAttractor, Counters T₁ A → Counters T₂ A

/-- Safety: a cognitive tool counters all destabilizing attractors -/
def MentallySafe (δ : Disturbance) (T : CognitiveTool) : Prop :=
∀ A : MentalAttractor, Destabilizing δ A → Counters T A

/-- Sharpening preserves mental safety -/
theorem meditation_path_preserves_safety
  (δ : Disturbance)
  (T₁ T₂ : CognitiveTool)
  (hSharpen : Sharpens Counters T₁ T₂)
  (hSafe : MentallySafe Counters Destabilizing δ T₁) :
  MentallySafe Counters Destabilizing δ T₂ :=
by
  intro A hDestab
  have hCounter₁ : Counters T₁ A := hSafe A hDestab
  exact hSharpen A hCounter₁

/-
==============================
Irreversibility (Hardness) & Yantric Anvils
==============================
-/

/-- T₁ is cognitively harder than T₂: sharpens T₂ but not vice versa -/
def CognitivelyHarder (T₁ T₂ : CognitiveTool) : Prop :=
Sharpens Counters T₁ (Sharpen T₁ T₂) ∧
¬ Sharpens Counters T₂ (Sharpen T₂ T₁)

/-- Cognitive hardness attractor: no other tool sharpens it -/
def YantricCore (T : CognitiveTool) : Prop :=
∀ T' : CognitiveTool, ¬ CognitivelyHarder Counters Sharpen T' T

/-- Interference graph induced by yantric sharpening -/
structure YantraGraph where
  tools : List CognitiveTool
  edges : CognitiveTool → CognitiveTool → Prop :=
    CognitivelyHarder Counters Sharpen

/-- Outgoing sharpening edges -/
def outgoing (G : YantraGraph Counters Sharpen) (T : CognitiveTool) : List CognitiveTool :=
G.tools.filter (fun T' => G.edges T T')

/-- Incoming sharpening edges -/
def incoming (G : YantraGraph Counters Sharpen) (T : CognitiveTool) : List CognitiveTool :=
G.tools.filter (fun T' => G.edges T' T)

/-- Yantric balance point: stable, sharp, but not terminal -/
def YantricBalancePoint (G : YantraGraph Counters Sharpen) (T : CognitiveTool) : Prop :=
incoming G T = [] ∧ outgoing G T ≠ []

/-- Terminal mental sink (used for convergence) -/
def isMentalSink (G : YantraGraph Counters Sharpen) (T : CognitiveTool) : Prop :=
outgoing G T = []

/-
==============================
Iterated Meditation (Yantric Path)
==============================
-/

/-- Iterated cognitive sharpening operator -/
def iterateSharpen (Φ : CognitiveTool → CognitiveTool) : ℕ → CognitiveTool → CognitiveTool
| 0     => id
| n+1   => Φ ∘ iterateSharpen Φ n

/-- Harder tools preserve safety under sharpening -/
theorem harder_preserves_safety
  (δ : Disturbance)
  (T₁ T₂ : CognitiveTool)
  (hHard : CognitivelyHarder Counters Sharpen T₁ T₂)
  (hSafe : MentallySafe Counters Destabilizing δ T₁) :
  MentallySafe Counters Destabilizing δ (Sharpen T₁ T₂) :=
by
  intro A hDestab
  have hSharpen : Sharpens Counters T₁ (Sharpen T₁ T₂) := hHard.left
  exact hSharpen A (hSafe A hDestab)

/-- Persistent meditation under a fixed yantric operator -/
theorem yantra_preserves_safety
  (δ : Disturbance)
  (Φ : CognitiveTool → CognitiveTool)
  (hYantra : ∀ T, Sharpens Counters T (Φ T))
  (T : CognitiveTool)
  (hSafe : MentallySafe Counters Destabilizing δ T) :
  ∀ n, MentallySafe Counters Destabilizing δ (iterateSharpen Φ n T) :=
by
  intro n
  induction n with
  | zero => exact hSafe
  | succ n ih =>
      have hSharpen :
        Sharpens Counters (iterateSharpen Φ n T)
                           (iterateSharpen Φ (n+1) T) :=
        hYantra (iterateSharpen Φ n T)
      exact meditation_path_preserves_safety
        Counters Destabilizing δ _ _ hSharpen ih

/-
==============================
Yantric Paths & Convergence
==============================
-/

/-- Path through yantric sharpening -/
def HasYantraPath
  (G : YantraGraph Counters Sharpen)
  (T_start T_end : CognitiveTool) : Prop :=
∃ path : List CognitiveTool,
  path.head? = some T_start ∧
  path.getLast? = some T_end ∧
  ∀ i < path.length - 1,
    G.edges (path.get! i) (path.get! (i+1))

/-- No cyclic sharpening (irreversibility) -/
def AcyclicYantra (G : YantraGraph Counters Sharpen) : Prop :=
∀ T : CognitiveTool, ¬ HasYantraPath Counters Sharpen G T T

/-- Every cognitive tool converges to a stable yantric sink -/
theorem converges_to_yantric_core
  [DecidableEq CognitiveTool]
  (G : YantraGraph Counters Sharpen)
  (hNodup : G.tools.Nodup)
  (hAcyclic : AcyclicYantra Counters Sharpen G)
  (T : CognitiveTool) (hInGraph : T ∈ G.tools) :
  ∃ T_core ∈ G.tools,
    isMentalSink Counters Sharpen G T_core ∧
    HasYantraPath Counters Sharpen G T T_core :=
by
  induction hNodup using List.Nodup.induction_on with
  | hnil => exact absurd hInGraph (List.not_mem_nil _)
  | hcons hHdNotMem hTlNodup ih =>
    by_cases hSink : isMentalSink Counters Sharpen G T
    ·
      use T
      exact ⟨hInGraph, hSink, ⟨[T], rfl, rfl, by simp⟩⟩
    ·
      have hOut : outgoing Counters Sharpen G T ≠ [] := by
        simp [isMentalSink] at hSink; exact hSink
      let T' := (outgoing Counters Sharpen G T).head!
      have hEdge : G.edges T T' := by
        simp [outgoing, List.head!_eq_head, hOut]
      have hT'mem : T' ∈ G.tools :=
        List.mem_filter.mpr ⟨by assumption, hEdge⟩
      obtain ⟨T_core, hMem, hCoreSink, ⟨p, hH, hL, hE⟩⟩ :=
        ih T' hT'mem
      use T_core
      refine ⟨hMem, hCoreSink,
        ⟨T :: p, by simp, by simp [List.getLast?_cons], ?_⟩⟩
      intro i hi
      by_cases hi0 : i = 0
      · simp [hi0]; exact hEdge
      ·
        have hi' : i - 1 < p.length - 1 :=
          Nat.pred_lt_pred_iff.mpr hi
        exact hE (i - 1) hi'

/-
==============================
Fixed Sri Yantra Operator
==============================
-/

/-- Fixed Sri Yantra shaping operator -/
def SriYantra (core : CognitiveTool) (T : CognitiveTool) : CognitiveTool :=
Sharpen core T

/-- Iterated meditation using a fixed Sri Yantra -/
def iterateSriYantra (core : CognitiveTool) : ℕ → CognitiveTool → CognitiveTool :=
iterateSharpen (SriYantra Counters Sharpen core)

/-- Sri Yantra preserves safety under iteration -/
theorem sri_yantra_preserves_safety
  (δ : Disturbance)
  (core T : CognitiveTool)
  (hCore : ∀ S, Sharpens Counters S (SriYantra Counters Sharpen core S))
  (hSafe : MentallySafe Counters Destabilizing δ T) :
  ∀ n, MentallySafe Counters Destabilizing δ (iterateSriYantra Counters Sharpen core n T) :=
by
  intro n
  exact yantra_preserves_safety
    Counters Destabilizing δ
    (SriYantra Counters Sharpen core)
    hCore T hSafe n
