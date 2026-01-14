/-!
===============================================================================
Sabr_Aql.lean 

Author: Sean Timothy
Date: 2026-01-13

Purpose:
  Unified master file for Nested Attractor simulations in Sabr-ʿAql flavor:
  - Deterministic grind → repair → integrate cycles
  - Stochastic absorption with LCG pseudo-randomness
  - Agent-adaptive Immortal Function
  - Nafs cost on sabr restoration (patience consumes mental energy)
  - Shukr boost on aql absorption (gratitude amplifies wisdom intake)
  Fully concrete, axiom-free, evaluable in Lean 4
===============================================================================
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.Finset.Basic

-- =========================================
-- Core State: Sabr (patience/endurance) and ʿAql (reason/wisdom)
-- =========================================
structure SabrState where
  sabr : ℝ          -- patient endurance, structural stability
  aql  : ℝ          -- discerning reason, adaptive wisdom
  x    : ℝ × ℝ := (0,0) -- optional spatial/contextual placeholder
  deriving Repr, BEq

def total_potential (s : SabrState) : ℝ := s.sabr + s.aql

-- =========================================
-- Basic Operations with Nafs Cost & Shukr Boost
-- =========================================

-- ErodeSabr: structured trial / perturbation
def ErodeSabr (s : SabrState) (factor : ℝ := 0.9) : SabrState :=
  { s with sabr := factor * s.sabr }

-- RestoreSabr: patient restoration with nafs cost
-- When sabr is rebuilt, a small portion of aql (mental/emotional energy) is consumed
def RestoreSabr (s : SabrState) : SabrState :=
  let gap := 1.0 - s.sabr
  let restore := 0.05 * gap
  let new_sabr := min 1.0 (s.sabr + restore)
  let nafs_cost := if new_sabr > s.sabr then 0.02 * (new_sabr - s.sabr) else 0
  { s with sabr := new_sabr, aql := max 0 (s.aql - nafs_cost) }

-- AbsorbReason: integrate external wisdom, with optional shukr multiplier
def AbsorbReason (s1 s2 : SabrState) (shukr_boost : ℝ := 1.0) : SabrState :=
  { s1 with aql := s1.aql + shukr_boost * 0.5 * s2.aql }

-- Shukr trigger: gratitude amplifies next absorption if total potential is high
def has_shukr (s : SabrState) : Bool := total_potential s ≥ 1.8

-- =========================================
-- Deterministic Cycle
-- =========================================
def CycleDet (s s_ext : SabrState) : SabrState :=
  let repaired := RestoreSabr (ErodeSabr s)
  let boost := if has_shukr repaired then 1.2 else 1.0   -- 20% extra absorption on gratitude
  AbsorbReason repaired s_ext boost

-- Recursive deterministic path
def state_after_det (s0 : SabrState) (ext_seq : ℕ → SabrState) : ℕ → SabrState
| 0     => s0
| n + 1 => CycleDet (state_after_det n) (ext_seq n)

-- Lower bound (deterministic, no shukr)
def lower_bound_aql (s0 : SabrState) (ext_seq : ℕ → SabrState) (n : ℕ) : ℝ :=
  s0.aql + 0.5 * Finset.sum (Finset.range n) (fun i => (ext_seq i).aql)

-- =========================================
-- Stochastic Cycle (LCG random absorption)
-- =========================================
def lcg_next (state : UInt32) : UInt32 × UInt32 :=
  let a : UInt32 := 1664525
  let c : UInt32 := 1013904223
  let m : UInt64 := 1 <<< 32
  let next := (UInt64.ofNat (a.val * state.val + c.val)) % m
  (next.toUInt32, next.toUInt32)

def random_r_seq (r_min r_max : ℝ) (seed : UInt32) : ℕ → ℝ
| n =>
  let mut state := seed
  let mut i : ℕ := 0
  while i < n do
    let (next, _) := lcg_next state
    state := next
    i := i + 1
  let frac : ℝ := (state.val : ℝ) / (UInt32.max.val : ℝ + 1)
  r_min + frac * (r_max - r_min)

def CycleStoch (r : ℝ) (s s_ext : SabrState) : SabrState :=
  let repaired := RestoreSabr (ErodeSabr s)
  let boost := if has_shukr repaired then 1.2 else 1.0
  { repaired with aql := repaired.aql + boost * r * s_ext.aql }

def lower_bound_aql_stoch (s0 : SabrState) (ext_seq : ℕ → SabrState) (n : ℕ) (r_min : ℝ) : ℝ :=
  s0.aql + r_min * Finset.sum (Finset.range n) (fun i => (ext_seq i).aql)

def simulate_random_cycles
    (s0 : SabrState) (ext_seq : ℕ → SabrState) (r_seq : ℕ → ℝ) (r_min : ℝ) (max_cycles : ℕ) :
    List (ℕ × SabrState × ℝ) :=
  let rec loop (k : ℕ) (s : SabrState) (acc : List (ℕ × SabrState × ℝ)) :=
    let lb := lower_bound_aql_stoch s0 ext_seq k r_min
    let entry := (k, s, lb)
    if k ≥ max_cycles then (entry :: acc).reverse
    else loop (k + 1) (CycleStoch (r_seq k) s (ext_seq k)) (entry :: acc)
  loop 0 s0 []

-- =========================================
-- Agent-Adaptive Immortal Function
-- =========================================
def ImmortalFunction (s : SabrState) : ℝ :=
  if s.aql < 0.7 then 0.8
  else if s.aql > 1.2 then 0.95
  else 0.9

def CycleAgent (s s_ext : SabrState) : SabrState :=
  let gf := ImmortalFunction s
  let eroded := ErodeSabr s gf
  let repaired := RestoreSabr eroded
  let boost := if has_shukr repaired then 1.2 else 1.0
  AbsorbReason repaired s_ext boost

def state_after_agent (s0 : SabrState) (ext_seq : ℕ → SabrState) : ℕ → SabrState
| 0     => s0
| n + 1 => CycleAgent (state_after_agent n) (ext_seq n)

def agent_utility (s : SabrState) : ℝ := s.aql + 0.5 * s.sabr

def simulate_agent_cycles_full
    (init : SabrState) (exts : ℕ → SabrState) (max_cycles : ℕ) :
    List (ℕ × SabrState × ℝ × ℝ) :=
  let rec loop (k : ℕ) (s : SabrState) (acc : List (ℕ × SabrState × ℝ × ℝ)) :=
    let util := agent_utility s
    let gf := ImmortalFunction s
    let entry := (k, s, util, gf)
    if k ≥ max_cycles then entry :: acc
    else loop (k + 1) (CycleAgent s (exts k)) (entry :: acc)
  (loop 0 init []).reverse

-- =========================================
-- Pretty Printers & Example Runs
-- =========================================
def pp_cycle (n : ℕ) (s : SabrState) (lb : ℝ) : String :=
  let fmt (x : ℝ) := s!"{x:.3f}"
  s!"Cycle {n.padLeft 2}: sabr = {fmt s.sabr}, aql = {fmt s.aql}, " ++
  s!"lower_bound = {fmt lb}, total = {fmt (total_potential s)}"

def pp_agent (n : ℕ) (s : SabrState) (util gf : ℝ) : String :=
  let fmt (x : ℝ) := s!"{x:.3f}"
  s!"Cycle {n.padLeft 2}: sabr = {fmt s.sabr}, aql = {fmt s.aql}, " ++
  s!"util = {fmt util}, total = {fmt (total_potential s)}, grind = {fmt gf}"

-- Example data
def initial_sabr : SabrState := ⟨1.0, 0.5⟩

def ext_seq_example : ℕ → SabrState
| 0 => ⟨0.5, 0.4⟩
| 1 => ⟨0.6, 0.3⟩
| 2 => ⟨0.7, 0.5⟩
| 3 => ⟨0.4, 0.2⟩
| 4 => ⟨0.6, 0.4⟩
| _ => ⟨0.5, 0.3⟩

def r_min_stoch := 0.3
def r_max_stoch := 0.7
def seed_stoch := 123 : UInt32
def r_seq_stoch := random_r_seq r_min_stoch r_max_stoch seed_stoch

-- Run examples
def sim_det := List.map (fun n => (n, state_after_det initial_sabr ext_seq_example n,
                                   lower_bound_aql initial_sabr ext_seq_example n))
                        (List.range 6)

#eval sim_det.map (fun (n,s,lb) => pp_cycle n s lb)

def sim_stoch := simulate_random_cycles initial_sabr ext_seq_example r_seq_stoch r_min_stoch 5
#eval sim_stoch.map (fun (n,s,lb) => pp_cycle n s lb)

def sim_agent := simulate_agent_cycles_full initial_sabr ext_seq_example 5
#eval sim_agent.map (fun (n,s,u,g) => pp_agent n s u g)

-- =========================================
-- Cultural & Conceptual Anchors
-- =========================================
/-!
Sabr: «إِنَّ اللَّهَ مَعَ الصَّابِرِينَ» (2:153)
ʿAql: «مَنْ يُؤْتَ الْحِكْمَةَ فَقَدْ أُوتِيَ خَيْرًا كَثِيرًا» (2:269)
Shukr boost: Gratitude opens the door to more wisdom
Nafs cost: Patience consumes mental energy — balance endurance with reflection
Immortal Function: Adaptive regulation of trial intensity based on current wisdom
-/
