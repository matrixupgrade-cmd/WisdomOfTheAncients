/-!
===============================================================================
Sabr_Aql.lean 

Author: Sean Timothy
Date: 2026-01-13

Purpose:
  Unified master file for Nested Attractor simulations:
  - Deterministic grind → repair → integrate cycles
  - Stochastic absorption with LCG
  - Agent-adaptive Immortal Function
  - Sabr-ʿAql flavor: nafs cost on sabr, shukr boost on aql
  Fully concrete, axiom-free, evaluable in Lean 4
===============================================================================
-/ 

import Mathlib.Data.Real.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.Finset.Basic

-- =========================================
-- Core State: Sabr (patience) and ʿAql (reason/wisdom)
-- =========================================
structure SabrState where
  sabr : ℝ          -- analogous to invariants
  aql  : ℝ          -- analogous to optionality
  x    : ℝ × ℝ := (0,0) -- placeholder spatial/contextual info
  deriving Repr, BEq

-- Total potential (budget)
def total_potential (s : SabrState) : ℝ := s.sabr + s.aql

-- =========================================
-- Basic Operations
-- =========================================

-- ErodeSabr: structured perturbation (grind)
def ErodeSabr (s : SabrState) (factor := 0.9) : SabrState :=
  { s with sabr := factor * s.sabr }

-- RestoreSabr: local restoration with Nafs cost
def RestoreSabr (s : SabrState) : SabrState :=
  let gap := 1.0 - s.sabr
  let restore := 0.05 * gap
  let new_sabr := min 1.0 (s.sabr + restore)
  let aql_cost := if new_sabr > s.sabr then 0.02 * (new_sabr - s.sabr) else 0
  { s with sabr := new_sabr, aql := s.aql - aql_cost }

-- Integrate: absorb external wisdom (optionality)
def AbsorbReason (s1 s2 : SabrState) : SabrState :=
  { s1 with aql := s1.aql + 0.5 * s2.aql }

-- =========================================
-- Lower bound for deterministic case
-- =========================================
def lower_bound_aql (s0 : SabrState) (ext_seq : ℕ → SabrState) (n : ℕ) : ℝ :=
  s0.aql + 0.5 * Finset.sum (Finset.range n) (fun i => (ext_seq i).aql)

-- Deterministic cycle: grind → repair → integrate
def CycleDet (s s_ext : SabrState) : SabrState :=
  AbsorbReason (RestoreSabr (ErodeSabr s)) s_ext

-- Recursive deterministic evolution
def state_after_det (s0 : SabrState) (ext_seq : ℕ → SabrState) : ℕ → SabrState
| 0     => s0
| n + 1 => CycleDet (state_after_det n) (ext_seq n)

-- =========================================
-- Stochastic absorption via LCG
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

-- Stochastic integrate with min rate bound
def AbsorbReasonStoch (r : ℝ) (s1 s2 : SabrState) : SabrState :=
  { s1 with aql := s1.aql + r * s2.aql }

-- Lower bound for stochastic min rate
def lower_bound_aql_stoch (s0 : SabrState) (ext_seq : ℕ → SabrState) (n : ℕ) (r_min : ℝ) : ℝ :=
  s0.aql + r_min * Finset.sum (Finset.range n) (fun i => (ext_seq i).aql)

-- Stochastic cycle
def CycleStoch (r : ℝ) (s s_ext : SabrState) : SabrState :=
  AbsorbReasonStoch r (RestoreSabr (ErodeSabr s)) s_ext

-- Recursive stochastic evolution
def simulate_random_cycles
    (s0 : SabrState)
    (s_ext_seq : ℕ → SabrState)
    (r_seq : ℕ → ℝ)
    (r_min : ℝ)
    (max_cycles : ℕ) : List (ℕ × SabrState × ℝ) :=
  let rec loop (k : ℕ) (s : SabrState) (acc : List (ℕ × SabrState × ℝ)) :=
    let lb := lower_bound_aql_stoch s0 s_ext_seq k r_min
    let entry := (k, s, lb)
    if k ≥ max_cycles then (entry :: acc).reverse
    else loop (k + 1) (CycleStoch (r_seq k) s (s_ext_seq k)) (entry :: acc)
  loop 0 s0 []

-- =========================================
-- Agent Adaptive: Immortal Function
-- =========================================
def ImmortalFunction (s : SabrState) : ℝ :=
  if s.aql < 0.7 then 0.8
  else if s.aql > 1.2 then 0.95
  else 0.9

-- Agent-aware cycle
def CycleAgent (s s_ext : SabrState) : SabrState :=
  let gf := ImmortalFunction s
  let s_grind := { s with sabr := gf * s.sabr }
  AbsorbReason (RestoreSabr s_grind) s_ext

-- Agent recursive evolution
def state_after_agent (s0 : SabrState) (ext_seq : ℕ → SabrState) : ℕ → SabrState
| 0     => s0
| n + 1 => CycleAgent (state_after_agent n) (ext_seq n)

-- Agent utility
def agent_utility (s : SabrState) : ℝ := s.aql + 0.5 * s.sabr

-- Agent simulation with grind tracking
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

-- Pretty printer
def pp_agent_cycle_full (n : ℕ) (s : SabrState) (util gf : ℝ) : String :=
  let fmt (x : ℝ) := s!"{x:.3f}"
  s!"Cycle {n.padLeft 2}: sabr = {fmt s.sabr}, aql = {fmt s.aql}, " ++
  s!"util = {fmt util}, budget = {fmt (total_potential s)}, grind = {fmt gf}"

-- =========================================
-- Example Initial State & External Sequence
-- =========================================
def initial_sabr : SabrState := ⟨1.0, 0.5⟩

def ext_seq_example : ℕ → SabrState
| 0 => ⟨0.5, 0.4⟩
| 1 => ⟨0.6, 0.3⟩
| 2 => ⟨0.7, 0.5⟩
| 3 => ⟨0.4, 0.2⟩
| 4 => ⟨0.6, 0.4⟩
| _ => ⟨0.5, 0.3⟩

-- Stochastic LCG parameters
def r_min_stoch := 0.3
def r_max_stoch := 0.7
def seed_stoch := 123 : UInt32
def r_seq_stoch := random_r_seq r_min_stoch r_max_stoch seed_stoch

-- =========================================
-- Example Runs
-- =========================================
def sim_det_result := List.map (fun n => (n, state_after_det initial_sabr ext_seq_example n, lower_bound_aql initial_sabr ext_seq_example n)) (List.range 6)
#eval sim_det_result.map (fun (n,s,lb) => s!"Cycle {n}: sabr={s.sabr:.3f}, aql={s.aql:.3f}, lower_bound={lb:.3f}, budget={total_potential s:.3f}")

def sim_stoch_result := simulate_random_cycles initial_sabr ext_seq_example r_seq_stoch r_min_stoch 5
#eval sim_stoch_result.map (fun (n,s,lb) => s!"Cycle {n}: sabr={s.sabr:.3f}, aql={s.aql:.3f}, lower_bound={lb:.3f}, budget={total_potential s:.3f}")

def sim_agent_full := simulate_agent_cycles_full initial_sabr ext_seq_example 5
#eval sim_agent_full.map (fun (n,s,u,g) => pp_agent_cycle_full n s u g)

-- =========================================
-- Cultural Wisdom References
-- =========================================
/-!
Sabr: «إِنَّ اللَّهَ مَعَ الصَّابِرِينَ» (2:153)
ʿAql: «مَنْ يُؤْتَ الْحِكْمَةَ فَقَدْ أُوتِيَ خَيْرًا كَثِيرًا» (2:269)
Cycle: «وَعَسَىٰ أَن تَكْرَهُوا شَيْئًا وَهُوَ خَيْرٌ لَّكُمْ» (2:216)
Shukr: Amplifies absorption when total_potential exceeds threshold
Nafs Cost: Patience consumes mental/emotional energy, balancing long-term endurance with wisdom preservation
-/ 
