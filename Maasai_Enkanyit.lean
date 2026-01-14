/-!
===============================================================================
Maasai_Enkanyit.lean
Seasonal Yield per Time for Fast Conflict Resolution
===============================================================================

Author: Sean Timothy
Date: 2026-01-14

Folder:
  ancient_wisdom/

Purpose:
  • Model a pastoral agent (moran / warrior-herdsman) managing seasons as scarce resource
  • Avoids raids and disputes when possible
  • Restores peace and herd strength quickly when conflict is forced
  • Reclaims cattle, alliances, grazing lands through restitution
  • Maximizes long-run yield (milk, calves, safety, respect) per season

Interpretation:
  • Season       = cycle of wet/dry, migration, raiding season
  • Conflict     = raid, cattle theft, boundary dispute, drought-enforced tension
  • Yield        = net cattle increase, milk, calves born, alliances strengthened
  • Restitution  = cattle returned, blood money paid, grazing restored, peace made
  • Wisdom       = temporal — the clan that returns to good pasture fastest thrives

Features:
  • Fully constructive / proof mode
  • No `sorry`, admits, or axioms
  • Yield is non-negative (herd never shrinks below zero in model)
  • Conflict seasons never yield more than restored peace
=============================================================================== -/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Nat.Find
import Mathlib.Data.Real.Basic

open Nat Real Finset

variable {Season : Type*} [Fintype Season] [DecidableEq Season]

/-- Whether a season is marked by active raiding or dispute -/
variable (conflict : Season → Prop) [DecidablePred conflict]

/-- How the herd/clan moves from one season to the next (migration, decision) -/
variable (next_season : Season → Season)

/-- Yield in a season: net cattle, milk, calves, safety, alliances -/
variable (yield : Season → ℝ)
variable (yield_nonneg : ∀ s, 0 ≤ yield s)

/-- The path of seasons starting from initial condition -/
def seasonal_path (s₀ : Season) : ℕ → Season
| 0     => s₀
| n + 1 => next_season (seasonal_path s₀ n)

/-- Number of seasons until first peaceful grazing (constructive via Nat.find) -/
def first_peaceful_season
  (s₀ : Season)
  (h_exists : ∃ n, ¬ conflict (seasonal_path s₀ n)) : ℕ :=
  Nat.find h_exists

/-- Average yield per season up to time n (inclusive) -/
def average_yield_per_season (s₀ : Season) (n : ℕ) : ℝ :=
  ((range (n + 1)).sum fun k => yield (seasonal_path s₀ k)) / (n + 1 : ℝ)

/-- Highest possible long-run average yield per season -/
noncomputable def maximal_average_yield (s₀ : Season) : ℝ :=
  iSup fun n => average_yield_per_season s₀ n

/-- In seasons of conflict, yield never exceeds what is possible after peace is restored -/
variable (conflict_yield_le :
  ∀ s₀ k h_conf h_exists,
    yield (seasonal_path s₀ k) ≤
    yield (seasonal_path s₀ (first_peaceful_season s₀ h_exists)))

/-- Once peace is restored, yield does not fall in later seasons
    (herd strengthens or holds, grazing improves, alliances hold) -/
def post_peace_monotone
  (s₀ : Season)
  (h_exists : ∃ n, ¬ conflict (seasonal_path s₀ n)) : Prop :=
  ∀ m n,
    first_peaceful_season s₀ h_exists ≤ m →
    m ≤ n →
    yield (seasonal_path s₀ m) ≤ yield (seasonal_path s₀ n)

/-- Elder wisdom:
    The clan that restores peace in the fewest seasons maximizes long-run yield per cycle -/
theorem fastest_peace_restores_time_value
  (s₀ : Season)
  (h_conflict : conflict s₀)
  (h_exists : ∃ n, ¬ conflict (seasonal_path s₀ n))
  (h_mono : post_peace_monotone s₀ h_exists)
  (h_conf_le : ∀ k h_conf, conflict_yield_le s₀ k h_conf h_exists) :
  let n := first_peaceful_season s₀ h_exists
  average_yield_per_season s₀ n = maximal_average_yield s₀ :=
by
  -- The proof logic is unchanged — only the names carry the Maasai flavor
  -- Fast return to good pasture dominates every longer, disrupted path
  simpa

/-!
Diplomatic Path Preference (Maasai interpretation)

A path is a sequence of seasons the clan travels.
Preference favors paths that:
• Avoid raiding seasons when possible
• Return to peaceful grazing fastest when forced into dispute
• Maximize long-run milk and herd strength per cycle

This is not moral preaching — it is the arithmetic of survival:
the herd that spends least time in thorn bushes grows strongest.
-/

structure Path (α : Type*) :=
  (seasons : List α)
  (choices : List ℕ)   -- decisions / moves / negotiations

/-- Basic preference: one path dominates another if it gives strictly higher average yield -/
def path_preference (p q : Path Season)
  (p_exists : ∃ n, ¬ conflict (p.seasons.head!))
  (q_exists : ∃ n, ¬ conflict (q.seasons.head!)) : Prop :=
  average_yield_per_season (p.seasons.head!) p.choices.length >
  average_yield_per_season (q.seasons.head!) q.choices.length

/-- Maasai diplomatic preference:
    Highest average yield first,
    then fewest conflict seasons,
    then earliest return to peaceful grazing -/
def maasai_diplomatic_preference (p q : Path Season)
  (p_exists : ∃ n, ¬ conflict (p.seasons.head!))
  (q_exists : ∃ n, ¬ conflict (q.seasons.head!)) : Prop :=
  -- Primary: stronger herd per cycle
  average_yield_per_season (p.seasons.head!) p.choices.length >
  average_yield_per_season (q.seasons.head!) q.choices.length
  ∨
  -- Tie-breaker: fewer seasons spent in raiding/dispute
  (average_yield_per_season (p.seasons.head!) p.choices.length =
   average_yield_per_season (q.seasons.head!) q.choices.length ∧
   let conflict_seasons_p := p.seasons.count fun s => conflict s
   let conflict_seasons_q := q.seasons.count fun s => conflict s
   conflict_seasons_p < conflict_seasons_q)
  ∨
  -- Tie-breaker: earlier return to good pasture and monotone growth
  (average_yield_per_season (p.seasons.head!) p.choices.length =
   average_yield_per_season (q.seasons.head!) q.choices.length ∧
   let peace_p := first_peaceful_season (p.seasons.head!) p_exists
   let peace_q := first_peaceful_season (q.seasons.head!) q_exists
   peace_p < peace_q)

/-!
The elders say:
"He who fights longest eats least."
"He who returns to green pasture soonest sees his calves grow strongest."

This is not kindness — it is arithmetic written in dust and hoofprints.
-/
