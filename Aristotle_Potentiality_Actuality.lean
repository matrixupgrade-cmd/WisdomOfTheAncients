/-
===============================================================================
Aristotle_Potentiality_Actuality.lean

"The Doctrine of Potentiality and Actuality in Choice"

In every moment of decision, the world stands between what is and what may be.
Aristotle teaches us: all change is the actualization of what was potential.
Yet the wise man does not pursue actuality so fiercely that he annihilates potentiality;
he reinforces the realized good while preserving the capacity to turn toward a greater one.

Each course of action bears two measures —
actus : the realized strength already achieved,
potentia : the latent flexibility that remains.

The prudent update strengthens actus without erasing potentia below a prudent threshold.
The selection always honors the highest actuality,
yet the basin of options continues to carry the seed of future excellence.

Author: Sean Timothy & VulcanLogic Architect
Date: 2026-01-10
===============================================================================
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.Option

open Finset

variable {Course : Type*}

/-- An option for action: has realized power (actus) and latent flexibility (potentia) -/
structure CourseOption where
  course   : Course
  actus    : ℝ
  potentia : { x : ℝ // 0 ≤ x }

/-- The finite basin of available options, with a current selection -/
structure UltimateChoice where
  basin  : Finset CourseOption
  select : CourseOption
  selection_property :
    select ∈ basin ∧ ∀ o ∈ basin, o.actus ≤ select.actus

namespace UltimateChoice

instance : LE CourseOption := ⟨fun a b => a.actus ≤ b.actus⟩
instance : DecidableRel ((· ≤ ·) : CourseOption → CourseOption → Prop) := inferInstance

instance : LinearOrder CourseOption :=
{ le := fun a b => a.actus ≤ b.actus,
  le_refl := fun _ => le_refl _,
  le_trans := fun _ _ _ => le_trans,
  le_antisymm := fun a b h₁ h₂ => by simp [CourseOption.actus] at *; exact le_antisymm h₁ h₂,
  le_total := fun a b => le_total a.actus b.actus,
  decidableLE := inferInstance }

def mk (basin : Finset CourseOption) (hne : basin.Nonempty) : UltimateChoice :=
  let sel := basin.max' hne
  { basin := basin, select := sel, selection_property := ⟨max'_mem _ _, max'_le _ _⟩ }

def max_actus (w : UltimateChoice) : ℝ := w.select.actus
def select_potentia (w : UltimateChoice) : ℝ := w.select.potentia

end UltimateChoice

/-- Reflexive update: strengthens actus while preserving a prudent fraction of potentia -/
structure ReflexiveUpdate where
  update_actus     : CourseOption → ℝ
  update_potentia  : CourseOption → { x : ℝ // 0 ≤ x }
  non_decreasing_actus :
    ∀ w : UltimateChoice, w.select.actus ≤ update_actus w.select
  preserves_relative_order :
    ∀ w : UltimateChoice, ∀ o ∈ w.basin, update_actus o ≤ update_actus w.select
  preserves_potentia_threshold_all :
    ∀ w : UltimateChoice, ∀ o ∈ w.basin,
      (update_potentia w o : ℝ) ≥ (o.potentia : ℝ) * 1/2

namespace AristotelianMetaOptionality

variable (r : ReflexiveUpdate)

/-- Non-empty image of basin after reflexive update -/
private lemma updated_basin_nonempty (w : UltimateChoice) (hw : w.basin.Nonempty) :
    (w.basin.image fun o => { o with actus := r.update_actus o, potentia := r.update_potentia o }).Nonempty :=
  hw.casesOn fun o ho => ⟨_, mem_image_of_mem _ ho⟩

/-- Maximum actus increases or stays the same; potentia of selected option preserved ≥ 1/2 -/
theorem max_actus_non_decreasing_with_potentia_preserved
    (w : UltimateChoice) (hw : w.basin.Nonempty) :
    let updated := w.basin.image fun o => { o with actus := r.update_actus o, potentia := r.update_potentia o }
    let new_w := UltimateChoice.mk updated (updated_basin_nonempty r w hw)
    w.max_actus ≤ new_w.max_actus ∧
    new_w.select_potentia ≥ w.select.potentia * (1/2) := by
  let updated := w.basin.image fun o => { o with actus := r.update_actus o, potentia := r.update_potentia o }
  let new_w := UltimateChoice.mk updated (updated_basin_nonempty r w hw)
  constructor
  · calc w.max_actus
      = w.select.actus               := rfl
      _ ≤ r.update_actus w.select    := r.non_decreasing_actus w
      _ ≤ new_w.select.actus         := max'_le _ _ (mem_image_of_mem _ w.selection_property.1)
      _ = new_w.max_actus            := rfl
  · exact r.preserves_potentia_threshold_all w w.select w.selection_property.1

/-- Reflexive update preserves at least half potentia for all options in the basin -/
theorem prudent_update_preserves_capacity_for_all
    (w : UltimateChoice) (hw : w.basin.Nonempty) :
    let updated := w.basin.image fun o => { o with actus := r.update_actus o, potentia := r.update_potentia o }
    ∀ o ∈ updated, (o.potentia : ℝ) ≥ (1/2) * ((w.basin.filter (fun x => x.course = o.course)).sup (fun x => (x.potentia : ℝ))) := by
  intros updated o ho
  rcases mem_image.1 ho with ⟨orig, h_mem, rfl⟩
  exact r.preserves_potentia_threshold_all w orig h_mem

end AristotelianMetaOptionality
