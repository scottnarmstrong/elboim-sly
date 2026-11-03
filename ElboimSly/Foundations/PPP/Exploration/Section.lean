/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.PPP.Finite
public import ElboimSly.Foundations.PPP.Giry
import Mathlib

/-!
# Measurability of sections

Measurability of sections.

For a jointly measurable `Z ⊆ Θ × S`, the maps `(θ, ν) ↦ τ(ν)(Z_θ)`, `(θ, ν) ↦ τ(ν)|_{Z_θ}` and
`(θ, ν) ↦ ∫ f(θ, x) τ(ν)(dx)` are measurable on `Θ × Measure S`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace ElboimSly

variable {S Θ : Type*} [MeasurableSpace S] [MeasurableSpace Θ] (μ : Measure S) [SigmaFinite μ]

theorem measurable_tau_section_cell (k : ℕ) {Z : Set (Θ × S)} (hZ : MeasurableSet Z) :
    Measurable fun p : Θ × Measure S => tau μ p.2 (Prod.mk p.1 ⁻¹' Z ∩ ppartition μ k) := by
  classical
  have hQ := measurableSet_ppartition μ k
  have hfin : ∀ p : Θ × Measure S, tau μ p.2 (ppartition μ k) < ∞ :=
    fun p => tau_mem_lfSet μ p.2 k
  have hτ : Measurable fun p : Θ × Measure S => tau μ p.2 :=
    (measurable_tau μ).comp measurable_snd
  induction Z, hZ using MeasurableSpace.induction_on_inter generateFrom_prod.symm
      (IsPiSystem.prod MeasurableSpace.isPiSystem_measurableSet MeasurableSpace.isPiSystem_measurableSet) with
  | empty => simp
  | basic t ht =>
    obtain ⟨T, hT, B, hB, rfl⟩ := ht
    have hT : MeasurableSet T := hT
    have hB : MeasurableSet B := hB
    have : (fun p : Θ × Measure S => tau μ p.2 (Prod.mk p.1 ⁻¹' (T ×ˢ B) ∩ ppartition μ k)) =
        fun p => if p.1 ∈ T then tau μ p.2 (B ∩ ppartition μ k) else 0 := by
      funext p
      by_cases hp : p.1 ∈ T <;> simp [hp, Set.preimage]
    rw [this]
    exact Measurable.ite (measurable_fst hT)
      ((Measure.measurable_coe (hB.inter hQ)).comp hτ) measurable_const
  | compl t ht ih =>
    have : (fun p : Θ × Measure S => tau μ p.2 (Prod.mk p.1 ⁻¹' tᶜ ∩ ppartition μ k)) =
        fun p => tau μ p.2 (ppartition μ k) - tau μ p.2 (Prod.mk p.1 ⁻¹' t ∩ ppartition μ k) := by
      funext p
      have h1 : Prod.mk p.1 ⁻¹' tᶜ ∩ ppartition μ k =
          ppartition μ k \ (Prod.mk p.1 ⁻¹' t ∩ ppartition μ k) := by
        ext x; simp [and_comm]
      rw [h1, measure_sdiff Set.inter_subset_right
        (((measurable_prodMk_left ht).inter hQ).nullMeasurableSet)
        (ne_top_of_le_ne_top (hfin p).ne (measure_mono Set.inter_subset_right))]
    rw [this]
    exact ((Measure.measurable_coe hQ).comp hτ).sub ih
  | iUnion f hd hf ih =>
    have : (fun p : Θ × Measure S => tau μ p.2 (Prod.mk p.1 ⁻¹' (⋃ i, f i) ∩ ppartition μ k)) =
        fun p => ∑' i, tau μ p.2 (Prod.mk p.1 ⁻¹' f i ∩ ppartition μ k) := by
      funext p
      have h1 : Prod.mk p.1 ⁻¹' (⋃ i, f i) ∩ ppartition μ k =
          ⋃ i, (Prod.mk p.1 ⁻¹' f i ∩ ppartition μ k) := by
        ext x; simp [and_comm]
      rw [h1, measure_iUnion]
      · intro i j hij
        exact ((hd hij).preimage (Prod.mk p.1)).mono Set.inter_subset_left Set.inter_subset_left
      · exact fun i => (measurable_prodMk_left (hf i)).inter hQ
    rw [this]
    exact Measurable.tsum ih

/-- Measurability of sections (a). -/
theorem measurable_tau_section {Z : Set (Θ × S)} (hZ : MeasurableSet Z) :
    Measurable fun p : Θ × Measure S => tau μ p.2 (Prod.mk p.1 ⁻¹' Z) := by
  have : (fun p : Θ × Measure S => tau μ p.2 (Prod.mk p.1 ⁻¹' Z)) =
      fun p => ∑' k, tau μ p.2 (Prod.mk p.1 ⁻¹' Z ∩ ppartition μ k) := by
    funext p
    have h1 : Prod.mk p.1 ⁻¹' Z = ⋃ k, (Prod.mk p.1 ⁻¹' Z ∩ ppartition μ k) := by
      rw [← Set.inter_iUnion, iUnion_ppartition, Set.inter_univ]
    conv_lhs => rw [h1]
    rw [measure_iUnion]
    · intro i j hij
      exact (pairwise_disjoint_ppartition μ hij).mono Set.inter_subset_right
        Set.inter_subset_right
    · exact fun k => (measurable_prodMk_left hZ).inter (measurableSet_ppartition μ k)
  rw [this]
  exact Measurable.tsum fun k => measurable_tau_section_cell μ k hZ

/-- Measurability of sections (b). -/
theorem measurable_tau_restrict_section {Z : Set (Θ × S)} (hZ : MeasurableSet Z) :
    Measurable fun p : Θ × Measure S => (tau μ p.2).restrict (Prod.mk p.1 ⁻¹' Z) := by
  rw [measurable_measure_iff]
  intro B hB
  have : (fun p : Θ × Measure S => (tau μ p.2).restrict (Prod.mk p.1 ⁻¹' Z) B) =
      fun p => tau μ p.2 (Prod.mk p.1 ⁻¹' (Z ∩ (Set.univ ×ˢ B))) := by
    funext p
    rw [Measure.restrict_apply hB]
    congr 1
    ext x; simp [and_comm]
  rw [this]
  exact measurable_tau_section μ (hZ.inter (MeasurableSet.univ.prod hB))

end ElboimSly
