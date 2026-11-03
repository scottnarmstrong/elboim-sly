/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.StrongApprox.StrongMarkov1d
public import Mathlib

/-!
# Measurability with respect to the stopped `σ`-algebra

Measurability of the embedding (c) (Part II).

For a stopping time `ρ` of the natural filtration of a standard real Brownian motion `β`, both
`ρ` and the stopped value `β(ρ)` are measurable for the stopped `σ`-algebra `ℱ_ρ`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace ElboimSly.StrongApprox

open ElboimSly.Brownian

lemma measurable_value_aux {Ω : Type*} [m : MeasurableSpace Ω] {Z : ℝ≥0 → Ω → ℝ}
    (hc : ∀ ω, Continuous fun s => Z s ω) (hZ : ∀ s, Measurable (Z s)) {σ : Ω → ℝ≥0}
    (hσ : Measurable σ) : Measurable fun ω => Z (σ ω) ω :=
  (measurable_uncurry_of_continuous_of_measurable hc hZ).comp (hσ.prodMk measurable_id)

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {β : ℝ≥0 → Ω → ℝ}

lemma measurable_self_stopped (hF : ∀ t, realFiltration β t ≤ mΩ) {ρ : Ω → ℝ≥0∞}
    (hρ : ∀ t : ℝ≥0, MeasurableSet[realFiltration β t] {ω | ρ ω ≤ t}) :
    Measurable[stoppedSigma (realFiltration β) ρ hρ] ρ := by
  refine measurable_of_Iic fun x => ?_
  induction x using ENNReal.recTopCoe with
  | top => simp
  | coe s =>
    refine (measurableSet_stoppedSigma).2 ⟨hF s _ (hρ s), fun t => ?_⟩
    rcases le_total s t with h | h
    · have : ρ ⁻¹' Set.Iic (s : ℝ≥0∞) ∩ {ω | ρ ω ≤ t} = {ω | ρ ω ≤ s} := by
        ext ω
        simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_Iic, Set.mem_ofPred_eq]
        exact ⟨fun h' => h'.1, fun h' => ⟨h', h'.trans (by exact_mod_cast h)⟩⟩
      rw [this]
      exact realFiltration_mono β h _ (hρ s)
    · have : ρ ⁻¹' Set.Iic (s : ℝ≥0∞) ∩ {ω | ρ ω ≤ t} = {ω | ρ ω ≤ t} := by
        ext ω
        simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_Iic, Set.mem_ofPred_eq]
        exact ⟨fun h' => h'.2, fun h' => ⟨h'.trans (by exact_mod_cast h), h'⟩⟩
      rw [this]
      exact hρ t

lemma measurable_toNNReal_stopped (hF : ∀ t, realFiltration β t ≤ mΩ) {ρ : Ω → ℝ≥0∞}
    (hρ : ∀ t : ℝ≥0, MeasurableSet[realFiltration β t] {ω | ρ ω ≤ t}) :
    Measurable[stoppedSigma (realFiltration β) ρ hρ] fun ω => (ρ ω).toNNReal :=
  ENNReal.measurable_toNNReal.comp (measurable_self_stopped hF hρ)

lemma measurable_value_stopped (hproc : IsProcess β) {ρ : Ω → ℝ≥0∞}
    (hρ : ∀ t : ℝ≥0, MeasurableSet[realFiltration β t] {ω | ρ ω ≤ t}) :
    Measurable[stoppedSigma (realFiltration β) ρ hρ] fun ω => β (ρ ω).toNNReal ω := by
  have hF : ∀ t, realFiltration β t ≤ mΩ := realFiltration_le hproc.2
  have hρm : Measurable ρ := measurable_of_stopping hproc.2 hρ
  intro Γ hΓ
  refine (measurableSet_stoppedSigma).2 ⟨?_, fun t => ?_⟩
  · exact (hproc.measurable_uncurry.comp (hρm.ennreal_toNNReal.prodMk measurable_id)) hΓ
  · -- a version of the value that is `ℱ_t`-measurable
    set m1 : Ω → ℝ≥0 := fun ω => (ρ ω ⊓ (t : ℝ≥0∞)).toNNReal with hm1
    have hm1m : Measurable[realFiltration β t] m1 := by
      let : MeasurableSpace Ω := realFiltration β t
      refine measurable_of_Iic fun s => ?_
      by_cases hst : t ≤ s
      · have : m1 ⁻¹' Set.Iic s = Set.univ := by
          ext ω
          simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_univ, iff_true, hm1]
          refine (ENNReal.toNNReal_mono (by simp) inf_le_right).trans ?_
          simpa using hst
        rw [this]; exact MeasurableSet.univ
      · have hlt : s < t := not_le.1 hst
        have : m1 ⁻¹' Set.Iic s = {ω | ρ ω ≤ s} := by
          ext ω
          simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_ofPred_eq, hm1]
          have hne : ρ ω ⊓ (t : ℝ≥0∞) ≠ ⊤ := ne_top_of_le_ne_top (by simp) inf_le_right
          rw [← ENNReal.coe_le_coe, ENNReal.coe_toNNReal hne]
          constructor
          · intro h
            rcases le_total (ρ ω) (t : ℝ≥0∞) with h1 | h1
            · rwa [inf_of_le_left h1] at h
            · rw [inf_of_le_right h1] at h
              exact absurd (lt_of_le_of_lt h (by exact_mod_cast hlt)) (lt_irrefl _)
          · intro h
            exact inf_le_left.trans h
        rw [this]
        exact realFiltration_mono β hlt.le _ (hρ s)
    set u : ℝ≥0 → Ω → ℝ := fun s ω => β (min s t) ω with hu
    have hg : Measurable[realFiltration β t] fun ω => u (m1 ω) ω := by
      refine @measurable_value_aux Ω (realFiltration β t) u (fun ω => ?_)
        (fun s => measurable_realFiltration (min_le_right s t)) m1 hm1m
      exact (hproc.1 ω).1.comp (continuous_id.min continuous_const)
    have e : (fun ω => β (ρ ω).toNNReal ω) ⁻¹' Γ ∩ {ω | ρ ω ≤ t} =
        (fun ω => u (m1 ω) ω) ⁻¹' Γ ∩ {ω | ρ ω ≤ t} := by
      ext ω
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq]
      constructor <;> rintro ⟨h1, h2⟩ <;> refine ⟨?_, h2⟩ <;>
        · have hm : m1 ω = (ρ ω).toNNReal := by simp [hm1, inf_of_le_left h2]
          have hle : (ρ ω).toNNReal ≤ t := by
            have := ENNReal.toNNReal_mono (by simp) h2
            simpa using this
          simp only [hu, hm, min_eq_left hle] at *
          exact h1
    rw [e]
    exact (hg hΓ).inter (hρ t)

end ElboimSly.StrongApprox
