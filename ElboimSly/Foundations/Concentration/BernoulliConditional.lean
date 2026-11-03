/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import Mathlib

/-!
# The conditional form of the Bernoulli-trial hypothesis

Domination by Bernoulli trials (d). The set form `p P(G ∩ F) ≤ P(A ∩ G ∩ F)` for all
`F ∈ 𝒢` is equivalent to `E[1_A | 𝒢] ≥ p` a.s. on `G`.
-/

public section

namespace ElboimSly

open MeasureTheory

variable {Ω : Type*} {𝒢 : MeasurableSpace Ω} {m0 : MeasurableSpace Ω} {μ : Measure Ω}

/-- Domination by Bernoulli trials (d). -/
theorem concBernoulli_hyp_iff_condExp [IsProbabilityMeasure μ]
    (h𝒢 : 𝒢 ≤ m0) {G A : Set Ω} (hG : MeasurableSet[𝒢] G) (hA : MeasurableSet A) (p : ℝ) :
    (∀ F, MeasurableSet[𝒢] F → p * μ.real (G ∩ F) ≤ μ.real (A ∩ G ∩ F)) ↔
      ∀ᵐ ω ∂μ, ω ∈ G → p ≤ (μ[A.indicator (fun _ => (1 : ℝ)) | 𝒢]) ω := by
  set f : Ω → ℝ := μ[A.indicator (fun _ => (1 : ℝ)) | 𝒢] with hf
  have hint : Integrable (A.indicator (fun _ => (1 : ℝ))) μ := (integrable_const 1).indicator hA
  have hfint : Integrable f μ := integrable_condExp
  have key : ∀ S, MeasurableSet[𝒢] S → ∫ x in S, f x ∂μ = μ.real (A ∩ S) := by
    intro S hS
    rw [hf, setIntegral_condExp h𝒢 hint hS, integral_indicator_const _ hA,
      measureReal_restrict_apply hA]
    simp
  have hGm : MeasurableSet G := h𝒢 _ hG
  constructor
  · intro h
    by_contra hcon
    -- the set where the conditional probability is below `p`
    set E : Set Ω := G ∩ {ω | f ω < p} with hE
    have hEm : MeasurableSet[𝒢] E := by
      refine hG.inter ?_
      exact (stronglyMeasurable_condExp (m := 𝒢) (μ := μ)
        (f := A.indicator fun _ => (1 : ℝ))).measurable (measurableSet_Iio (a := p))
    have hEm0 : MeasurableSet E := h𝒢 _ hEm
    have h1 := h E hEm
    rw [show G ∩ E = E by ext ω; simp [hE], show A ∩ G ∩ E = A ∩ E by
      ext ω; simp [hE]; tauto] at h1
    have hpos : 0 < μ E := by
      by_contra h0
      have h0' : μ E = 0 := by simpa using h0
      apply hcon
      have : ∀ᵐ ω ∂μ, ω ∉ E := by
        rw [ae_iff]; simpa using h0'
      filter_upwards [this] with ω hω hωG
      by_contra hlt
      exact hω ⟨hωG, not_le.1 hlt⟩
    have hI : Integrable (fun ω => p - f ω) μ := (integrable_const p).sub hfint
    have hpos' : 0 < ∫ x in E, (p - f x) ∂μ := by
      rw [setIntegral_pos_iff_support_of_nonneg_ae]
      · have : Function.support (fun x => p - f x) ∩ E = E := by
          ext ω
          simp only [Set.mem_inter_iff, Function.mem_support]
          constructor
          · exact fun h => h.2
          · intro hω
            exact ⟨by have := hω.2; simp only [Set.mem_ofPred_eq] at this; linarith, hω⟩
        rw [this]; exact hpos
      · rw [Filter.EventuallyLE, ae_restrict_iff' hEm0]
        exact Filter.Eventually.of_forall fun ω hω => by
          have := hω.2; simp only [Set.mem_ofPred_eq] at this; simp; linarith
      · exact hI.integrableOn
    rw [integral_sub (integrable_const p).integrableOn hfint.integrableOn, setIntegral_const,
      key E hEm] at hpos'
    simp only [smul_eq_mul] at hpos'
    linarith [mul_comm p (μ.real E)]
  · intro h F hF
    have hGF : MeasurableSet[𝒢] (G ∩ F) := hG.inter hF
    have hGFm : MeasurableSet (G ∩ F) := h𝒢 _ hGF
    have h1 : ∫ x in G ∩ F, p ∂μ ≤ ∫ x in G ∩ F, f x ∂μ := by
      refine setIntegral_mono_ae_restrict (integrable_const p).integrableOn hfint.integrableOn ?_
      rw [Filter.EventuallyLE, ae_restrict_iff' hGFm]
      exact h.mono fun ω hω hmem => hω hmem.1
    rw [key _ hGF, setIntegral_const] at h1
    simp only [smul_eq_mul] at h1
    rw [Set.inter_assoc]
    linarith [mul_comm p (μ.real (G ∩ F))]

end ElboimSly
