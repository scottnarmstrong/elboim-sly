/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.StrongApprox.X1LawT
public import ElboimSly.Foundations.StrongApprox.Chernoff
public import Mathlib

/-!
# The clocks: Chernoff hypotheses in the coupling space

Laws in the coupling (c), the coupling error (clock event `G₁`)
(Part II).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace ElboimSly.StrongApprox

open ElboimSly.Brownian

variable {d ℓ : ℕ} (lam : Measure (Fin d → ℝ)) [IsProbabilityMeasure lam]

lemma map_Tcoord (hlam : ∀ᵐ x ∂lam, ∀ k, 0 ≤ x k) (k : Fin d) (i : Fin ℓ) :
    (P1 d ℓ lam).map (fun ω => Tp k (Vfull ℓ ω) i) = kbar lam k := by
  have hTm : Measurable fun ω : Ω1 d ℓ => Tp k (Vfull ℓ ω) :=
    (measurable_Tp k).comp (measurable_Vfull d ℓ)
  have e : (fun ω : Ω1 d ℓ => Tp k (Vfull ℓ ω) i) =
      (fun t : Fin ℓ → ℝ≥0∞ => t i) ∘ (fun ω => Tp k (Vfull ℓ ω)) := rfl
  rw [e, ← Measure.map_map (measurable_pi_apply i) hTm, map_Tvec lam hlam k,
    (measurePreserving_eval (fun _ : Fin ℓ => kbar lam k) i).map_eq]

lemma measurable_Tcoord (k : Fin d) (i : Fin ℓ) :
    Measurable fun ω : Ω1 d ℓ => Tp k (Vfull ℓ ω) i :=
  (measurable_pi_apply i).comp ((measurable_Tp k).comp (measurable_Vfull d ℓ))

lemma iIndepFun_Tcoord (hlam : ∀ᵐ x ∂lam, ∀ k, 0 ≤ x k) (k : Fin d) :
    iIndepFun (fun (i : Fin ℓ) (ω : Ω1 d ℓ) => Tp k (Vfull ℓ ω) i) (P1 d ℓ lam) := by
  refine (iIndepFun_iff_map_fun_eq_pi_map (fun i => (measurable_Tcoord k i).aemeasurable)).2 ?_
  have hTm : Measurable fun ω : Ω1 d ℓ => Tp k (Vfull ℓ ω) :=
    (measurable_Tp k).comp (measurable_Vfull d ℓ)
  have : (fun ω : Ω1 d ℓ => fun i : Fin ℓ => Tp k (Vfull ℓ ω) i) =
      fun ω => Tp k (Vfull ℓ ω) := rfl
  rw [this, map_Tvec lam hlam k]
  congr 1
  funext i
  exact (map_Tcoord lam hlam k i).symm

lemma ae_Tcoord_lt_top (hlam : ∀ᵐ x ∂lam, ∀ k, 0 ≤ x k) :
    ∀ᵐ ω ∂(P1 d ℓ lam), ∀ (k : Fin d) (i : Fin ℓ), Tp k (Vfull ℓ ω) i < ⊤ := by
  rw [ae_all_iff]; intro k
  rw [ae_all_iff]; intro i
  have h := kbar_top lam k (hlam.mono fun x hx => hx k)
  have : ∀ᵐ t ∂(kbar lam k), t < ⊤ := by
    rw [ae_iff]
    refine measure_mono_null ?_ h
    intro t ht
    simpa using ht
  have hm := measurable_Tcoord (ℓ := ℓ) k i
  rw [← map_Tcoord lam hlam k i] at this
  exact (ae_map_iff hm.aemeasurable measurableSet_Iio).1 this

variable (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ]

lemma ae_lam_bound {M : ℝ} (hM : μ {x | ‖x‖ ≤ M} = 1) :
    ∀ᵐ x ∂(μ.map absVec), ∀ k, 0 ≤ x k ∧ x k ≤ M := by
  have hS : MeasurableSet {x : Fin d → ℝ | ∀ k, 0 ≤ x k ∧ x k ≤ M} := by
    have : {x : Fin d → ℝ | ∀ k, 0 ≤ x k ∧ x k ≤ M} =
        ⋂ k, ({x : Fin d → ℝ | 0 ≤ x k} ∩ {x : Fin d → ℝ | x k ≤ M}) := by
      ext x; simp
    rw [this]
    exact MeasurableSet.iInter fun k =>
      (measurableSet_le measurable_const (measurable_pi_apply k)).inter
        (measurableSet_le (measurable_pi_apply k) measurable_const)
  rw [ae_map_iff (measurable_absVec d).aemeasurable hS]
  have hc : MeasurableSet {x : Fin d → ℝ | ‖x‖ ≤ M} := measurableSet_le measurable_norm
    measurable_const
  have : ∀ᵐ z ∂μ, ‖z‖ ≤ M := by
    rw [ae_iff]
    have := (prob_compl_eq_zero_iff hc).2 hM
    simpa [Set.compl_def, not_le] using this
  filter_upwards [this] with z hz k
  exact ⟨abs_nonneg _, (norm_le_pi_norm z k).trans hz⟩

variable {μ}

/-- The clocks of coordinate `k` satisfy the hypotheses of the Chernoff bound. -/
theorem chernoff_clocks_event (hℓ : 1 ≤ ℓ) {M : ℝ} (hM : 1 ≤ M)
    (hμM : μ {x | ‖x‖ ≤ M} = 1) (hsq : ∀ k, ∫ x, x k ^ 2 ∂μ = 1)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ : γ ≤ 2 * ℓ) (k : Fin d) :
    (P1 d ℓ (μ.map absVec)) {ω | ∃ j : Fin ℓ, 215 * M ^ 2 * Real.sqrt (ℓ * γ) ≤
        |∑ i ∈ Finset.univ.filter (· ≤ j), ((Tp k (Vfull ℓ ω) i).toReal - 1)|} ≤
      ENNReal.ofReal (2 * ℓ * Real.exp (-γ)) := by
  have : IsProbabilityMeasure (μ.map absVec) :=
    (Measure.isProbabilityMeasure_map_iff (measurable_absVec d).aemeasurable).2 inferInstance
  have hlam0 : ∀ᵐ x ∂(μ.map absVec), ∀ k, 0 ≤ x k :=
    (ae_lam_bound μ hμM).mono fun x hx k => (hx k).1
  have hlamM := ae_lam_bound μ hμM
  have hfin := ae_Tcoord_lt_top (μ.map absVec) hlam0 (ℓ := ℓ)
  refine chernoff_clock hℓ hM (τ := fun (i : Fin ℓ) (ω : Ω1 d ℓ) => (Tp k (Vfull ℓ ω) i).toReal)
    (fun i => ENNReal.measurable_toReal.comp (measurable_Tcoord k i))
    ((iIndepFun_Tcoord (μ.map absVec) hlam0 k).comp (fun _ => ENNReal.toReal)
      (fun _ => ENNReal.measurable_toReal))
    (fun i ω => ENNReal.toReal_nonneg) ?_ ?_ hγ0 hγ
  · intro i
    rw [integral_toReal (measurable_Tcoord k i).aemeasurable
      (hfin.mono fun ω h => h k i)]
    have h1 : ∫⁻ ω, Tp k (Vfull ℓ ω) i ∂(P1 d ℓ (μ.map absVec)) = 1 := by
      have := lintegral_map (μ := P1 d ℓ (μ.map absVec)) (f := fun t : ℝ≥0∞ => t)
        measurable_id (measurable_Tcoord k i)
      rw [map_Tcoord (μ.map absVec) hlam0 k i] at this
      rw [← this, lintegral_kbar_id (μ.map absVec) k (hlam0.mono fun x hx => hx k),
        lintegral_map (f := fun x : Fin d → ℝ => ENNReal.ofReal (x k ^ 2))
          (ENNReal.measurable_ofReal.comp ((measurable_pi_apply k).pow_const 2))
          (measurable_absVec d)]
      have hint : Integrable (fun z : Fin d → ℝ => z k ^ 2) μ :=
        Integrable.of_integral_ne_zero (by rw [hsq k]; exact one_ne_zero)
      have : ∀ z : Fin d → ℝ, ENNReal.ofReal (absVec z k ^ 2) = ENNReal.ofReal (z k ^ 2) := by
        intro z; simp [absVec, sq_abs]
      simp_rw [this]
      rw [← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun z =>
        sq_nonneg _), hsq k]
      simp
    rw [h1]; simp
  · intro i
    have hf : Measurable fun t : ℝ≥0∞ => ENNReal.ofReal (Real.exp (t.toReal / (36 * M ^ 2))) :=
      ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
        (ENNReal.measurable_toReal.div_const _))
    have := lintegral_map (μ := P1 d ℓ (μ.map absVec)) hf (measurable_Tcoord k i)
    rw [map_Tcoord (μ.map absVec) hlam0 k i] at this
    rw [← this]
    refine le_trans (lintegral_kbar_exp (μ.map absVec) k hM (hlamM.mono fun x hx => hx k)) ?_
    norm_num

end ElboimSly.StrongApprox
