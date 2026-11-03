/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Brownian.Defs
public import ElboimSly.Foundations.Brownian.Process
import Mathlib

/-!
# Existence of standard `d`-dimensional Brownian motion

Gaussian-process characterization; L'evy--Ciesielski; Existence.

* `isStandardBrownianMotion_of_gaussian`: the "if" direction of gaussian-process characterization.
* `isStandardBrownianMotion_levyCiesielski`: l'evy--Ciesielski.
* `exists_standardBrownianMotion`: existence.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace ElboimSly.Brownian

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {d : ℕ}

/-- Gaussian-process characterization (the "if" direction). A process `B` with (BM0) and (BM1) such
that the real process `(i,t) ↦ B(t)_i` is Gaussian, centred, with covariance `δ_{ij} min(s,t)`,
is a standard `d`-dimensional Brownian motion. -/
theorem isStandardBrownianMotion_of_gaussian [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → (Fin d → ℝ)} (h0 : ∀ t, Measurable (B t))
    (h1 : ∀ ω, Continuous (fun t => B t ω) ∧ B 0 ω = 0)
    (hG : IsGaussianProcess (fun (p : Σ _ : Fin d, ℝ≥0) ω => B p.2 ω p.1) P)
    (hmean : ∀ p : Σ _ : Fin d, ℝ≥0, ∫ ω, B p.2 ω p.1 ∂P = 0)
    (hcov : ∀ p q : Σ _ : Fin d, ℝ≥0,
      cov[fun ω => B p.2 ω p.1, fun ω => B q.2 ω q.1; P] =
        if p.1 = q.1 then ((min p.2 q.2 : ℝ≥0) : ℝ) else 0) :
    IsStandardBrownianMotion d B P where
  measurable := h0
  continuous_zero := h1
  isPreBrownianReal i := by
    refine (hG.comp_right (fun t : ℝ≥0 => (⟨i, t⟩ : Σ _ : Fin d, ℝ≥0))).isPreBrownianReal_of_covariance
      (fun t => hmean ⟨i, t⟩) fun s t hst => ?_
    have := hcov ⟨i, s⟩ ⟨i, t⟩
    simp only [ite_true, min_eq_left hst] at this
    exact this
  iIndepFun := by
    refine IsGaussianProcess.iIndepFun_of_covariance_eq_zero
      (X := fun (i : Fin d) (t : ℝ≥0) ω => B t ω i) (S := fun _ => ℝ≥0) hG
      (fun i t => ((measurable_pi_apply i).comp (h0 t)).aemeasurable) ?_
    intro i j hij s t
    have := hcov ⟨i, s⟩ ⟨j, t⟩
    simpa [hij] using this

section LC

variable [IsProbabilityMeasure P] {ξ : Idx d → Ω → ℝ}

/-- Each coordinate `B^i(t)` of the Lévy–Ciesielski process has law `N(0, t)`. -/
lemma hasLaw_levyCiesielski_coord (hmeas : ∀ α, Measurable (ξ α)) (hind : iIndepFun ξ P)
    (hlaw : ∀ α, HasLaw (ξ α) (gaussianReal 0 1) P) (p : Σ _ : Fin d, ℝ≥0) :
    HasLaw (fun ω => levyCiesielski ξ p.2 ω p.1) (gaussianReal 0 p.2) P := by
  have := (hasLaw_linear_combination hmeas hind hlaw (ι := Unit) (fun _ => p) (fun _ => 1)).2
  convert this using 1
  · funext ω; simp
  · congr 1
    simp

/-- The covariance of two coordinates of the Lévy–Ciesielski process. -/
lemma covariance_levyCiesielski (hmeas : ∀ α, Measurable (ξ α)) (hind : iIndepFun ξ P)
    (hlaw : ∀ α, HasLaw (ξ α) (gaussianReal 0 1) P) (p q : Σ _ : Fin d, ℝ≥0) :
    cov[fun ω => levyCiesielski ξ p.2 ω p.1, fun ω => levyCiesielski ξ q.2 ω q.1; P] =
      if p.1 = q.1 then ((min p.2 q.2 : ℝ≥0) : ℝ) else 0 := by
  have hp := hasLaw_levyCiesielski_coord hmeas hind hlaw p
  have hq := hasLaw_levyCiesielski_coord hmeas hind hlaw q
  have hpq := hasLaw_linear_combination hmeas hind hlaw (ι := Fin 2) ![p, q] (fun _ => 1)
  have hmp := hp.hasGaussianLaw.memLp_two
  have hmq := hq.hasGaussianLaw.memLp_two
  have hvar := hpq.2.variance_eq
  rw [variance_id_gaussianReal, Real.coe_toNNReal _ hpq.1] at hvar
  have hadd := variance_fun_add hmp hmq
  have e : (fun ω => levyCiesielski ξ p.2 ω p.1 + levyCiesielski ξ q.2 ω q.1) =
      fun ω => ∑ j, 1 * levyCiesielski ξ ((![p, q] : Fin 2 → Σ _ : Fin d, ℝ≥0) j).2 ω
        ((![p, q] : Fin 2 → Σ _ : Fin d, ℝ≥0) j).1 := by
    funext ω; simp [Fin.sum_univ_two]
  rw [e] at hadd
  rw [hvar, hp.variance_eq, hq.variance_eq, variance_id_gaussianReal, variance_id_gaussianReal]
    at hadd
  simp only [Fin.sum_univ_two] at hadd
  by_cases h : p.1 = q.1
  · simp [h] at hadd ⊢
    have := min_comm (p.2 : ℝ) q.2
    linarith
  · have h' : ¬ q.1 = p.1 := fun e => h e.symm
    simp [h, h'] at hadd ⊢
    linarith

end LC

/-- **Lévy–Ciesielski.** L'evy--Ciesielski. If `(ξ_α)_{α ∈ Idx d}` are independent
real random variables with law `N(0,1)`, then `LC[ξ]` is a standard `d`-dimensional Brownian
motion. Moreover `LC[ξ](j) = ∑_{m<j} ξ_{(·,m,*)}` everywhere, for every `j : ℕ`
(`levyCiesielski_nat`). -/
theorem isStandardBrownianMotion_levyCiesielski [IsProbabilityMeasure P]
    {ξ : Idx d → Ω → ℝ} (hmeas : ∀ α, Measurable (ξ α)) (hind : iIndepFun ξ P)
    (hlaw : ∀ α, HasLaw (ξ α) (gaussianReal 0 1) P) :
    IsStandardBrownianMotion d (levyCiesielski ξ) P := by
  -- the real process is Gaussian
  have hG : IsGaussianProcess (fun (p : Σ _ : Fin d, ℝ≥0) ω => levyCiesielski ξ p.2 ω p.1) P := by
    refine ⟨fun I => ?_⟩
    have hm : Measurable fun ω => I.restrict fun p => levyCiesielski ξ p.2 ω p.1 :=
      measurable_pi_iff.2 fun (p : I) => (measurable_pi_apply p.1.1).comp
        (measurable_levyCiesielski hmeas p.1.2)
    refine ⟨hm.aemeasurable, isGaussian_of_map_eq_gaussianReal fun L => ?_⟩
    set lam : I → ℝ := fun j => L (fun k => if j = k then 1 else 0) with hlam
    have hL : (L ∘ fun ω => I.restrict fun p => levyCiesielski ξ p.2 ω p.1) =
        fun ω => ∑ j : I, lam j * levyCiesielski ξ (j.1.2) ω j.1.1 := by
      funext ω
      have h := L.toLinearMap.pi_apply_eq_sum_univ
        (I.restrict fun p => levyCiesielski ξ p.2 ω p.1)
      exact h.trans (Finset.sum_congr rfl fun j _ => by simp [mul_comm, hlam])
    have hY := (hasLaw_linear_combination hmeas hind hlaw (ι := I) (fun j => j.1) lam).2
    exact ⟨0, _, by rw [Measure.map_map L.continuous.measurable hm, hL]; exact hY.map_eq⟩
  refine isStandardBrownianMotion_of_gaussian (measurable_levyCiesielski hmeas)
    (fun ω => ⟨continuous_levyCiesielski ξ ω, levyCiesielski_zero ξ ω⟩) hG ?_
    (covariance_levyCiesielski hmeas hind hlaw)
  intro p
  have := (hasLaw_levyCiesielski_coord hmeas hind hlaw p).integral_eq
  rw [show (∫ ω, levyCiesielski ξ p.2 ω p.1 ∂P) = _ from this]
  exact integral_id_gaussianReal

/-- **Existence of Brownian motion.** Existence. For every `d` there is a
probability space carrying a standard `d`-dimensional Brownian motion: the product space
`ℝ^{Idx d}` with `⨂_α N(0,1)` and `ξ_α(ω) = ω_α`. -/
theorem exists_standardBrownianMotion (d : ℕ) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (B : ℝ≥0 → Ω → (Fin d → ℝ)), IsStandardBrownianMotion d B P := by
  let μ : Idx d → Measure ℝ := fun _ => gaussianReal 0 1
  refine ⟨Idx d → ℝ, inferInstance, Measure.infinitePi μ, inferInstance,
    levyCiesielski (fun (α : Idx d) (ω : Idx d → ℝ) => ω α), ?_⟩
  refine isStandardBrownianMotion_levyCiesielski (fun α => measurable_pi_apply α) ?_ ?_
  · exact iIndepFun_infinitePi (P := μ) (X := fun _ x => x) fun _ => measurable_id
  · intro α
    exact ⟨(measurable_pi_apply α).aemeasurable, Measure.infinitePi_map_eval μ α⟩

end ElboimSly.Brownian
