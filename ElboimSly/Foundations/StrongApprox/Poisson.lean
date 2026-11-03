/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import Mathlib.Probability.Distributions.Poisson.Basic
public import Mathlib.Probability.Moments.Basic
public import ElboimSly.Foundations.StrongApprox.Elementary

/-!
# Poisson root estimates

Poisson root estimates (Part I). The moment
generating function of the Poisson law (Poisson facts(f)) is reproved here from
Mathlib's `ProbabilityTheory.poissonMeasure`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology Finset
open scoped NNReal Real ENNReal Nat

namespace ElboimSly
namespace StrongApprox

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {P : Ω → ℕ} {r : ℝ≥0}

theorem poisson_hasSum_mgf (r : ℝ≥0) (θ : ℝ) :
    HasSum (fun n : ℕ => (Real.exp (-r) * (r : ℝ) ^ n / n !) * Real.exp (θ * ((n : ℝ) - r)))
      (Real.exp (r * (Real.exp θ - 1 - θ))) := by
  have h := (NormedSpace.expSeries_div_hasSum_exp ((r : ℝ) * Real.exp θ)).mul_left
    (Real.exp (-r - θ * r))
  rw [← Real.exp_eq_exp_ℝ] at h
  convert h using 1
  · funext n
    have : Real.exp (θ * ((n : ℝ) - r)) = Real.exp (n * θ) * Real.exp (-(θ * r)) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [this, Real.exp_nat_mul, show -(r : ℝ) - θ * r = -r + -(θ * r) by ring, Real.exp_add, mul_pow]
    ring
  · rw [← Real.exp_add]; congr 1; ring

theorem poisson_integrable_mgf (hP : HasLaw P (poissonMeasure r) μ) (θ : ℝ) :
    Integrable (fun ω => Real.exp (θ * (((P ω : ℕ) : ℝ) - r))) μ := by
  have : Integrable (fun n : ℕ => Real.exp (θ * ((n : ℝ) - r))) (poissonMeasure r) := by
    rw [integrable_poissonMeasure_iff]
    refine (poisson_hasSum_mgf r θ).summable.congr fun n => ?_
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact hP.integrable_comp this

/-- The Poisson moment generating function (Poisson facts(f)). -/
theorem poisson_integral_mgf (hP : HasLaw P (poissonMeasure r) μ) (θ : ℝ) :
    ∫ ω, Real.exp (θ * (((P ω : ℕ) : ℝ) - r)) ∂μ = Real.exp (r * (Real.exp θ - 1 - θ)) := by
  have h := hP.integral_comp (f := fun n : ℕ => Real.exp (θ * ((n : ℝ) - r)))
    Measurable.of_discrete.aestronglyMeasurable
  simp only [Function.comp_def] at h
  rw [h, integral_poissonMeasure]
  rw [← (poisson_hasSum_mgf r θ).tsum_eq]
  simp only [smul_eq_mul]

section Tails

variable [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
theorem poisson_mgf_le (hP : HasLaw P (poissonMeasure r) μ) {θ : ℝ} (hθ : |θ| ≤ 1) :
    ∫ ω, Real.exp (θ * (((P ω : ℕ) : ℝ) - r)) ∂μ ≤ Real.exp (3 / 4 * r * θ ^ 2) := by
  rw [poisson_integral_mgf hP]
  apply Real.exp_le_exp.2
  have := (abs_le.1 (abs_exp_sub_one_sub_le hθ)).2
  have h0 : (0 : ℝ) ≤ r := r.2
  nlinarith

theorem poisson_upper_markov (hP : HasLaw P (poissonMeasure r) μ) {θ : ℝ} (hθ : 0 ≤ θ) (ε : ℝ) :
    μ.real {ω | ε ≤ ((P ω : ℕ) : ℝ) - r} ≤
      Real.exp (-θ * ε) * Real.exp (r * (Real.exp θ - 1 - θ)) := by
  have := measure_ge_le_exp_mul_mgf (μ := μ) (X := fun ω => ((P ω : ℕ) : ℝ) - r) ε hθ
    (poisson_integrable_mgf hP θ)
  rw [mgf, poisson_integral_mgf hP] at this
  exact this

theorem poisson_lower_markov (hP : HasLaw P (poissonMeasure r) μ) {θ : ℝ} (hθ : θ ≤ 0) (ε : ℝ) :
    μ.real {ω | ((P ω : ℕ) : ℝ) - r ≤ ε} ≤
      Real.exp (-θ * ε) * Real.exp (r * (Real.exp θ - 1 - θ)) := by
  have := measure_le_le_exp_mul_mgf (μ := μ) (X := fun ω => ((P ω : ℕ) : ℝ) - r) ε hθ
    (poisson_integrable_mgf hP θ)
  rw [mgf, poisson_integral_mgf hP] at this
  exact this

theorem exp_markov_le {θ : ℝ} (ε : ℝ) (hθ : |θ| ≤ 1) :
    Real.exp (-θ * ε) * Real.exp (r * (Real.exp θ - 1 - θ)) ≤
      Real.exp (-θ * ε + 3 / 4 * r * θ ^ 2) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.2
  have := (abs_le.1 (abs_exp_sub_one_sub_le hθ)).2
  have h0 : (0 : ℝ) ≤ r := r.2
  nlinarith

theorem poisson_sqrt_upper (hP : HasLaw P (poissonMeasure r) μ) (hr : 1 ≤ (r : ℝ)) {t : ℝ}
    (ht : 0 < t) :
    μ.real {ω | t ≤ √((P ω : ℕ) : ℝ) - √(r : ℝ)} ≤ Real.exp (-(t ^ 2 / 4)) := by
  have hr0 : (0 : ℝ) < r := by linarith
  have hsr : 0 < √(r : ℝ) := Real.sqrt_pos.2 hr0
  have hsq : √(r : ℝ) ^ 2 = r := Real.sq_sqrt hr0.le
  have hincl : ∀ ω, t ≤ √((P ω : ℕ) : ℝ) - √(r : ℝ) →
      (√(r : ℝ) + t) ^ 2 ≤ (P ω : ℝ) := by
    intro ω h
    have h1 : √(r : ℝ) + t ≤ √((P ω : ℕ) : ℝ) := by linarith
    have h2 := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) (P ω))
    rw [← h2]; exact pow_le_pow_left₀ (by positivity) h1 2
  by_cases htr : t ≤ √(r : ℝ)
  · have hθ : t / √(r : ℝ) ≤ 1 := by rw [div_le_one hsr]; exact htr
    have hθ0 : 0 ≤ t / √(r : ℝ) := by positivity
    have e1 : (t / √(r : ℝ)) * (2 * t * √(r : ℝ)) = 2 * t ^ 2 := by field_simp
    have e2 : (r : ℝ) * (t / √(r : ℝ)) ^ 2 = t ^ 2 := by
      rw [div_pow, hsq]; field_simp
    calc μ.real {ω | t ≤ √((P ω : ℕ) : ℝ) - √(r : ℝ)}
        ≤ μ.real {ω | 2 * t * √(r : ℝ) ≤ ((P ω : ℕ) : ℝ) - r} := by
          apply measureReal_mono _ (measure_ne_top _ _)
          intro ω h
          have := hincl ω h
          simp only [mem_ofPred_eq] at h ⊢
          nlinarith [sq_nonneg t]
        _ ≤ _ := poisson_upper_markov hP hθ0 _
        _ ≤ _ := exp_markov_le _ (by rw [abs_of_nonneg hθ0]; exact hθ)
        _ ≤ Real.exp (-(t ^ 2 / 4)) := by
          apply Real.exp_le_exp.2
          have : -(t / √(r : ℝ)) * (2 * t * √(r : ℝ)) = -(2 * t ^ 2) := by linarith
          rw [this, mul_assoc, e2]
          nlinarith [sq_nonneg t]
  · rw [not_le] at htr
    have hrt : (r : ℝ) < t ^ 2 := by nlinarith
    calc μ.real {ω | t ≤ √((P ω : ℕ) : ℝ) - √(r : ℝ)}
        ≤ μ.real {ω | t ^ 2 ≤ ((P ω : ℕ) : ℝ) - r} := by
          apply measureReal_mono _ (measure_ne_top _ _)
          intro ω h
          have := hincl ω h
          simp only [mem_ofPred_eq] at h ⊢
          nlinarith [mul_pos hsr ht]
        _ ≤ _ := poisson_upper_markov hP (θ := 1) zero_le_one _
        _ ≤ _ := exp_markov_le _ (by simp)
        _ ≤ Real.exp (-(t ^ 2 / 4)) := by
          apply Real.exp_le_exp.2
          nlinarith [exp_one_sub_two_le]

theorem poisson_sqrt_lower (hP : HasLaw P (poissonMeasure r) μ) (hr : 1 ≤ (r : ℝ)) {t : ℝ}
    (ht : 0 < t) :
    μ.real {ω | √((P ω : ℕ) : ℝ) - √(r : ℝ) ≤ -t} ≤ Real.exp (-(t ^ 2 / 4)) := by
  have hr0 : (0 : ℝ) < r := by linarith
  have hsr : 0 < √(r : ℝ) := Real.sqrt_pos.2 hr0
  have hsq : √(r : ℝ) ^ 2 = r := Real.sq_sqrt hr0.le
  by_cases htr : t ≤ √(r : ℝ)
  · have hθ : t / √(r : ℝ) ≤ 1 := by rw [div_le_one hsr]; exact htr
    have hθ0 : 0 ≤ t / √(r : ℝ) := by positivity
    have e1 : (-(t / √(r : ℝ))) * (-(t * √(r : ℝ))) = t ^ 2 := by field_simp
    have e2 : (r : ℝ) * (-(t / √(r : ℝ))) ^ 2 = t ^ 2 := by
      rw [neg_sq, div_pow, hsq]; field_simp
    calc μ.real {ω | √((P ω : ℕ) : ℝ) - √(r : ℝ) ≤ -t}
        ≤ μ.real {ω | ((P ω : ℕ) : ℝ) - r ≤ -(t * √(r : ℝ))} := by
          apply measureReal_mono _ (measure_ne_top _ _)
          intro ω h
          simp only [mem_ofPred_eq] at h ⊢
          have h1 : √((P ω : ℕ) : ℝ) ≤ √(r : ℝ) - t := by linarith
          have h2 := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) (P ω))
          have h3 := Real.sqrt_nonneg ((P ω : ℕ) : ℝ)
          have h4 : ((P ω : ℕ) : ℝ) ≤ (√(r : ℝ) - t) ^ 2 := by
            rw [← h2]; exact pow_le_pow_left₀ h3 h1 2
          nlinarith [mul_nonneg ht.le (sub_nonneg.2 htr)]
        _ ≤ _ := poisson_lower_markov hP (θ := -(t / √(r : ℝ))) (by linarith) _
        _ ≤ _ := exp_markov_le _ (by rw [abs_neg, abs_of_nonneg hθ0]; exact hθ)
        _ ≤ Real.exp (-(t ^ 2 / 4)) := by
          apply Real.exp_le_exp.2
          have e3 : -(-(t / √(r : ℝ))) * -(t * √(r : ℝ)) = -t ^ 2 := by linarith
          nlinarith [e2, e3, sq_nonneg t]
  · rw [not_le] at htr
    have : {ω | √((P ω : ℕ) : ℝ) - √(r : ℝ) ≤ -t} = ∅ := by
      ext ω
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_le]
      have := Real.sqrt_nonneg ((P ω : ℕ) : ℝ)
      linarith
    rw [this]; simp only [measureReal_empty]; exact (Real.exp_pos _).le


/-- Poisson root estimates(a), the tail bound. -/
theorem poisson_sqrt_abs_tail (hP : HasLaw P (poissonMeasure r) μ) (hr : 1 ≤ (r : ℝ)) {t : ℝ}
    (ht : 0 < t) :
    μ.real {ω | t ≤ |√((P ω : ℕ) : ℝ) - √(r : ℝ)|} ≤ 2 * Real.exp (-(t ^ 2 / 4)) := by
  calc μ.real {ω | t ≤ |√((P ω : ℕ) : ℝ) - √(r : ℝ)|}
      ≤ μ.real ({ω | t ≤ √((P ω : ℕ) : ℝ) - √(r : ℝ)} ∪
          {ω | √((P ω : ℕ) : ℝ) - √(r : ℝ) ≤ -t}) := by
        apply measureReal_mono _ (measure_ne_top _ _)
        intro ω h
        simp only [mem_ofPred_eq, mem_union] at h ⊢
        rcases le_abs'.1 h with h | h
        · right; exact h
        · left; exact h
    _ ≤ μ.real {ω | t ≤ √((P ω : ℕ) : ℝ) - √(r : ℝ)} +
          μ.real {ω | √((P ω : ℕ) : ℝ) - √(r : ℝ) ≤ -t} := measureReal_union_le _ _
    _ ≤ Real.exp (-(t ^ 2 / 4)) + Real.exp (-(t ^ 2 / 4)) :=
        add_le_add (poisson_sqrt_upper hP hr ht) (poisson_sqrt_lower hP hr ht)
    _ = _ := by ring

theorem poisson_sqrt_sq_tail (hP : HasLaw P (poissonMeasure r) μ) (hr : 1 ≤ (r : ℝ)) {ρ : ℝ}
    (hρ : 0 ≤ ρ) :
    μ.real {ω | ρ ≤ (√((P ω : ℕ) : ℝ) - √(r : ℝ)) ^ 2} ≤ 2 * Real.exp (-(1 / 4 * ρ)) := by
  rcases hρ.eq_or_lt with rfl | hρp
  · simp only [mul_zero, neg_zero, Real.exp_zero, mul_one]
    exact (measureReal_le_one).trans (by norm_num)
  have ht : 0 < √ρ := Real.sqrt_pos.2 hρp
  have h2 : √ρ ^ 2 = ρ := Real.sq_sqrt hρ
  have := poisson_sqrt_abs_tail hP hr ht
  rw [h2] at this
  refine le_trans (measureReal_mono ?_ (measure_ne_top _ _)) (this.trans (le_of_eq ?_))
  · intro ω h
    simp only [mem_ofPred_eq] at h ⊢
    calc √ρ = √ρ := rfl
      _ ≤ √((√((P ω : ℕ) : ℝ) - √(r : ℝ)) ^ 2) := Real.sqrt_le_sqrt h
      _ = _ := Real.sqrt_sq_eq_abs _
  · congr 2; ring

/-- Poisson root estimates(a), the moment bound `E e^{c(√P-√r)²} ≤ 19`. -/
theorem poisson_exp_sqrt_sq_le (hP : HasLaw P (poissonMeasure r) μ) (hPm : Measurable P)
    (hr : 1 ≤ (r : ℝ)) {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1 / 8) :
    Integrable (fun ω => Real.exp (c * (√((P ω : ℕ) : ℝ) - √(r : ℝ)) ^ 2)) μ ∧
      ∫ ω, Real.exp (c * (√((P ω : ℕ) : ℝ) - √(r : ℝ)) ^ 2) ∂μ ≤ 19 := by
  have hβ : Measurable fun ω => (√((P ω : ℕ) : ℝ) - √(r : ℝ)) ^ 2 := by fun_prop
  have := integral_exp_le_layerCakeBound (P := μ)
    (Y := fun ω => (√((P ω : ℕ) : ℝ) - √(r : ℝ)) ^ 2) hβ (fun ω => sq_nonneg _) (c := c)
    (κ := 1 / 4) hc0 (by linarith) (fun ρ hρ => poisson_sqrt_sq_tail hP hr hρ)
  refine ⟨this.1, this.2.trans ?_⟩
  exact (layerCakeBound_mono hc1 (by norm_num)).trans layerCakeBound_quarter_le

omit [IsProbabilityMeasure μ] in
/-- Poisson root estimates(b): `E e^{|P-r|/√r} ≤ 2e^{3/4}`. -/
theorem poisson_exp_abs_le (hP : HasLaw P (poissonMeasure r) μ) (hPm : Measurable P)
    (hr : 1 ≤ (r : ℝ)) :
    Integrable (fun ω => Real.exp (|((P ω : ℕ) : ℝ) - r| / √(r : ℝ))) μ ∧
      ∫ ω, Real.exp (|((P ω : ℕ) : ℝ) - r| / √(r : ℝ)) ∂μ ≤ 2 * Real.exp (3 / 4) := by
  have hr0 : (0 : ℝ) < r := by linarith
  have hsr : 0 < √(r : ℝ) := Real.sqrt_pos.2 hr0
  have hsq : √(r : ℝ) ^ 2 = r := Real.sq_sqrt hr0.le
  have hθ : 1 / √(r : ℝ) ≤ 1 := by
    rw [div_le_one hsr]; calc (1 : ℝ) = √1 := Real.sqrt_one.symm
      _ ≤ _ := Real.sqrt_le_sqrt hr
  have hθ0 : 0 ≤ 1 / √(r : ℝ) := by positivity
  have hθ2 : 3 / 4 * (r : ℝ) * (1 / √(r : ℝ)) ^ 2 = 3 / 4 := by
    rw [div_pow, hsq]; field_simp
  have i1 := poisson_integrable_mgf hP (1 / √(r : ℝ))
  have i2 := poisson_integrable_mgf hP (-(1 / √(r : ℝ)))
  have m1 := poisson_mgf_le hP (θ := 1 / √(r : ℝ)) (by rw [abs_of_nonneg hθ0]; exact hθ)
  have m2 := poisson_mgf_le hP (θ := -(1 / √(r : ℝ))) (by rw [abs_neg, abs_of_nonneg hθ0]; exact hθ)
  rw [hθ2] at m1
  rw [neg_sq, hθ2] at m2
  have hle : ∀ ω, Real.exp (|((P ω : ℕ) : ℝ) - r| / √(r : ℝ)) ≤
      Real.exp (1 / √(r : ℝ) * (((P ω : ℕ) : ℝ) - r)) +
        Real.exp (-(1 / √(r : ℝ)) * (((P ω : ℕ) : ℝ) - r)) := by
    intro ω
    rcases abs_cases (((P ω : ℕ) : ℝ) - r) with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h]
      have : ((P ω : ℕ) : ℝ) - r = ((P ω : ℕ) : ℝ) - r := rfl
      have e : (((P ω : ℕ) : ℝ) - r) / √(r : ℝ) = 1 / √(r : ℝ) * (((P ω : ℕ) : ℝ) - r) := by ring
      rw [e]; linarith [Real.exp_pos (-(1 / √(r : ℝ)) * (((P ω : ℕ) : ℝ) - r))]
    · rw [h]
      have e : -(((P ω : ℕ) : ℝ) - r) / √(r : ℝ) = -(1 / √(r : ℝ)) * (((P ω : ℕ) : ℝ) - r) := by ring
      rw [e]; linarith [Real.exp_pos (1 / √(r : ℝ) * (((P ω : ℕ) : ℝ) - r))]
  have hmeas : Measurable fun ω => Real.exp (|((P ω : ℕ) : ℝ) - r| / √(r : ℝ)) := by fun_prop
  have hint : Integrable (fun ω => Real.exp (|((P ω : ℕ) : ℝ) - r| / √(r : ℝ))) μ :=
    (i1.add i2).mono' hmeas.aestronglyMeasurable
      (ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]; exact hle ω)
  refine ⟨hint, ?_⟩
  calc ∫ ω, Real.exp (|((P ω : ℕ) : ℝ) - r| / √(r : ℝ)) ∂μ
      ≤ ∫ ω, (Real.exp (1 / √(r : ℝ) * (((P ω : ℕ) : ℝ) - r)) +
          Real.exp (-(1 / √(r : ℝ)) * (((P ω : ℕ) : ℝ) - r))) ∂μ :=
        integral_mono hint (i1.add i2) hle
    _ = _ := integral_add i1 i2
    _ ≤ Real.exp (3 / 4) + Real.exp (3 / 4) := add_le_add m1 m2
    _ = _ := by ring

end Tails

end StrongApprox
end ElboimSly
