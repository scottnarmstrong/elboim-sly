/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.StrongApprox.PathMoment

/-!
# A1 for dyadic lengths: moments

Exponential moments along a path; A1 for dyadic lengths. The probability space of the tree of depth `n` is
`ℕ × ℝ × DT n` with law `Poisson(2^n) ⊗ 𝒩(0,1) ⊗ muDT n`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace ElboimSly
namespace StrongApprox

/-- The probability space of the tree of depth `n` (The dyadic tree of depth 2L, `Ω_L`, `ℙ_L`). -/
noncomputable def Pdy (n : ℕ) : Measure (ℕ × ℝ × DT n) :=
  (poissonMeasure (2 ^ n)).prod (saN.prod (muDT n))

instance (n : ℕ) : IsProbabilityMeasure (Pdy n) := by
  unfold Pdy; infer_instance

/-- Markov's inequality in exponential form. -/
theorem markov_exp {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {f : Ω → ℝ}
    (hf : Measurable f) {s : ℝ} (hs : 0 < s) (t : ℝ) :
    μ {ω | t ≤ f ω} ≤
      ENNReal.ofReal (Real.exp (-(s * t))) * ∫⁻ ω, ENNReal.ofReal (Real.exp (s * f ω)) ∂μ := by
  have hmeas : Measurable fun ω => ENNReal.ofReal (Real.exp (s * f ω)) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (measurable_const.mul hf))
  have h := mul_meas_ge_le_lintegral₀ (μ := μ) hmeas.aemeasurable (ENNReal.ofReal (Real.exp (s * t)))
  have hsub : μ {ω | t ≤ f ω} ≤
      μ {ω | ENNReal.ofReal (Real.exp (s * t)) ≤ ENNReal.ofReal (Real.exp (s * f ω))} := by
    refine measure_mono fun ω hω => ?_
    simp only [mem_ofPred_eq] at hω ⊢
    exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (by nlinarith))
  have h0 : ENNReal.ofReal (Real.exp (s * t)) ≠ 0 := by simp [Real.exp_pos]
  have hinv : (ENNReal.ofReal (Real.exp (s * t)))⁻¹ = ENNReal.ofReal (Real.exp (-(s * t))) := by
    rw [← ENNReal.ofReal_inv_of_pos (Real.exp_pos _), Real.exp_neg]
  refine hsub.trans ?_
  rw [← hinv]
  exact (ENNReal.mul_le_iff_le_inv h0 ENNReal.ofReal_ne_top).1 h

theorem lintegral_snd_prod_le {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [SFinite μ] [IsProbabilityMeasure μ] [SFinite ν]
    (g : Y → ℝ≥0∞) : ∫⁻ r, g r.2 ∂(μ.prod ν) ≤ ∫⁻ y, g y ∂ν := by
  refine (lintegral_prod_le _).trans ?_
  simp

theorem lintegral_exp_sqrt_poisson (n : ℕ) :
    ∫⁻ p, ENNReal.ofReal (Real.exp (theta0 * (√(p : ℝ) - √((2 : ℝ) ^ n)) ^ 2))
      ∂(poissonMeasure (2 ^ n)) ≤ 19 := by
  have hr : (1 : ℝ) ≤ ((2 ^ n : ℝ≥0) : ℝ) := by
    push_cast; exact one_le_pow₀ (by norm_num)
  have h := poisson_exp_sqrt_sq_le (μ := poissonMeasure (2 ^ n)) (P := id) (r := 2 ^ n)
    HasLaw.id measurable_id hr (c := theta0) theta0_pos.le (by have := theta0_le; linarith)
  obtain ⟨hi, hv⟩ := h
  have : ∀ p : ℕ, (√((id p : ℕ) : ℝ) - √(((2 ^ n : ℝ≥0)) : ℝ)) ^ 2 =
      (√(p : ℝ) - √((2 : ℝ) ^ n)) ^ 2 := by intro p; push_cast; rfl
  simp only [this] at hi hv
  rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun _ => (Real.exp_pos _).le)]
  exact ENNReal.ofReal_le_of_le_toReal (by simpa using hv)

/-- Exponential moments along a path, Step 3, first display. -/
theorem psi_moment (n j : ℕ) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (theta0 * Psi n ω.1 ω.2.2 j)) ∂(Pdy n) ≤
      ENNReal.ofReal (Real.exp (theta0 * 2000000000 * n)) * 19 * 5 ^ n := by
  have hpt : ∀ ω : ℕ × ℝ × DT n, ENNReal.ofReal (Real.exp (theta0 * Psi n ω.1 ω.2.2 j)) ≤
      ENNReal.ofReal (Real.exp (theta0 * 2000000000 * n)) *
        (ENNReal.ofReal (Real.exp (theta0 * (√(ω.1 : ℝ) - √((2 : ℝ) ^ n)) ^ 2)) *
          ENNReal.ofReal (Real.exp (theta0 * Theta n ω.1 ω.2.2 j))) := by
    intro ω
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
      ← Real.exp_add, ← Real.exp_add]
    refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
    have := Psi_le n ω.1 ω.2.2 j
    have h0 := theta0_pos
    nlinarith
  unfold Pdy
  calc _ ≤ ∫⁻ ω, ENNReal.ofReal (Real.exp (theta0 * 2000000000 * n)) *
        (ENNReal.ofReal (Real.exp (theta0 * (√(ω.1 : ℝ) - √((2 : ℝ) ^ n)) ^ 2)) *
          ENNReal.ofReal (Real.exp (theta0 * Theta n ω.1 ω.2.2 j)))
        ∂((poissonMeasure (2 ^ n)).prod (saN.prod (muDT n))) := lintegral_mono hpt
    _ ≤ ∫⁻ p, ∫⁻ r, ENNReal.ofReal (Real.exp (theta0 * 2000000000 * n)) *
        (ENNReal.ofReal (Real.exp (theta0 * (√(p : ℝ) - √((2 : ℝ) ^ n)) ^ 2)) *
          ENNReal.ofReal (Real.exp (theta0 * Theta n p r.2 j))) ∂(saN.prod (muDT n))
        ∂(poissonMeasure (2 ^ n)) := lintegral_prod_le _
    _ ≤ ∫⁻ p, ENNReal.ofReal (Real.exp (theta0 * 2000000000 * n)) *
        (ENNReal.ofReal (Real.exp (theta0 * (√(p : ℝ) - √((2 : ℝ) ^ n)) ^ 2)) * 5 ^ n)
        ∂(poissonMeasure (2 ^ n)) := by
      refine lintegral_mono fun p => ?_
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine mul_le_mul_right ?_ _
      rw [show (fun r : ℝ × DT n => ENNReal.ofReal (Real.exp (theta0 *
          (√(p : ℝ) - √((2 : ℝ) ^ n)) ^ 2)) *
          ENNReal.ofReal (Real.exp (theta0 * Theta n p r.2 j))) = _ from rfl]
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine mul_le_mul_right ?_ _
      exact (lintegral_snd_prod_le saN (muDT n) _).trans (theta_moment n p j)
    _ = ENNReal.ofReal (Real.exp (theta0 * 2000000000 * n)) *
        ((∫⁻ p, ENNReal.ofReal (Real.exp (theta0 * (√(p : ℝ) - √((2 : ℝ) ^ n)) ^ 2))
          ∂(poissonMeasure (2 ^ n))) * 5 ^ n) := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_mul_const' _ _ (by simp)]
    _ ≤ ENNReal.ofReal (Real.exp (theta0 * 2000000000 * n)) * (19 * 5 ^ n) :=
      mul_le_mul_right (mul_le_mul_left (lintegral_exp_sqrt_poisson n) _) _
    _ = _ := by rw [mul_assoc (ENNReal.ofReal _)]

theorem integrable_exp_abs_saN (t : ℝ) : Integrable (fun y : ℝ => Real.exp (t * |y|)) saN := by
  have h1 : Integrable (fun y => Real.exp (t * y)) saN := integrable_exp_mul_gaussianReal t
  have h2 : Integrable (fun y => Real.exp ((-t) * y)) saN := integrable_exp_mul_gaussianReal (-t)
  refine (h1.add h2).mono' (by fun_prop) (ae_of_all _ fun y => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  rcases abs_cases y with ⟨h, _⟩ | ⟨h, _⟩
  · rw [h]; simp only [Pi.add_apply]; linarith [Real.exp_pos ((-t) * y)]
  · rw [h]; simp only [Pi.add_apply]
    have : t * -y = (-t) * y := by ring
    rw [this]; linarith [Real.exp_pos (t * y)]

/-- The root error `R` of pathwise error bounds(e), for the tree of depth `2L`. -/
noncomputable def Rroot (L : ℕ) (ω : ℕ × ℝ × DT (2 * L)) : ℝ :=
  |(ω.1 : ℝ) - 2 ^ (2 * L)| / 2 ^ L + |ω.2.1|

theorem measurable_Rroot (L : ℕ) : Measurable (Rroot L) := by
  unfold Rroot
  have h1 : Measurable (fun ω : ℕ × ℝ × DT (2 * L) => (ω.1 : ℝ)) :=
    (measurable_from_top (f := (Nat.cast : ℕ → ℝ))).comp measurable_fst
  have h2 : Measurable (fun ω : ℕ × ℝ × DT (2 * L) => ω.2.1) :=
    measurable_fst.comp measurable_snd
  have h4 : Measurable (fun ω : ℕ × ℝ × DT (2 * L) => (ω.1 : ℝ) - 2 ^ (2 * L)) :=
    h1.sub measurable_const
  have h3 := (h4.norm.div_const ((2 : ℝ) ^ L)).add h2.norm
  simp only [Real.norm_eq_abs] at h3
  exact h3

/-- Exponential moments along a path, second display (Step 4). -/
theorem Rroot_moment (L : ℕ) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (Rroot L ω / 4)) ∂(Pdy (2 * L)) ≤
      ENNReal.ofReal (Real.exp (3 / 4) + Real.exp (1 / 8)) := by
  have hpt : ∀ ω : ℕ × ℝ × DT (2 * L), ENNReal.ofReal (Real.exp (Rroot L ω / 4)) ≤
      2⁻¹ * (ENNReal.ofReal (Real.exp (|(ω.1 : ℝ) - 2 ^ (2 * L)| / 2 ^ L)) +
        ENNReal.ofReal (Real.exp (1 / 2 * |ω.2.1|))) := by
    intro ω
    set u := |(ω.1 : ℝ) - 2 ^ (2 * L)| / 2 ^ L with hu
    have hu0 : 0 ≤ u := by positivity
    have e1 : Real.exp (Rroot L ω / 4) = Real.exp (u / 4) * Real.exp (|ω.2.1| / 4) := by
      rw [← Real.exp_add]; congr 1; unfold Rroot; ring
    have e2 : Real.exp (u / 2) = Real.exp (u / 4) ^ 2 := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    have e3 : Real.exp (1 / 2 * |ω.2.1|) = Real.exp (|ω.2.1| / 4) ^ 2 := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    have e4 : Real.exp (u / 2) ≤ Real.exp u := Real.exp_le_exp.2 (by linarith)
    have hle : Real.exp (Rroot L ω / 4) ≤ (Real.exp u + Real.exp (1 / 2 * |ω.2.1|)) / 2 := by
      rw [e1]
      nlinarith [sq_nonneg (Real.exp (u / 4) - Real.exp (|ω.2.1| / 4))]
    calc _ ≤ ENNReal.ofReal ((Real.exp u + Real.exp (1 / 2 * |ω.2.1|)) / 2) :=
          ENNReal.ofReal_le_ofReal hle
      _ = _ := by
          rw [div_eq_mul_inv, mul_comm, ENNReal.ofReal_mul (by norm_num),
            ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le]
          congr 1
          rw [ENNReal.ofReal_inv_of_pos (by norm_num : (0:ℝ) < 2)]; simp
  have hP : ∫⁻ p, ENNReal.ofReal (Real.exp (|(p : ℝ) - 2 ^ (2 * L)| / 2 ^ L))
      ∂(poissonMeasure (2 ^ (2 * L))) ≤ ENNReal.ofReal (2 * Real.exp (3 / 4)) := by
    have hr : (1 : ℝ) ≤ ((2 ^ (2 * L) : ℝ≥0) : ℝ) := by
      push_cast; exact one_le_pow₀ (by norm_num)
    obtain ⟨hi, hv⟩ := poisson_exp_abs_le (μ := poissonMeasure (2 ^ (2 * L))) (P := id)
      (r := 2 ^ (2 * L)) HasLaw.id measurable_id hr
    have hs : √(((2 ^ (2 * L) : ℝ≥0)) : ℝ) = 2 ^ L := by
      push_cast; rw [pow_mul', Real.sqrt_sq (by positivity)]
    simp only [hs, id] at hi hv
    push_cast at hi hv
    rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun _ => (Real.exp_pos _).le)]
    exact ENNReal.ofReal_le_ofReal hv
  have hG : ∫⁻ z, ENNReal.ofReal (Real.exp (1 / 2 * |z|)) ∂saN ≤
      ENNReal.ofReal (2 * Real.exp (1 / 8)) := by
    rw [← ofReal_integral_eq_lintegral_ofReal (integrable_exp_abs_saN _)
      (ae_of_all _ fun _ => (Real.exp_pos _).le)]
    refine ENNReal.ofReal_le_ofReal ?_
    have := integral_exp_abs_saN_le (t := 1 / 2) (by norm_num)
    convert this using 2; norm_num
  unfold Pdy
  have hA : Measurable fun p : ℕ => ENNReal.ofReal (Real.exp (|(p : ℝ) - 2 ^ (2 * L)| / 2 ^ L)) :=
    measurable_from_top
  calc _ ≤ ∫⁻ ω, 2⁻¹ * (ENNReal.ofReal (Real.exp (|(ω.1 : ℝ) - 2 ^ (2 * L)| / 2 ^ L)) +
        ENNReal.ofReal (Real.exp (1 / 2 * |ω.2.1|)))
        ∂((poissonMeasure (2 ^ (2 * L))).prod (saN.prod (muDT (2 * L)))) := lintegral_mono hpt
    _ ≤ ∫⁻ p, ∫⁻ r, 2⁻¹ * (ENNReal.ofReal (Real.exp (|(p : ℝ) - 2 ^ (2 * L)| / 2 ^ L)) +
        ENNReal.ofReal (Real.exp (1 / 2 * |r.1|))) ∂(saN.prod (muDT (2 * L)))
        ∂(poissonMeasure (2 ^ (2 * L))) := lintegral_prod_le _
    _ ≤ ∫⁻ p, 2⁻¹ * (ENNReal.ofReal (Real.exp (|(p : ℝ) - 2 ^ (2 * L)| / 2 ^ L)) +
        ENNReal.ofReal (2 * Real.exp (1 / 8))) ∂(poissonMeasure (2 ^ (2 * L))) := by
      refine lintegral_mono fun p => ?_
      refine (lintegral_prod_le _).trans ?_
      simp only [lintegral_const, measure_univ, mul_one]
      rw [lintegral_const_mul' _ _ (by simp), lintegral_add_left measurable_const,
        lintegral_const, measure_univ, mul_one]
      exact mul_le_mul_right (add_le_add le_rfl hG) _
    _ = 2⁻¹ * ((∫⁻ p, ENNReal.ofReal (Real.exp (|(p : ℝ) - 2 ^ (2 * L)| / 2 ^ L))
        ∂(poissonMeasure (2 ^ (2 * L)))) + ENNReal.ofReal (2 * Real.exp (1 / 8))) := by
      rw [lintegral_const_mul' _ _ (by simp), lintegral_add_left hA, lintegral_const,
        measure_univ, mul_one]
    _ ≤ 2⁻¹ * (ENNReal.ofReal (2 * Real.exp (3 / 4)) + ENNReal.ofReal (2 * Real.exp (1 / 8))) :=
      mul_le_mul_right (add_le_add hP le_rfl) _
    _ = _ := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      rw [show (2 : ℝ≥0∞)⁻¹ = ENNReal.ofReal (1 / 2) by
        rw [one_div, ENNReal.ofReal_inv_of_pos (by norm_num)]; simp]
      rw [← ENNReal.ofReal_mul (by norm_num)]
      congr 1; ring

/-- The constant `c₃` of a1 for dyadic lengths. -/
noncomputable def c3 : ℝ :=
  (Real.log 2 + 2 * theta0 * 2000000000 + 2 * Real.log 5) / theta0

theorem psi_tail_real (L : ℕ) (x : ℝ) :
    Real.exp (-(theta0 * (c3 * L + x / 4))) *
        (Real.exp (theta0 * 2000000000 * ((2 * L : ℕ) : ℝ)) * 19 * 5 ^ (2 * L)) =
      19 * (2 ^ L)⁻¹ * Real.exp (-(theta0 * x / 4)) := by
  have h0 := theta0_pos
  have hc : theta0 * c3 = Real.log 2 + 2 * theta0 * 2000000000 + 2 * Real.log 5 := by
    unfold c3; field_simp
  have h5 : (5 : ℝ) ^ (2 * L) = Real.exp (((2 * L : ℕ) : ℝ) * Real.log 5) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
  have h2 : ((2 : ℝ) ^ L)⁻¹ = Real.exp (-((L : ℝ) * Real.log 2)) := by
    rw [Real.exp_neg, Real.exp_nat_mul, Real.exp_log (by norm_num)]
  rw [h5, h2]
  have : Real.exp (-(theta0 * (c3 * L + x / 4))) * Real.exp (theta0 * 2000000000 * ((2 * L : ℕ) : ℝ))
      * Real.exp (((2 * L : ℕ) : ℝ) * Real.log 5) =
      Real.exp (-((L : ℝ) * Real.log 2)) * Real.exp (-(theta0 * x / 4)) := by
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    congr 1
    push_cast
    nlinarith [hc]
  calc _ = 19 * (Real.exp (-(theta0 * (c3 * L + x / 4))) *
        Real.exp (theta0 * 2000000000 * ((2 * L : ℕ) : ℝ)) *
        Real.exp (((2 * L : ℕ) : ℝ) * Real.log 5)) := by ring
    _ = _ := by rw [this]; ring

/-- Pathwise error bounds(e), `|S_j| ≤ R + 2 Ψ(j)` for `j < 2^L`. -/
theorem Spart_le_R (L : ℕ) (ω : ℕ × ℝ × DT (2 * L)) (j : ℕ) (hj : j < 2 ^ L) :
    |Spart (2 * L) ω.1 (2 ^ L * ω.2.1) ω.2.2 j| ≤
      Rroot L ω + 2 * Psi (2 * L) ω.1 ω.2.2 j := by
  have h := Spart_le (2 * L) ω.1 (2 ^ L * ω.2.1) ω.2.2 j
    (le_trans hj.le (Nat.pow_le_pow_right (by norm_num) (by omega)))
  have hT : (0 : ℝ) < 2 ^ L := by positivity
  have e : (2 : ℝ) ^ (2 * L) = 2 ^ L * 2 ^ L := by rw [two_mul, pow_add]
  have hjL : (j : ℝ) ≤ 2 ^ L := by exact_mod_cast hj.le
  have he0 : |(ω.1 : ℝ) - 2 ^ (2 * L) - 2 ^ L * ω.2.1| ≤
      |(ω.1 : ℝ) - 2 ^ (2 * L)| + 2 ^ L * |ω.2.1| := by
    calc _ ≤ |(ω.1 : ℝ) - 2 ^ (2 * L)| + |2 ^ L * ω.2.1| := abs_sub _ _
      _ = _ := by rw [abs_mul, abs_of_pos hT]
  have hP := Psi_nonneg (2 * L) ω.1 ω.2.2 j
  have h1 : (j : ℝ) * |(ω.1 : ℝ) - 2 ^ (2 * L) - 2 ^ L * ω.2.1| ≤
      2 ^ L * (|(ω.1 : ℝ) - 2 ^ (2 * L)| + 2 ^ L * |ω.2.1|) :=
    mul_le_mul hjL he0 (abs_nonneg _) hT.le
  have hR : (2 : ℝ) ^ (2 * L) * Rroot L ω =
      2 ^ L * (|(ω.1 : ℝ) - 2 ^ (2 * L)| + 2 ^ L * |ω.2.1|) := by
    unfold Rroot; rw [e]; field_simp
  rw [pow_succ] at h
  have hpos : (0 : ℝ) < 2 ^ (2 * L) := by positivity
  by_contra hcon
  rw [not_le] at hcon
  have := mul_lt_mul_of_pos_left hcon hpos
  nlinarith

/-- A1 for dyadic lengths. -/
theorem prop_dyadic (L : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    Pdy (2 * L) {ω | ∃ j < 2 ^ L,
        2 * c3 * L + x ≤ |Spart (2 * L) ω.1 (2 ^ L * ω.2.1) ω.2.2 j|} ≤
      ENNReal.ofReal ((Real.exp (3 / 4) + Real.exp (1 / 8) + 19) *
        Real.exp (-(theta0 * x / 4))) := by
  have h0 := theta0_pos
  have hθ := theta0_le
  set AR := Real.exp (3 / 4) + Real.exp (1 / 8) with hAR
  -- the root part
  have hRt : Pdy (2 * L) {ω | x / 2 ≤ Rroot L ω} ≤
      ENNReal.ofReal (AR * Real.exp (-(theta0 * x / 4))) := by
    refine (markov_exp _ (measurable_Rroot L) (s := 1 / 4) (by norm_num) (x / 2)).trans ?_
    have := Rroot_moment L
    simp only [show ∀ ω : ℕ × ℝ × DT (2 * L), 1 / 4 * Rroot L ω = Rroot L ω / 4 from
      fun ω => by ring] at this ⊢
    calc _ ≤ ENNReal.ofReal (Real.exp (-(1 / 4 * (x / 2)))) * ENNReal.ofReal AR :=
          mul_le_mul_right this _
      _ = ENNReal.ofReal (Real.exp (-(1 / 4 * (x / 2))) * AR) :=
          (ENNReal.ofReal_mul (Real.exp_pos _).le).symm
      _ ≤ _ := by
          apply ENNReal.ofReal_le_ofReal
          have : Real.exp (-(1 / 4 * (x / 2))) ≤ Real.exp (-(theta0 * x / 4)) :=
            Real.exp_le_exp.2 (by nlinarith)
          have hAR0 : 0 ≤ AR := by positivity
          nlinarith
  -- the path part
  have hPs : ∀ j, Pdy (2 * L) {ω | c3 * L + x / 4 ≤ Psi (2 * L) ω.1 ω.2.2 j} ≤
      ENNReal.ofReal (19 * (2 ^ L)⁻¹ * Real.exp (-(theta0 * x / 4))) := by
    intro j
    have hm : Measurable (fun ω : ℕ × ℝ × DT (2 * L) => Psi (2 * L) ω.1 ω.2.2 j) :=
      (measurable_Psi (2 * L) j).comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd))
    refine (markov_exp _ hm h0 (c3 * L + x / 4)).trans ?_
    calc _ ≤ ENNReal.ofReal (Real.exp (-(theta0 * (c3 * L + x / 4)))) *
          (ENNReal.ofReal (Real.exp (theta0 * 2000000000 * ((2 * L : ℕ) : ℝ))) * 19 *
            5 ^ (2 * L)) := mul_le_mul_right (psi_moment (2 * L) j) _
      _ = ENNReal.ofReal (Real.exp (-(theta0 * (c3 * L + x / 4))) *
          (Real.exp (theta0 * 2000000000 * ((2 * L : ℕ) : ℝ)) * 19 * 5 ^ (2 * L))) := by
          rw [ENNReal.ofReal_mul (Real.exp_pos _).le, ENNReal.ofReal_mul (by positivity),
            ENNReal.ofReal_mul (Real.exp_pos _).le]
          simp
      _ = _ := by rw [psi_tail_real]
  -- the union
  have hsub : {ω : ℕ × ℝ × DT (2 * L) | ∃ j < 2 ^ L,
        2 * c3 * L + x ≤ |Spart (2 * L) ω.1 (2 ^ L * ω.2.1) ω.2.2 j|} ⊆
      {ω | x / 2 ≤ Rroot L ω} ∪ ⋃ j ∈ Finset.range (2 ^ L),
        {ω | c3 * L + x / 4 ≤ Psi (2 * L) ω.1 ω.2.2 j} := by
    rintro ω ⟨j, hj, hS⟩
    have h1 := Spart_le_R L ω j hj
    by_cases hR : x / 2 ≤ Rroot L ω
    · exact Or.inl hR
    · right
      simp only [mem_iUnion, Finset.mem_range, mem_ofPred_eq]
      refine ⟨j, hj, ?_⟩
      rw [not_le] at hR
      linarith
  have hU : Pdy (2 * L) (⋃ j ∈ Finset.range (2 ^ L),
        {ω | c3 * L + x / 4 ≤ Psi (2 * L) ω.1 ω.2.2 j}) ≤
      ENNReal.ofReal (19 * Real.exp (-(theta0 * x / 4))) := by
    refine (measure_biUnion_finset_le _ _).trans ?_
    calc _ ≤ ∑ j ∈ Finset.range (2 ^ L),
          ENNReal.ofReal (19 * (2 ^ L)⁻¹ * Real.exp (-(theta0 * x / 4))) :=
          Finset.sum_le_sum fun j _ => hPs j
      _ = ENNReal.ofReal (19 * Real.exp (-(theta0 * x / 4))) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
          congr 1
          push_cast
          field_simp
  calc _ ≤ Pdy (2 * L) ({ω | x / 2 ≤ Rroot L ω} ∪ ⋃ j ∈ Finset.range (2 ^ L),
        {ω | c3 * L + x / 4 ≤ Psi (2 * L) ω.1 ω.2.2 j}) := measure_mono hsub
    _ ≤ _ := measure_union_le _ _
    _ ≤ ENNReal.ofReal (AR * Real.exp (-(theta0 * x / 4))) +
        ENNReal.ofReal (19 * Real.exp (-(theta0 * x / 4))) := add_le_add hRt hU
    _ = _ := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1; ring

end StrongApprox
end ElboimSly
