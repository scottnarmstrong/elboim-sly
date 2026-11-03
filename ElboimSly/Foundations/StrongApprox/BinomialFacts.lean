/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.StrongApprox.Binomial

/-!
# Binomial facts

Binomial facts (Part I): symmetry, the
moment generating function, sub-Gaussian tails and the square-root tails.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology Finset
open scoped NNReal Real ENNReal unitInterval

namespace ElboimSly
namespace StrongApprox

/-- The (finite) moment generating function of `Bin(m,1/2) - m/2`. -/
noncomputable def sabMgf (m : ℕ) (θ : ℝ) : ℝ :=
  ∑ k ∈ range (m + 1), sab m k * Real.exp (θ * ((k : ℝ) - m / 2))

/-- Binomial facts(b), first equality: `E e^{θ(Y-μ)} = cosh(θ/2)^m`. -/
theorem sabMgf_eq (m : ℕ) (θ : ℝ) : sabMgf m θ = Real.cosh (θ / 2) ^ m := by
  unfold sabMgf
  rw [Real.cosh_eq, show (Real.exp (θ / 2) + Real.exp (-(θ / 2))) / 2 =
    Real.exp (θ / 2) / 2 + Real.exp (-(θ / 2)) / 2 by ring, add_pow]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k ≤ m := by simpa [Nat.lt_succ_iff] using hk
  rw [sab_natCast, div_pow, div_pow, ← Real.exp_nat_mul, ← Real.exp_nat_mul, Nat.cast_sub hk']
  have h2 : (2 : ℝ) ^ k * 2 ^ (m - k) = 2 ^ m := by rw [← pow_add, Nat.add_sub_cancel' hk']
  have h3 : Real.exp (↑k * (θ / 2)) * Real.exp (((m : ℝ) - k) * -(θ / 2)) =
      Real.exp (θ * ((k : ℝ) - m / 2)) := by
    rw [← Real.exp_add]; congr 1; ring
  have h4 : (0 : ℝ) < 2 ^ k := by positivity
  have h5 : (0 : ℝ) < 2 ^ (m - k) := by positivity
  rw [← h3, ← h2]; field_simp

/-- Binomial facts(b), the bound `cosh(θ/2)^m ≤ e^{mθ²/8}`. -/
theorem sabMgf_le (m : ℕ) (θ : ℝ) : sabMgf m θ ≤ Real.exp (m * θ ^ 2 / 8) := by
  rw [sabMgf_eq]
  have h := Real.cosh_le_exp_half_sq (θ / 2)
  have h0 : 0 ≤ Real.cosh (θ / 2) := (Real.cosh_pos _).le
  calc Real.cosh (θ / 2) ^ m ≤ Real.exp ((θ / 2) ^ 2 / 2) ^ m := by gcongr
    _ = Real.exp (m * θ ^ 2 / 8) := by rw [← Real.exp_nat_mul]; congr 1; ring

/-- Binomial facts(b), a Markov inequality at the level of finite sums. -/
theorem sab_tail_aux (m : ℕ) (θ r : ℝ) (p : ℕ → Prop) [DecidablePred p]
    (hp : ∀ k, p k → r ≤ θ * ((k : ℝ) - m / 2)) :
    ∑ k ∈ range (m + 1), (if p k then sab m k else 0) ≤ Real.exp (m * θ ^ 2 / 8 - r) := by
  have h1 : ∑ k ∈ range (m + 1), (if p k then sab m k else 0) ≤
      ∑ k ∈ range (m + 1), sab m k * Real.exp (θ * ((k : ℝ) - m / 2)) * Real.exp (-r) := by
    refine Finset.sum_le_sum fun k _ => ?_
    split_ifs with h
    · have : 1 ≤ Real.exp (θ * ((k : ℝ) - m / 2)) * Real.exp (-r) := by
        rw [← Real.exp_add]; exact Real.one_le_exp (by linarith [hp k h])
      have := sab_nonneg m k
      nlinarith
    · have := sab_nonneg m k
      positivity
  refine h1.trans ?_
  rw [← Finset.sum_mul]
  change sabMgf m θ * Real.exp (-r) ≤ _
  rw [sub_eq_add_neg, Real.exp_add]
  exact mul_le_mul_of_nonneg_right (sabMgf_le m θ) (Real.exp_pos _).le

/-- Binomial facts(b), upper tail, finite-sum form. -/
theorem sab_upper_tail (m : ℕ) (hm : 1 ≤ m) {ρ : ℝ} (hρ : 0 ≤ ρ) (p : ℕ → Prop) [DecidablePred p]
    (hp : ∀ k, p k → ρ ≤ (k : ℝ) - m / 2) :
    ∑ k ∈ range (m + 1), (if p k then sab m k else 0) ≤ Real.exp (-(2 * ρ ^ 2 / m)) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have := sab_tail_aux m (4 * ρ / m) (4 * ρ / m * ρ) p (fun k hk => by
    have := hp k hk
    have : 0 ≤ 4 * ρ / m := by positivity
    nlinarith)
  refine this.trans (le_of_eq ?_)
  congr 1
  field_simp
  ring

/-- Binomial facts(b), lower tail, finite-sum form. -/
theorem sab_lower_tail (m : ℕ) (hm : 1 ≤ m) {ρ : ℝ} (hρ : 0 ≤ ρ) (p : ℕ → Prop) [DecidablePred p]
    (hp : ∀ k, p k → (k : ℝ) - m / 2 ≤ -ρ) :
    ∑ k ∈ range (m + 1), (if p k then sab m k else 0) ≤ Real.exp (-(2 * ρ ^ 2 / m)) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have := sab_tail_aux m (-(4 * ρ / m)) (4 * ρ / m * ρ) p (fun k hk => by
    have := hp k hk
    have : 0 ≤ 4 * ρ / m := by positivity
    nlinarith)
  refine this.trans (le_of_eq ?_)
  congr 1
  field_simp
  ring

/-- Binomial facts(a), `P(Y ≥ μ) ≥ 1/2`, finite-sum form. -/
theorem sab_half_le_sum (m : ℕ) :
    1 / 2 ≤ ∑ k ∈ range (m + 1), (if (m : ℝ) / 2 ≤ k then sab m k else 0) := by
  set S1 := ∑ k ∈ range (m + 1), (if (m : ℝ) / 2 ≤ k then sab m k else 0) with hS1
  set S2 := ∑ k ∈ range (m + 1), (if (k : ℝ) ≤ m / 2 then sab m k else 0) with hS2
  have h12 : S1 = S2 := by
    rw [hS1, hS2, ← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' : k ≤ m := by simpa [Nat.lt_succ_iff] using hk
    have e : m + 1 - 1 - k = m - k := by omega
    rw [e, Nat.cast_sub hk']
    have : sab m ((m - k : ℕ)) = sab m k := by
      rw [sab_natCast, sab_natCast, Nat.choose_symm hk']
    rw [this]
    by_cases h : (k : ℝ) ≤ m / 2
    · have h' : (m : ℝ) / 2 ≤ m - k := by linarith
      simp only [h, h', ite_true]
    · have h' : ¬ ((m : ℝ) / 2 ≤ m - k) := by intro hh; apply h; linarith
      simp only [h, h', ite_false]
  have hsum : 1 ≤ S1 + S2 := by
    rw [← sum_sab m, hS1, hS2, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun k _ => ?_
    have := sab_nonneg m k
    by_cases h : (m : ℝ) / 2 ≤ k
    · simp only [h, ite_true]
      split_ifs <;> linarith
    · have h' : (k : ℝ) ≤ m / 2 := by linarith [not_le.1 h]
      simp only [h, h', ite_true, ite_false]; linarith
  linarith

/-! ### Square-root tails -/

open Classical in
theorem sab_sqrt_upper (m : ℕ) (hm : 1 ≤ m) {t : ℝ} (ht : 0 < t) :
    ∑ k ∈ range (m + 1), (if t ≤ √(k : ℝ) - √((m : ℝ) / 2) then sab m k else 0) ≤
      Real.exp (-(4 * t ^ 2)) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hμ : 0 ≤ (m : ℝ) / 2 := by positivity
  have hsq := Real.sq_sqrt hμ
  have hsn := Real.sqrt_nonneg ((m : ℝ) / 2)
  have h := sab_upper_tail m hm (ρ := 2 * t * √((m : ℝ) / 2)) (by positivity)
    (fun k => t ≤ √(k : ℝ) - √((m : ℝ) / 2)) (fun k hk => by
      have h1 : √((m : ℝ) / 2) + t ≤ √(k : ℝ) := by linarith
      have h2 := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) k)
      nlinarith)
  refine h.trans (le_of_eq ?_)
  congr 1
  field_simp
  rw [hsq]
  ring

open Classical in
theorem sab_sqrt_lower (m : ℕ) (hm : 1 ≤ m) {t : ℝ} (ht : 0 < t) :
    ∑ k ∈ range (m + 1), (if √(k : ℝ) - √((m : ℝ) / 2) ≤ -t then sab m k else 0) ≤
      Real.exp (-(t ^ 2)) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hμ : 0 ≤ (m : ℝ) / 2 := by positivity
  have hsq := Real.sq_sqrt hμ
  have hsn := Real.sqrt_nonneg ((m : ℝ) / 2)
  by_cases htm : √((m : ℝ) / 2) < t
  · have : ∀ k ∈ range (m + 1), (if √(k : ℝ) - √((m : ℝ) / 2) ≤ -t then sab m k else 0) = 0 := by
      intro k _
      have := Real.sqrt_nonneg (k : ℝ)
      have hn : ¬ (√(k : ℝ) - √((m : ℝ) / 2) ≤ -t) := not_le.2 (by linarith)
      simp only [hn, ite_false]
    rw [Finset.sum_eq_zero this]
    exact (Real.exp_pos _).le
  · rw [not_lt] at htm
    have h := sab_lower_tail m hm (ρ := t * √((m : ℝ) / 2)) (by positivity)
      (fun k => √(k : ℝ) - √((m : ℝ) / 2) ≤ -t) (fun k hk => by
        have h1 : √(k : ℝ) ≤ √((m : ℝ) / 2) - t := by linarith
        have h2 := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) k)
        have h3 := Real.sqrt_nonneg (k : ℝ)
        have h4 : (k : ℝ) ≤ (√((m : ℝ) / 2) - t) ^ 2 := by
          rw [← h2]; exact pow_le_pow_left₀ h3 h1 2
        nlinarith [mul_nonneg ht.le (sub_nonneg.2 htm)])
    refine h.trans (le_of_eq ?_)
    congr 1
    field_simp
    rw [hsq]
    ring

theorem ite_sq_le_add (ρ b x : ℝ) (hx : 0 ≤ x) :
    (if ρ ≤ b ^ 2 then x else 0) ≤
      (if √ρ ≤ b then x else 0) + (if b ≤ -√ρ then x else 0) := by
  by_cases h : ρ ≤ b ^ 2
  · have h1 : √ρ ≤ |b| := by
      calc √ρ ≤ √(b ^ 2) := Real.sqrt_le_sqrt h
        _ = |b| := Real.sqrt_sq_eq_abs b
    rcases le_abs'.1 h1 with h2 | h2
    · simp only [h, h2, ite_true]
      split_ifs <;> linarith
    · simp only [h, h2, ite_true]
      split_ifs <;> linarith
  · split_ifs <;> linarith

open Classical in
theorem sab_sqrt_sq_tail (m : ℕ) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    ∑ k ∈ range (m + 1), (if ρ ≤ (√(k : ℝ) - √((m : ℝ) / 2)) ^ 2 then sab m k else 0) ≤
      2 * Real.exp (-(1 * ρ)) := by
  rcases hρ.eq_or_lt with rfl | hρp
  · simp only [mul_zero, neg_zero, Real.exp_zero, mul_one]
    calc _ ≤ ∑ k ∈ range (m + 1), sab m k := Finset.sum_le_sum fun k _ => by
          split_ifs
          · exact le_rfl
          · exact sab_nonneg m k
      _ = 1 := sum_sab m
      _ ≤ 2 := by norm_num
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have : ∀ k ∈ range (0 + 1), (if ρ ≤ (√(k : ℝ) - √(((0 : ℕ) : ℝ) / 2)) ^ 2 then sab 0 k else 0) = 0 := by
      intro k hk
      have : k = 0 := by simpa using hk
      subst this
      have h0 : ¬ ρ ≤ (√(((0 : ℕ) : ℝ)) - √(((0 : ℕ) : ℝ) / 2)) ^ 2 := by simpa using hρp
      simp only [Nat.cast_zero] at h0 ⊢
      simp only [h0, ite_false]
    rw [Finset.sum_eq_zero this]
    positivity
  have ht : 0 < √ρ := Real.sqrt_pos.2 hρp
  have hρ2 : (√ρ) ^ 2 = ρ := Real.sq_sqrt hρ
  calc _ ≤ ∑ k ∈ range (m + 1), ((if √ρ ≤ √(k : ℝ) - √((m : ℝ) / 2) then sab m k else 0) +
        (if √(k : ℝ) - √((m : ℝ) / 2) ≤ -√ρ then sab m k else 0)) := by
        refine Finset.sum_le_sum fun k _ => ?_
        exact ite_sq_le_add ρ _ _ (sab_nonneg m k)
    _ ≤ Real.exp (-(4 * √ρ ^ 2)) + Real.exp (-(√ρ ^ 2)) := by
        rw [Finset.sum_add_distrib]
        exact add_le_add (sab_sqrt_upper m hm ht) (sab_sqrt_lower m hm ht)
    _ ≤ 2 * Real.exp (-(1 * ρ)) := by
        rw [hρ2, one_mul]
        have : Real.exp (-(4 * ρ)) ≤ Real.exp (-ρ) := Real.exp_le_exp.2 (by linarith)
        linarith

/-! ### Probabilistic form of binomial facts -/

section Prob

open Classical

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {Y : Ω → ℕ} {m : ℕ}

/-- Binomial facts(c), `P(β² ≥ ρ) ≤ 2e^{-ρ}` (all `m ≥ 0`). -/
theorem binomial_sqrt_sq_tail (hY : HasLaw Y (binomial m sahalf) P) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    P.real {ω | ρ ≤ (√(Y ω : ℝ) - √((m : ℝ) / 2)) ^ 2} ≤ 2 * Real.exp (-(1 * ρ)) := by
  rw [hasLaw_real_pred_half hY (fun k => ρ ≤ (√(k : ℝ) - √((m : ℝ) / 2)) ^ 2)]
  exact sab_sqrt_sq_tail m hρ

/-- Binomial facts(c), `E e^{cβ²} ≤ 7` for `0 ≤ c ≤ 1/2` (all `m ≥ 0`). -/
theorem binomial_exp_sqrt_sq_le [IsProbabilityMeasure P] (hY : HasLaw Y (binomial m sahalf) P)
    (hYm : Measurable Y) {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1 / 2) :
    Integrable (fun ω => Real.exp (c * (√(Y ω : ℝ) - √((m : ℝ) / 2)) ^ 2)) P ∧
      ∫ ω, Real.exp (c * (√(Y ω : ℝ) - √((m : ℝ) / 2)) ^ 2) ∂P ≤ 7 := by
  have hβ : Measurable fun ω => (√(Y ω : ℝ) - √((m : ℝ) / 2)) ^ 2 := by fun_prop
  have := integral_exp_le_layerCakeBound (P := P) (Y := fun ω => (√(Y ω : ℝ) - √((m : ℝ) / 2)) ^ 2)
    hβ (fun ω => sq_nonneg _) (c := c) (κ := 1) hc0 (by linarith)
    (fun ρ hρ => binomial_sqrt_sq_tail hY hρ)
  refine ⟨this.1, this.2.trans ?_⟩
  exact (layerCakeBound_mono hc1 (by norm_num)).trans layerCakeBound_one_half_le

end Prob

end StrongApprox
end ElboimSly
