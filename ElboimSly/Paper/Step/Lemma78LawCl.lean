/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Step.Lemma78Sets
public import ElboimSly.Paper.Step.Levels
public import ElboimSly.Paper.Avoid.Claim2Final
public import ElboimSly.Foundations.Brownian.FarHit
public import Mathlib

/-!
# The closing event

One excursion succeeds with probability at least frac12, "Closing": by levels (c) (`stepRegime_H2_pow`),
`P(∃ m ≥ 1, mβ < 4ⁿ, W(mβ) = 0) ≤ Σ_{m≥1}(mβ)^{-d/2+0.1} ≤ 2β^{-2}` for the regenerated walk `W`.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Step

open ElboimSly.Paper ElboimSly.Cyclic

theorem sum_inv_sq_le_two (M : ℕ) : ∑ m ∈ Finset.range M, (1 : ℝ) / ((m + 1 : ℕ) : ℝ) ^ 2 ≤ 2 := by
  have h : ∀ M : ℕ, ∑ m ∈ Finset.range (M + 1), (1 : ℝ) / ((m + 1 : ℕ) : ℝ) ^ 2 ≤
      2 - 1 / ((M : ℝ) + 1) := by
    intro M
    induction M with
    | zero => norm_num
    | succ M ih =>
      rw [Finset.sum_range_succ]
      have h1 : (1 : ℝ) / ((M + 1 + 1 : ℕ) : ℝ) ^ 2 ≤ 1 / ((M : ℝ) + 1) - 1 / ((M : ℝ) + 2) := by
        push_cast
        rw [div_sub_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity)
          (by positivity)]
        nlinarith [sq_nonneg (M : ℝ)]
      push_cast at *
      have e : (1 : ℝ) / ((M : ℝ) + 1 + 1) = 1 / ((M : ℝ) + 2) := by ring_nf
      rw [e]
      linarith
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · simp
  · obtain ⟨K, rfl⟩ : ∃ K, M = K + 1 := ⟨M - 1, by omega⟩
    have := h K
    have : (0 : ℝ) ≤ 1 / ((K : ℝ) + 1) := by positivity
    linarith

variable {d : ℕ} {β : ℝ} [Fact (0 < β)]

/-- The closing event has probability at most `2β^{-2}` for the regenerated walk. -/
theorem step78_law_cl {n₁ n : ℕ} {t₀ : ℝ} (hd : 5 ≤ d) (hβ1 : 1 ≤ β)
    (hreg : StepRegime d n₁ β n t₀) (hβ4 : (4 : ℝ) ^ (n₁ + 2) ≤ β)
    {Ω₀ : Type} [MeasurableSpace Ω₀] {Pr₀ : Measure Ω₀} {N₀ : Ω₀ → Measure (CycS ℕ d β)}
    (hN₀ : IsPoissonPointProcess N₀ (cycIntensity ℕ d β) Pr₀) :
    (Pr₀.map (avoidPath N₀)) (step78Scl d β n) ≤ ENNReal.ofReal (2 * (β ^ 2)⁻¹) := by
  have hH2 := stepRegime_H2_pow hreg hβ4
  have hm : AEMeasurable (avoidPath N₀) Pr₀ := aemeasurable_avoidPath hN₀
  have hβ0 : 0 < β := Fact.out
  set f : ℕ → ℝ := fun m => (1 : ℝ) / ((m + 1 : ℕ) : ℝ) ^ 2 * (β ^ 2)⁻¹ with hf
  have hscl : step78Scl d β n ⊆ ⋃ m : ℕ, {y | y ((((m + 1 : ℕ) : ℝ) * β).toNNReal) = 0 ∧
      (((m + 1 : ℕ) : ℝ) * β < (4 : ℝ) ^ n)} := by
    rintro y ⟨k, hk1, hk4, hk0⟩
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    exact mem_iUnion.2 ⟨m, hk0, hk4⟩
  have hterm : ∀ m : ℕ, (Pr₀.map (avoidPath N₀)) {y : ℝ≥0 → Fin d → ℤ |
      y ((((m + 1 : ℕ) : ℝ) * β).toNNReal) = 0 ∧ (((m + 1 : ℕ) : ℝ) * β < (4 : ℝ) ^ n)} ≤
      ENNReal.ofReal (f m) := by
    intro m
    set r : ℝ := ((m + 1 : ℕ) : ℝ) * β with hr
    have hr1 : 1 ≤ r := by
      rw [hr]
      have : (1 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le m)
      nlinarith
    by_cases h4 : r < (4 : ℝ) ^ n
    · have hset : MeasurableSet {y : ℝ≥0 → Fin d → ℤ |
          y (r.toNNReal) = 0 ∧ r < (4 : ℝ) ^ n} := by
        have : {y : ℝ≥0 → Fin d → ℤ | y (r.toNNReal) = 0 ∧ r < (4 : ℝ) ^ n} =
            {y | y (r.toNNReal) = 0} := by ext y; simp [h4]
        rw [this]
        exact measurableSet_eq_fun (measurable_pi_apply _) measurable_const
      rw [Measure.map_apply_of_aemeasurable hm hset]
      have hsub : avoidPath N₀ ⁻¹' {y : ℝ≥0 → Fin d → ℤ | y (r.toNNReal) = 0 ∧ r < (4 : ℝ) ^ n} =
          {ω | regenWalk (fun k => copyEnv (N₀ ω) k) r = 0} := by
        ext ω
        simp only [mem_preimage, mem_ofPred_eq, h4, and_true]
        show avoidWalk N₀ ω ((r.toNNReal : ℝ≥0) : ℝ) = 0 ↔ _
        rw [Real.coe_toNNReal _ (by linarith)]
        rfl
      rw [hsub]
      refine (hH2 Ω₀ Pr₀ N₀ hN₀ r ⟨hr1, h4.le⟩ 0).trans (ENNReal.ofReal_le_ofReal ?_)
      have hd5 : -(d : ℝ) / 2 + 1 / 10 ≤ -2 := by
        have : (5 : ℝ) ≤ d := by exact_mod_cast hd
        linarith
      calc r ^ (-(d : ℝ) / 2 + 1 / 10) ≤ r ^ (-2 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hr1 hd5
        _ = f m := by
            rw [hf, hr, Real.rpow_neg (by linarith), show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num,
              Real.rpow_natCast]
            simp only
            rw [mul_pow, one_div, ← mul_inv]
    · have : {y : ℝ≥0 → Fin d → ℤ | y (r.toNNReal) = 0 ∧ r < (4 : ℝ) ^ n} = ∅ := by
        ext y; simp [h4]
      rw [this]; simp
  calc (Pr₀.map (avoidPath N₀)) (step78Scl d β n)
      ≤ (Pr₀.map (avoidPath N₀)) (⋃ m : ℕ, {y | y ((((m + 1 : ℕ) : ℝ) * β).toNNReal) = 0 ∧
        (((m + 1 : ℕ) : ℝ) * β < (4 : ℝ) ^ n)}) := measure_mono hscl
    _ ≤ ∑' m : ℕ, (Pr₀.map (avoidPath N₀)) {y | y ((((m + 1 : ℕ) : ℝ) * β).toNNReal) = 0 ∧
        (((m + 1 : ℕ) : ℝ) * β < (4 : ℝ) ^ n)} := measure_iUnion_le _
    _ ≤ ∑' m : ℕ, ENNReal.ofReal (f m) := ENNReal.tsum_le_tsum hterm
    _ ≤ ENNReal.ofReal (2 * (β ^ 2)⁻¹) := by
        refine ElboimSly.Brownian.tsum_ofReal_le_of_partial (fun m => by rw [hf]; positivity)
          fun M => ?_
        have : ∑ m ∈ Finset.range M, f m = (∑ m ∈ Finset.range M,
            (1 : ℝ) / ((m + 1 : ℕ) : ℝ) ^ 2) * (β ^ 2)⁻¹ := by
          rw [Finset.sum_mul]
        rw [this]
        exact mul_le_mul_of_nonneg_right (sum_inv_sq_le_two M) (by positivity)

end ElboimSly.Paper.Step

end
