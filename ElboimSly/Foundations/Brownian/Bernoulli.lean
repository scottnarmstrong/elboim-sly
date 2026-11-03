/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import Mathlib

/-!
# Adapted Bernoulli trials: upper tail

Adapted Bernoulli trials: upper tail.

Let `𝒢 ₀ ≤ 𝒢 ₁ ≤ ⋯` be `σ`-algebras, `G j ∈ 𝒢 j` and `E j ∈ 𝒢 (j+1)` events with
`P(E j ∩ G j ∩ F) ≤ p P(G j ∩ F)` for all `F ∈ 𝒢 j`. Then the number of `j < J` with
`ω ∈ E j ∩ G j` is at least `m` with probability at most `exp (-m + (e - 1) p J)`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ElboimSly.Brownian

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- The count `Y_k = ∑_{j<k} 1_{E_j ∩ G_j}`. -/
noncomputable def bernCount (E G : ℕ → Set Ω) (k : ℕ) (ω : Ω) : ℕ :=
  ∑ j ∈ Finset.range k, (E j ∩ G j).indicator (fun _ => (1 : ℕ)) ω

omit mΩ in
lemma bernCount_le (E G : ℕ → Set Ω) (k : ℕ) (ω : Ω) : bernCount E G k ω ≤ k := by
  unfold bernCount
  calc _ ≤ ∑ _j ∈ Finset.range k, 1 := Finset.sum_le_sum fun j _ => by
        by_cases h : ω ∈ E j ∩ G j <;> simp [h]
    _ = k := by simp

omit mΩ in
lemma bernCount_succ (E G : ℕ → Set Ω) (k : ℕ) (ω : Ω) :
    bernCount E G (k + 1) ω = bernCount E G k ω + (E k ∩ G k).indicator (fun _ => (1 : ℕ)) ω := by
  simp [bernCount, Finset.sum_range_succ]

omit mΩ in
lemma measurable_bernCount {𝒢 : ℕ → MeasurableSpace Ω} (h𝒢 : Monotone 𝒢) {E G : ℕ → Set Ω}
    (hG : ∀ j, MeasurableSet[𝒢 j] (G j)) (hE : ∀ j, MeasurableSet[𝒢 (j + 1)] (E j)) (k : ℕ) :
    Measurable[𝒢 k] (bernCount E G k) := by
  unfold bernCount
  let _ : MeasurableSpace Ω := 𝒢 k
  refine Finset.measurable_sum _ fun j hj => ?_
  have hjk : j < k := Finset.mem_range.1 hj
  have h1 : MeasurableSet[𝒢 k] (E j) := h𝒢 (Nat.succ_le_of_lt hjk) _ (hE j)
  have h2 : MeasurableSet[𝒢 k] (G j) := h𝒢 hjk.le _ (hG j)
  exact measurable_const.indicator (h1.inter h2)

/-- The exponential moment weight `W_k = e^{Y_k}` with values in `[0,∞]`. -/
noncomputable def bernWeight (E G : ℕ → Set Ω) (k : ℕ) (ω : Ω) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (bernCount E G k ω))

section Main

variable {𝒢 : ℕ → MeasurableSpace Ω} {E G : ℕ → Set Ω}

lemma measurable_bernCount' (h𝒢 : Monotone 𝒢) (hle : ∀ j, 𝒢 j ≤ mΩ)
    (hG : ∀ j, MeasurableSet[𝒢 j] (G j)) (hE : ∀ j, MeasurableSet[𝒢 (j + 1)] (E j)) (k : ℕ) :
    Measurable (bernCount E G k) :=
  (measurable_bernCount h𝒢 hG hE k).mono (hle k) le_rfl

lemma measurable_bernWeight (h𝒢 : Monotone 𝒢) (hle : ∀ j, 𝒢 j ≤ mΩ)
    (hG : ∀ j, MeasurableSet[𝒢 j] (G j)) (hE : ∀ j, MeasurableSet[𝒢 (j + 1)] (E j)) (k : ℕ) :
    Measurable (bernWeight E G k) :=
  ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
    (measurable_from_top.comp (measurable_bernCount' h𝒢 hle hG hE k)))

lemma lintegral_indicator_bernWeight (h𝒢 : Monotone 𝒢) (hle : ∀ j, 𝒢 j ≤ mΩ)
    (hG : ∀ j, MeasurableSet[𝒢 j] (G j)) (hE : ∀ j, MeasurableSet[𝒢 (j + 1)] (E j)) (k : ℕ)
    {U : Set Ω} (hU : MeasurableSet U) :
    ∫⁻ ω, U.indicator (bernWeight E G k) ω ∂P =
      ∑ l ∈ Finset.range (k + 1), ENNReal.ofReal (Real.exp l) *
        P (U ∩ {ω | bernCount E G k ω = l}) := by
  have hS : ∀ l : ℕ, MeasurableSet {ω | bernCount E G k ω = l} := fun l =>
    measurable_bernCount' h𝒢 hle hG hE k (measurableSet_singleton l)
  have hpt : ∀ ω, U.indicator (bernWeight E G k) ω = ∑ l ∈ Finset.range (k + 1),
      ENNReal.ofReal (Real.exp l) * (U ∩ {ω | bernCount E G k ω = l}).indicator 1 ω := by
    intro ω
    by_cases hω : ω ∈ U
    · rw [Set.indicator_of_mem hω]
      have hl : bernCount E G k ω ∈ Finset.range (k + 1) :=
        Finset.mem_range.2 (Nat.lt_succ_of_le (bernCount_le E G k ω))
      rw [Finset.sum_eq_single (bernCount E G k ω)]
      · simp [bernWeight, hω]
      · intro l _ hne
        have : ω ∉ U ∩ {ω | bernCount E G k ω = l} := fun h => hne h.2.symm
        simp [Set.indicator_of_notMem this]
      · intro h; exact absurd hl h
    · simp [hω]
  simp_rw [hpt]
  have hm : ∀ l : ℕ, Measurable fun ω => ENNReal.ofReal (Real.exp l) *
      (U ∩ {ω | bernCount E G k ω = l}).indicator (1 : Ω → ℝ≥0∞) ω := fun l =>
    (measurable_one.indicator (hU.inter (hS l))).const_mul _
  rw [lintegral_finsetSum _ fun l _ => hm l]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [lintegral_const_mul _ (measurable_one.indicator (hU.inter (hS l))),
    lintegral_indicator_one (hU.inter (hS l))]

lemma bern_key (h𝒢 : Monotone 𝒢) (hle : ∀ j, 𝒢 j ≤ mΩ)
    (hG : ∀ j, MeasurableSet[𝒢 j] (G j)) (hE : ∀ j, MeasurableSet[𝒢 (j + 1)] (E j)) {p : ℝ}
    (hP : ∀ j, ∀ F, MeasurableSet[𝒢 j] F → P (E j ∩ G j ∩ F) ≤ ENNReal.ofReal p * P (G j ∩ F))
    (k : ℕ) :
    ∫⁻ ω, (E k ∩ G k).indicator (bernWeight E G k) ω ∂P ≤
      ENNReal.ofReal p * ∫⁻ ω, (G k).indicator (bernWeight E G k) ω ∂P := by
  have hEm : MeasurableSet (E k ∩ G k) := (hle _ _ (hE k)).inter (hle _ _ (hG k))
  have hGm : MeasurableSet (G k) := hle _ _ (hG k)
  rw [lintegral_indicator_bernWeight h𝒢 hle hG hE k hEm,
    lintegral_indicator_bernWeight h𝒢 hle hG hE k hGm, Finset.mul_sum]
  refine Finset.sum_le_sum fun l _ => ?_
  have hSl : MeasurableSet[𝒢 k] {ω | bernCount E G k ω = l} :=
    measurable_bernCount h𝒢 hG hE k (measurableSet_singleton l)
  calc ENNReal.ofReal (Real.exp l) * P (E k ∩ G k ∩ {ω | bernCount E G k ω = l})
      ≤ ENNReal.ofReal (Real.exp l) * (ENNReal.ofReal p * P (G k ∩ {ω | bernCount E G k ω = l})) :=
        mul_le_mul_right (hP k _ hSl) _
    _ = _ := by ring

omit mΩ in
lemma bern_pointwise (E G : ℕ → Set Ω) (k : ℕ) (ω : Ω) :
    bernWeight E G (k + 1) ω = bernWeight E G k ω +
      ENNReal.ofReal (Real.exp 1 - 1) * (E k ∩ G k).indicator (bernWeight E G k) ω := by
  by_cases hω : ω ∈ E k ∩ G k
  · rw [Set.indicator_of_mem hω]
    unfold bernWeight
    rw [bernCount_succ, Set.indicator_of_mem hω]
    push_cast
    rw [Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le]
    have : ENNReal.ofReal (Real.exp 1) = 1 + ENNReal.ofReal (Real.exp 1 - 1) := by
      rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add zero_le_one (by linarith [Real.add_one_le_exp (1 : ℝ)])]
      congr 1; ring
    rw [this]; ring
  · rw [Set.indicator_of_notMem hω]
    unfold bernWeight
    rw [bernCount_succ, Set.indicator_of_notMem hω]
    simp

theorem bern_step [IsProbabilityMeasure P] (h𝒢 : Monotone 𝒢) (hle : ∀ j, 𝒢 j ≤ mΩ)
    (hG : ∀ j, MeasurableSet[𝒢 j] (G j)) (hE : ∀ j, MeasurableSet[𝒢 (j + 1)] (E j)) {p : ℝ}
    (_hp : 0 ≤ p)
    (hP : ∀ j, ∀ F, MeasurableSet[𝒢 j] F → P (E j ∩ G j ∩ F) ≤ ENNReal.ofReal p * P (G j ∩ F))
    (k : ℕ) :
    ∫⁻ ω, bernWeight E G (k + 1) ω ∂P ≤
      (1 + ENNReal.ofReal ((Real.exp 1 - 1) * p)) * ∫⁻ ω, bernWeight E G k ω ∂P := by
  have hEm : MeasurableSet (E k ∩ G k) := (hle _ _ (hE k)).inter (hle _ _ (hG k))
  have hWm := measurable_bernWeight h𝒢 hle hG hE k
  have h1 : (0 : ℝ) ≤ Real.exp 1 - 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  simp_rw [bern_pointwise E G k]
  rw [lintegral_add_left hWm, lintegral_const_mul _ (hWm.indicator hEm)]
  have h2 := bern_key h𝒢 hle hG hE hP k
  have h3 : ∫⁻ ω, (G k).indicator (bernWeight E G k) ω ∂P ≤ ∫⁻ ω, bernWeight E G k ω ∂P :=
    lintegral_mono fun ω => Set.indicator_le_self _ _ ω
  calc _ ≤ ∫⁻ ω, bernWeight E G k ω ∂P + ENNReal.ofReal (Real.exp 1 - 1) *
        (ENNReal.ofReal p * ∫⁻ ω, bernWeight E G k ω ∂P) :=
        add_le_add le_rfl (mul_le_mul_right (h2.trans (mul_le_mul_right h3 _)) _)
    _ = _ := by
        rw [ENNReal.ofReal_mul h1, add_mul, one_mul, mul_assoc]

/-- Adapted Bernoulli trials: upper tail. Adapted Bernoulli trials, upper tail: for every real `m`,
`P(∑_{j<J} 1_{E_j ∩ G_j} ≥ m) ≤ exp (-m + (e - 1) p J)`. -/
theorem bernoulli_upper_tail [IsProbabilityMeasure P] (h𝒢 : Monotone 𝒢) (hle : ∀ j, 𝒢 j ≤ mΩ)
    (hG : ∀ j, MeasurableSet[𝒢 j] (G j)) (hE : ∀ j, MeasurableSet[𝒢 (j + 1)] (E j)) {p : ℝ}
    (hp : 0 ≤ p)
    (hP : ∀ j, ∀ F, MeasurableSet[𝒢 j] F → P (E j ∩ G j ∩ F) ≤ ENNReal.ofReal p * P (G j ∩ F))
    (J : ℕ) (m : ℝ) :
    P {ω | m ≤ (bernCount E G J ω : ℝ)} ≤
      ENNReal.ofReal (Real.exp (-m + (Real.exp 1 - 1) * p * J)) := by
  have h1 : (0 : ℝ) ≤ Real.exp 1 - 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hmom : ∀ k : ℕ, ∫⁻ ω, bernWeight E G k ω ∂P ≤
      ENNReal.ofReal (Real.exp ((Real.exp 1 - 1) * p * k)) := by
    intro k
    induction k with
    | zero => simp [bernWeight, bernCount]
    | succ k ih =>
      refine (bern_step h𝒢 hle hG hE hp hP k).trans ?_
      have h2 : 1 + ENNReal.ofReal ((Real.exp 1 - 1) * p) ≤
          ENNReal.ofReal (Real.exp ((Real.exp 1 - 1) * p)) := by
        rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add zero_le_one (mul_nonneg h1 hp)]
        exact ENNReal.ofReal_le_ofReal (by linarith [Real.add_one_le_exp ((Real.exp 1 - 1) * p)])
      calc _ ≤ ENNReal.ofReal (Real.exp ((Real.exp 1 - 1) * p)) *
            ENNReal.ofReal (Real.exp ((Real.exp 1 - 1) * p * k)) := mul_le_mul h2 ih zero_le zero_le
        _ = _ := by
          rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
          congr 2; push_cast; ring
  have hWm := measurable_bernWeight h𝒢 hle hG hE J
  have hmk := mul_meas_ge_le_lintegral (μ := P) hWm (ENNReal.ofReal (Real.exp m))
  have hsub : {ω | m ≤ (bernCount E G J ω : ℝ)} ⊆
      {ω | ENNReal.ofReal (Real.exp m) ≤ bernWeight E G J ω} := fun ω hω =>
    ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 hω)
  calc P {ω | m ≤ (bernCount E G J ω : ℝ)}
      ≤ P {ω | ENNReal.ofReal (Real.exp m) ≤ bernWeight E G J ω} := measure_mono hsub
    _ = ENNReal.ofReal (Real.exp (-m)) * (ENNReal.ofReal (Real.exp m) *
          P {ω | ENNReal.ofReal (Real.exp m) ≤ bernWeight E G J ω}) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
        simp
    _ ≤ ENNReal.ofReal (Real.exp (-m)) * ENNReal.ofReal (Real.exp ((Real.exp 1 - 1) * p * J)) :=
        mul_le_mul le_rfl (hmk.trans (hmom J)) zero_le zero_le
    _ = _ := by
        rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]

end Main

end ElboimSly.Brownian
