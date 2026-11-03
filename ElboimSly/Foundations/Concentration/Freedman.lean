/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Concentration.FreedmanSupermartingale

/-!
# Freedman's inequality, maximal form

Freedman's inequality, maximal form (a)-(c). The proof follows the written proof: the stopped exponential
supermartingale of `FreedmanSupermartingale`, the Chernoff bound, and the choice
`λ = x / (V + b x / 3)`.
-/

public section

namespace ElboimSly

open MeasureTheory

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}

/-- Freedman's inequality, maximal form, Step 4 (choice of `λ`). -/
lemma freedman_choice {b x V : ℝ} (hb : 0 < b) (hx : 0 < x) (hV : 0 < V) :
    0 < x / (V + b * x / 3) ∧ x / (V + b * x / 3) * b < 3 ∧
      x ^ 2 / (2 * (V + b * x / 3)) ≤
        x / (V + b * x / 3) * x - concPhi (x / (V + b * x / 3) * b) / b ^ 2 * V := by
  set D : ℝ := V + b * x / 3 with hD
  have hDpos : 0 < D := by positivity
  set l : ℝ := x / D with hl
  have hlpos : 0 < l := by positivity
  have hlb : l * b < 3 := by
    rw [hl, div_mul_eq_mul_div, div_lt_iff₀ hDpos]
    nlinarith
  refine ⟨hlpos, hlb, ?_⟩
  have h1 := concPhi_le_of_lt_three (w := l * b) (by positivity) hlb
  have h3 : 1 - l * b / 3 = V / D := by
    rw [hl]; field_simp; rw [hD]; ring
  have h2 : (l * b) ^ 2 / (2 * (1 - l * b / 3)) / b ^ 2 * V = x ^ 2 / (2 * D) := by
    rw [h3, hl]; field_simp
  have h4 : concPhi (l * b) / b ^ 2 * V ≤ x ^ 2 / (2 * D) := by
    rw [← h2]
    exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right h1 (by positivity)) hV.le
  have h5 : l * x = x ^ 2 / D := by rw [hl]; field_simp
  have h6 : x ^ 2 / D = 2 * (x ^ 2 / (2 * D)) := by field_simp
  linarith

section Core

variable {ℱ : Filtration ℕ m0} {M v : ℕ → Ω → ℝ} {b : ℝ} {k : ℕ}

/-- The bad event `E_+`. -/
def concFreedmanEvent (M v : ℕ → Ω → ℝ) (k : ℕ) (x V : ℝ) : Set Ω :=
  {ω | ∃ j ≤ k, x ≤ M j ω ∧ ∑ i ∈ Finset.range j, v (i + 1) ω ≤ V}

/-- Freedman's inequality, maximal form, Steps 2-4 for `b > 0`, `x > 0`. -/
lemma ConcFreedmanSetting.event_le_pos [IsProbabilityMeasure μ]
    (S : ConcFreedmanSetting μ ℱ M v b k) (hb : 0 < b) {x V : ℝ} (hx : 0 < x) (hV : 0 < V) :
    μ.real (concFreedmanEvent M v k x V) ≤ Real.exp (-(x ^ 2 / (2 * (V + b * x / 3)))) := by
  obtain ⟨hlpos, hlb, hchoice⟩ := freedman_choice hb hx hV
  set l : ℝ := x / (V + b * x / 3) with hl
  set ψ : ℝ := concPhi (l * b) / b ^ 2 with hψ
  have hψpos : 0 ≤ ψ := by
    have := sq_div_two_le_concPhi (w := l * b) (by positivity)
    have : 0 < concPhi (l * b) := lt_of_lt_of_le (by positivity) this
    positivity
  obtain ⟨hYint, hYle⟩ := S.integral_Y_le (x := x) hb hlpos k le_rfl
  have hsub : concFreedmanEvent M v k x V ⊆
      {ω | Real.exp (l * x - ψ * V) ≤ concY M v l ψ x k ω} := by
    intro ω ⟨j, hjk, hxj, hQ⟩
    have hj1 : 1 ≤ j := by
      rcases Nat.eq_zero_or_pos j with h | h
      · subst h; simp [S.zero] at hxj; linarith
      · exact h
    exact concY_ge_of_exceed S.zero hψpos V S.v_nonneg hlpos.le k le_rfl ω
      ⟨j, hj1, hjk, hxj, hQ⟩
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall (concY_nonneg S.zero k)) hYint (Real.exp (l * x - ψ * V))
  have h1 : Real.exp (l * x - ψ * V) * μ.real (concFreedmanEvent M v k x V) ≤ 1 :=
    (mul_le_mul_of_nonneg_left (measureReal_mono hsub) (Real.exp_pos _).le).trans
      (hmarkov.trans hYle)
  have h2 : μ.real (concFreedmanEvent M v k x V) ≤ Real.exp (-(l * x - ψ * V)) := by
    rw [Real.exp_neg, ← one_div, le_div_iff₀ (Real.exp_pos _)]
    linarith [mul_comm (Real.exp (l * x - ψ * V)) (μ.real (concFreedmanEvent M v k x V))]
  refine h2.trans (Real.exp_le_exp.2 ?_)
  linarith

/-- The case `b = 0`, `x > 0`: all increments vanish a.s., so the event is null. -/
lemma ConcFreedmanSetting.event_le_zero (S : ConcFreedmanSetting μ ℱ M v b k) (hb : b = 0)
    [IsProbabilityMeasure μ] {x V : ℝ} (hx : 0 < x) : μ.real (concFreedmanEvent M v k x V) = 0 := by
  have hall : ∀ᵐ ω ∂μ, ∀ j ∈ Finset.range (k + 1), |M j ω| ≤ j * b :=
    (Filter.eventually_all_finset _).2 fun j hj => S.abs_M_le j (by simpa [Nat.lt_succ_iff] using hj)
  have hsub : concFreedmanEvent M v k x V ⊆ {ω | ¬ ∀ j ∈ Finset.range (k + 1), |M j ω| ≤ j * b} := by
    intro ω ⟨j, hjk, hxj, _⟩ hcon
    have := hcon j (by simp; omega)
    rw [hb] at this
    simp at this
    linarith [le_abs_self (M j ω)]
  refine le_antisymm ?_ measureReal_nonneg
  calc μ.real (concFreedmanEvent M v k x V)
      ≤ μ.real {ω | ¬ ∀ j ∈ Finset.range (k + 1), |M j ω| ≤ j * b} := measureReal_mono hsub
    _ = 0 := by rw [measureReal_def, ae_iff.1 hall]; simp

/-- Freedman's inequality, maximal form (a). -/
theorem ConcFreedmanSetting.event_le [IsProbabilityMeasure μ]
    (S : ConcFreedmanSetting μ ℱ M v b k) (hb : 0 ≤ b) {x V : ℝ} (hx : 0 ≤ x) (hV : 0 < V) :
    μ.real (concFreedmanEvent M v k x V) ≤ Real.exp (-(x ^ 2 / (2 * (V + b * x / 3)))) := by
  rcases hx.eq_or_lt with rfl | hxpos
  · simp
  rcases hb.eq_or_lt with hb0 | hbpos
  · rw [S.event_le_zero hb0.symm hxpos]; positivity
  · exact S.event_le_pos hbpos hxpos hV

end Core

/-- **Freedman's inequality, maximal form (a).** Freedman's inequality, maximal form (a).
Here `M` is a martingale with `M 0 = 0` and increments bounded by `b`, and `v (j+1)` is an
`ℱ j`-measurable nonnegative bound on the conditional variance of the `(j+1)`-st increment. -/
theorem concFreedman_exists_ge [IsProbabilityMeasure μ] {ℱ : Filtration ℕ m0}
    {M v : ℕ → Ω → ℝ} {b : ℝ} {k : ℕ}
    (hM0 : M 0 = 0) (hM : Martingale M ℱ μ) (hb : 0 ≤ b)
    (hbd : ∀ j < k, ∀ᵐ ω ∂μ, |M (j + 1) ω - M j ω| ≤ b)
    (hv : ∀ j < k, StronglyMeasurable[ℱ j] (v (j + 1))) (hv0 : ∀ j < k, 0 ≤ v (j + 1))
    (hvar : ∀ j < k, μ[(M (j + 1) - M j) ^ 2 | ℱ j] ≤ᵐ[μ] v (j + 1))
    {x V : ℝ} (hx : 0 ≤ x) (hV : 0 < V) :
    μ.real {ω | ∃ j ≤ k, x ≤ M j ω ∧ ∑ i ∈ Finset.range j, v (i + 1) ω ≤ V} ≤
      Real.exp (-(x ^ 2 / (2 * (V + b * x / 3)))) :=
  (ConcFreedmanSetting.mk hM0 hM hbd hv (fun j hj ω => hv0 j hj ω) hvar).event_le hb hx hV

/-- **Freedman's inequality, maximal form (b).** Freedman's inequality, maximal form (b). -/
theorem concFreedman_exists_abs_ge [IsProbabilityMeasure μ] {ℱ : Filtration ℕ m0}
    {M v : ℕ → Ω → ℝ} {b : ℝ} {k : ℕ}
    (hM0 : M 0 = 0) (hM : Martingale M ℱ μ) (hb : 0 ≤ b)
    (hbd : ∀ j < k, ∀ᵐ ω ∂μ, |M (j + 1) ω - M j ω| ≤ b)
    (hv : ∀ j < k, StronglyMeasurable[ℱ j] (v (j + 1))) (hv0 : ∀ j < k, 0 ≤ v (j + 1))
    (hvar : ∀ j < k, μ[(M (j + 1) - M j) ^ 2 | ℱ j] ≤ᵐ[μ] v (j + 1))
    {x V : ℝ} (hx : 0 ≤ x) (hV : 0 < V) :
    μ.real {ω | ∃ j ≤ k, x ≤ |M j ω| ∧ ∑ i ∈ Finset.range j, v (i + 1) ω ≤ V} ≤
      2 * Real.exp (-(x ^ 2 / (2 * (V + b * x / 3)))) := by
  have hplus := concFreedman_exists_ge hM0 hM hb hbd hv hv0 hvar hx hV
  have hneg := concFreedman_exists_ge (M := -M) (v := v) (by simp [hM0]) hM.neg hb
    (fun j hj => (hbd j hj).mono fun ω h => by
      simp only [Pi.neg_apply]
      rw [show -M (j + 1) ω - -M j ω = -(M (j + 1) ω - M j ω) by ring, abs_neg]
      exact h) hv hv0
    (fun j hj => by
      have : ((-M) (j + 1) - (-M) j) ^ 2 = (M (j + 1) - M j) ^ 2 := by
        funext ω; simp; ring
      rw [this]; exact hvar j hj) hx hV
  have hsub : {ω | ∃ j ≤ k, x ≤ |M j ω| ∧ ∑ i ∈ Finset.range j, v (i + 1) ω ≤ V} ⊆
      {ω | ∃ j ≤ k, x ≤ M j ω ∧ ∑ i ∈ Finset.range j, v (i + 1) ω ≤ V} ∪
      {ω | ∃ j ≤ k, x ≤ (-M) j ω ∧ ∑ i ∈ Finset.range j, v (i + 1) ω ≤ V} := by
    intro ω ⟨j, hjk, hxj, hQ⟩
    rcases le_abs'.1 hxj with h | h
    · right; exact ⟨j, hjk, by simpa using (by linarith : x ≤ -M j ω), hQ⟩
    · left; exact ⟨j, hjk, h, hQ⟩
  calc _ ≤ _ := measureReal_mono hsub
    _ ≤ _ := measureReal_union_le _ _
    _ ≤ _ := by linarith

/-- **Freedman's inequality, maximal form (c).** Freedman's inequality, maximal form (c). -/
theorem concFreedman_max_abs_ge [IsProbabilityMeasure μ] {ℱ : Filtration ℕ m0}
    {M v : ℕ → Ω → ℝ} {b : ℝ} {k : ℕ}
    (hM0 : M 0 = 0) (hM : Martingale M ℱ μ) (hb : 0 ≤ b)
    (hbd : ∀ j < k, ∀ᵐ ω ∂μ, |M (j + 1) ω - M j ω| ≤ b)
    (hv : ∀ j < k, StronglyMeasurable[ℱ j] (v (j + 1))) (hv0 : ∀ j < k, 0 ≤ v (j + 1))
    (hvar : ∀ j < k, μ[(M (j + 1) - M j) ^ 2 | ℱ j] ≤ᵐ[μ] v (j + 1))
    {x V : ℝ} (hx : 0 ≤ x) (hV : 0 < V)
    (hQ : ∀ᵐ ω ∂μ, ∑ i ∈ Finset.range k, v (i + 1) ω ≤ V) :
    μ.real {ω | x ≤ (Finset.range (k + 1)).sup' ⟨0, by simp⟩
        (fun j => |M j ω|)} ≤ 2 * Real.exp (-(x ^ 2 / (2 * (V + b * x / 3)))) := by
  have hb' := concFreedman_exists_abs_ge hM0 hM hb hbd hv hv0 hvar hx hV
  have hsub : {ω | x ≤ (Finset.range (k + 1)).sup' ⟨0, by simp⟩
        (fun j => |M j ω|)} ⊆
      {ω | ∃ j ≤ k, x ≤ |M j ω| ∧ ∑ i ∈ Finset.range j, v (i + 1) ω ≤ V} ∪
      {ω | ¬ ∑ i ∈ Finset.range k, v (i + 1) ω ≤ V} := by
    intro ω hω
    by_cases hQω : ∑ i ∈ Finset.range k, v (i + 1) ω ≤ V
    · left
      obtain ⟨j, hj, hxj⟩ := (Finset.le_sup'_iff (f := fun j => |M j ω|) _).1 (show x ≤ _ from hω)
      refine ⟨j, by simpa [Nat.lt_succ_iff] using hj, hxj, le_trans ?_ hQω⟩
      refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono
        (by simpa [Nat.lt_succ_iff] using hj)) ?_
      intro i hi _
      have : i < k := by
        have := Finset.mem_range.1 hi
        have hjk : j ≤ k := by simpa [Nat.lt_succ_iff] using hj
        omega
      exact hv0 i this ω
    · right; exact hQω
  calc _ ≤ _ := measureReal_mono hsub
    _ ≤ _ := measureReal_union_le _ _
    _ ≤ 2 * Real.exp (-(x ^ 2 / (2 * (V + b * x / 3)))) + 0 := by
        refine add_le_add hb' (le_of_eq ?_)
        rw [measureReal_def, ae_iff.1 hQ]; simp
    _ = _ := add_zero _

end ElboimSly
