/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Heavy.Es6Four

/-!
# Lemma 6.4

ES22 Lemma 6.4 (§6).

`es6_four`: for `n` satisfying the thresholds, a cyclic path `w` and `0 ≤ t < τ_jump(w) ∧ τ'(w)`,
no block `B(x, r)` with `r ≥ t_n^δ` is heavy for `w` on `[0, t]`.
-/

@[expose] public section

open Set
open scoped ENNReal

namespace ElboimSly.Paper

open ElboimSly

variable {d n₀ n : ℕ} {E : HeavyEscConsts} {t₀ : ℝ} {w : ℝ → Fin d → ℤ}

/-- ES22 Lemma 6.4. -/
theorem es6_four (hd : 5 ≤ d) (ht1 : 1 < t₀) (ht4 : t₀ ≤ 4) (hT : HeavyT d n₀ E n)
    (hw : IsCyclicPath w) {t : ℝ} (ht0 : 0 ≤ t) (hj : ENNReal.ofReal t < pathTjumpCube w n)
    (hτ : ENNReal.ofReal t < heavyTauPrime d t₀ n w) (x : Fin d → ℤ) {r : ℝ}
    (hr : indScale t₀ n ^ indDelta d ≤ r) : ¬ IsHeavy w 0 t x r := by
  classical
  rintro ⟨hr0, hge⟩
  have hn4 : 4 ≤ n := hT.t4
  have hδ := heavy_indDelta_pos (d := d) (by omega)
  have htn : (4 : ℝ) ^ n ≤ indScale t₀ n := (indScale_gt_four_pow ht1 n).le
  have htn1 : (1 : ℝ) ≤ indScale t₀ n := le_trans (one_le_pow₀ (by norm_num)) htn
  have hr1 : 1 ≤ r := le_trans (Real.one_le_rpow htn1 hδ.le) hr
  set m : ℕ := ⌈Real.logb 2 (2 * r + 1)⌉₊ with hm
  have hlog0 : 0 ≤ Real.logb 2 (2 * r + 1) := Real.logb_nonneg (by norm_num) (by linarith)
  have hm1 : 2 * r + 1 ≤ (2 : ℝ) ^ m := by
    have h := Nat.le_ceil (Real.logb 2 (2 * r + 1))
    rw [Real.logb_le_iff_le_rpow (by norm_num) (by linarith)] at h
    rwa [Real.rpow_natCast] at h
  have hm2 : (2 : ℝ) ^ m < 2 * (2 * r + 1) := by
    have h := Nat.ceil_lt_add_one hlog0
    have h2 : (2 : ℝ) ^ (m : ℝ) < (2 : ℝ) ^ (Real.logb 2 (2 * r + 1) + 1) :=
      Real.rpow_lt_rpow_of_exponent_lt (by norm_num) h
    rw [Real.rpow_add (by norm_num), Real.rpow_logb (by norm_num) (by norm_num) (by linarith),
      Real.rpow_natCast] at h2
    simpa [mul_comm] using h2
  have hm0 : heavyM0 d t₀ n ≤ m := by
    have h1 : (heavyM0 d t₀ n : ℝ) ≤ indDelta d * Real.logb 2 (indScale t₀ n) :=
      Nat.floor_le (mul_nonneg hδ.le (Real.logb_nonneg (by norm_num) htn1))
    have h2 : indDelta d * Real.logb 2 (indScale t₀ n) = Real.logb 2 (indScale t₀ n ^ indDelta d) :=
      (Real.logb_rpow_eq_mul_logb_of_pos (by linarith)).symm
    have h3 : Real.logb 2 (indScale t₀ n ^ indDelta d) ≤ Real.logb 2 (2 * r + 1) :=
      Real.logb_le_logb_of_le (by norm_num) (Real.rpow_pos_of_pos (by linarith) _)
        (by linarith)
    have h4 : (m : ℝ) ≥ Real.logb 2 (2 * r + 1) := Nat.le_ceil _
    have : (heavyM0 d t₀ n : ℝ) ≤ m := by linarith
    exact_mod_cast this
  have hjm : heavyScaleJ n ≤ m := (scales_facts_b hd ht1 ht4 hT).1.trans hm0
  obtain ⟨T, hTc, hcover⟩ := ball_subset_blocks (d := d) m x hr0.le hm1
  set D := heavyD n m with hDdef
  have hD : 1 ≤ D := by
    rw [hDdef]; unfold heavyD; exact Nat.mul_pos (by positivity) (by positivity)
  have hn1 : 1 ≤ n := by omega
  have hjump : ENNReal.ofReal t < pathTjump w ((n : ℝ) ^ 3) := hj
  have hblock : ∀ ι : Fin d → ℤ, (heavyBlock m ι ∩ visitedSet w 0 t).Finite ∧
      (heavyBlock m ι ∩ visitedSet w 0 t).ncard ≤
        heavyTrials d n * (n ^ 3 * D) * (2 ^ heavyScaleJ n) ^ d := by
    intro ι
    have h2 : ENNReal.ofReal t < heavyEntSeq w (heavyScaleJ n) m (D : ℝ≥0∞) ι (heavyTrials d n) := by
      refine lt_of_lt_of_le hτ ?_
      unfold heavyTauPrime
      exact iInf₂_le_of_le m hm0 (iInf_le_of_le ι le_rfl)
    exact heavy_block_count hw hn1 hD hjm ι ht0 hjump h2
  have hsub : {v : Fin d → ℤ | ‖v - x‖ ≤ r} ∩ visitedSet w 0 t ⊆
      ⋃ ι ∈ T, (heavyBlock m ι ∩ visitedSet w 0 t) := by
    rintro v ⟨hv, hV⟩
    obtain ⟨ι, hιT, hvι⟩ := mem_iUnion₂.1 (hcover hv)
    exact mem_iUnion₂.2 ⟨ι, hιT, hvι, hV⟩
  have hfin : (⋃ ι ∈ T, (heavyBlock m ι ∩ visitedSet w 0 t)).Finite :=
    T.finite_toSet.biUnion fun ι _ => (hblock ι).1
  have hcard : ({v : Fin d → ℤ | ‖v - x‖ ≤ r} ∩ visitedSet w 0 t).ncard ≤
      2 ^ d * (heavyTrials d n * (n ^ 3 * D) * (2 ^ heavyScaleJ n) ^ d) := by
    calc _ ≤ (⋃ ι ∈ T, (heavyBlock m ι ∩ visitedSet w 0 t)).ncard := Set.ncard_le_ncard hsub hfin
      _ ≤ ∑ ι ∈ T, (heavyBlock m ι ∩ visitedSet w 0 t).ncard := Finset.set_ncard_biUnion_le _ _
      _ ≤ ∑ _ι ∈ T, heavyTrials d n * (n ^ 3 * D) * (2 ^ heavyScaleJ n) ^ d :=
          Finset.sum_le_sum fun ι _ => (hblock ι).2
      _ = T.card * (heavyTrials d n * (n ^ 3 * D) * (2 ^ heavyScaleJ n) ^ d) := by simp
      _ ≤ _ := Nat.mul_le_mul_right _ hTc
  have hnum := es6_four_numeric hd ht1 hT hr hm1 hm2
  have : ((({v : Fin d → ℤ | ‖v - x‖ ≤ r} ∩ visitedSet w 0 t).ncard : ℕ) : ℝ) < r ^ (5 / 2 : ℝ) :=
    lt_of_le_of_lt (by exact_mod_cast hcard) hnum
  exact absurd hge (not_le.2 this)

end ElboimSly.Paper
