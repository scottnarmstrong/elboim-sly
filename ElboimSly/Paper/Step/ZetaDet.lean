/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Step.Concatenation
public import Mathlib

/-!
# The deterministic decomposition of Lemma 7.1

ES22 Lemma 7.1, Steps 3, 5 and 6 (pathwise).

Let `W`, `V₂` be paths with `V₂ 0 = 0` and `W̃ = W|_{[0,s₀]} ⌢ V₂`. Let
`s₀ = zp 0 ≤ zn 0 ≤ zp 1 ≤ zn 1 ≤ ⋯ ≤ zn K`, with `T ≤ zn K ≤ T`, gaps `zn i - zp i ≤ h`,
agreement of the increments of `W` and `W̃` on `[zn i, zp (i+1)]` for `i < K`, and the fast
displacement bounds `‖W u' - W u‖, ‖V₂ u' - V₂ u‖ ≤ L (u' - u + 1)` on `[0, T]`. Then
`‖W s - W̃ s‖ ≤ 2 (K + 1) L (h + 1)` for `s ≤ T`.
-/

@[expose] public section

open scoped NNReal

namespace ElboimSly.Paper.Step

open ElboimSly.Paper

variable {d : ℕ}

theorem stepCat_ge_eq {W V₂ : ℝ≥0 → Fin d → ℤ} (hV0 : V₂ 0 = 0) {s₀ u : ℝ≥0} (h : s₀ ≤ u) :
    stepCat s₀ W V₂ u = W s₀ + V₂ (u - s₀) := by
  rcases h.eq_or_lt with rfl | hlt
  · rw [stepCat_of_le _ _ le_rfl, tsub_self, hV0, add_zero]
  · exact stepCat_of_gt _ _ hlt

theorem min_sub_min_le (s a b : ℝ) (hba : b ≤ a) (_h0 : 0 ≤ a - b) :
    min s a - min s b ≤ a - b := by
  rcases le_total s b with h1 | h1
  · rw [min_eq_left h1, min_eq_left (h1.trans hba)]; linarith
  · rcases le_total s a with h2 | h2
    · rw [min_eq_left h2, min_eq_right h1]; linarith
    · rw [min_eq_right h2, min_eq_right h1]

theorem det_decomp {W V₂ : ℝ≥0 → Fin d → ℤ} (hV0 : V₂ 0 = 0) {s₀ T : ℝ≥0} {h L : ℝ} (K : ℕ)
    (zn zp : ℕ → ℝ≥0) (h0 : zp 0 = s₀) (hmono1 : ∀ i ≤ K, zp i ≤ zn i)
    (hmono2 : ∀ i < K, zn i ≤ zp (i + 1)) (hend : T ≤ zn K) (hzT : ∀ i ≤ K, zn i ≤ T)
    (hgap : ∀ i ≤ K, (zn i : ℝ) - zp i ≤ h)
    (hcpl : ∀ i < K, ∀ r : ℝ≥0, zn i + r ≤ zp (i + 1) →
      W (zn i + r) - W (zn i) =
        stepCat s₀ W V₂ (zn i + r) - stepCat s₀ W V₂ (zn i))
    (hfW : ∀ u u' : ℝ≥0, u ≤ u' → u' ≤ T → ‖W u' - W u‖ ≤ L * ((u' : ℝ) - u + 1))
    (hfV : ∀ u u' : ℝ≥0, u ≤ u' → u' ≤ T → ‖V₂ u' - V₂ u‖ ≤ L * ((u' : ℝ) - u + 1))
    (hL : 0 ≤ L) (hh : 0 ≤ h) :
    ∀ s : ℝ≥0, s ≤ T → ‖W s - stepCat s₀ W V₂ s‖ ≤ 2 * ((K : ℝ) + 1) * (L * (h + 1)) := by
  intro s hsT
  have hB : 0 ≤ L * (h + 1) := mul_nonneg hL (by linarith)
  by_cases hss : s ≤ s₀
  · rw [stepCat_of_le _ _ hss, sub_self, norm_zero]
    have : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg K
    positivity
  rw [not_le] at hss
  set D : ℝ≥0 → Fin d → ℤ := fun u => W u - stepCat s₀ W V₂ u with hD
  have hs0 : ∀ i ≤ K, s₀ ≤ zp i := by
    intro i
    induction i with
    | zero => intro _; rw [h0]
    | succ i ih =>
      intro hi
      exact (ih (by omega)).trans ((hmono1 i (by omega)).trans (hmono2 i (by omega)))
  have hpiece : ∀ i ≤ K, ‖D (min s (zn i)) - D (min s (zp i))‖ ≤ 2 * (L * (h + 1)) := by
    intro i hi
    have hle : min s (zp i) ≤ min s (zn i) := min_le_min le_rfl (hmono1 i hi)
    have hdiff : ((min s (zn i) : ℝ≥0) : ℝ) - (min s (zp i) : ℝ≥0) ≤ h := by
      have h1 := min_sub_min_le (s : ℝ) (zn i) (zp i) (by exact_mod_cast hmono1 i hi)
        (by have := hmono1 i hi; have : (zp i : ℝ) ≤ zn i := by exact_mod_cast this
            linarith)
      have e1 : ((min s (zn i) : ℝ≥0) : ℝ) = min (s : ℝ) (zn i) := NNReal.coe_min _ _
      have e2 : ((min s (zp i) : ℝ≥0) : ℝ) = min (s : ℝ) (zp i) := NNReal.coe_min _ _
      rw [e1, e2]
      linarith [hgap i hi]
    have hu'T : min s (zn i) ≤ T := (min_le_right _ _).trans (hzT i hi)
    have hW := hfW _ _ hle hu'T
    have hs0m : s₀ ≤ min s (zp i) := le_min hss.le (hs0 i hi)
    have hs0n : s₀ ≤ min s (zn i) := hs0m.trans hle
    have hcat : stepCat s₀ W V₂ (min s (zn i)) - stepCat s₀ W V₂ (min s (zp i)) =
        V₂ (min s (zn i) - s₀) - V₂ (min s (zp i) - s₀) := by
      rw [stepCat_ge_eq hV0 hs0n, stepCat_ge_eq hV0 hs0m]
      abel
    have hV := hfV (min s (zp i) - s₀) (min s (zn i) - s₀) (tsub_le_tsub_right hle s₀)
      ((tsub_le_self).trans hu'T)
    have hsub1 : ((min s (zn i) - s₀ : ℝ≥0) : ℝ) = ((min s (zn i) : ℝ≥0) : ℝ) - s₀ :=
      NNReal.coe_sub hs0n
    have hsub2 : ((min s (zp i) - s₀ : ℝ≥0) : ℝ) = ((min s (zp i) : ℝ≥0) : ℝ) - s₀ :=
      NNReal.coe_sub hs0m
    rw [hsub1, hsub2] at hV
    have hD1 : D (min s (zn i)) - D (min s (zp i)) =
        (W (min s (zn i)) - W (min s (zp i))) -
          (stepCat s₀ W V₂ (min s (zn i)) - stepCat s₀ W V₂ (min s (zp i))) := by
      simp only [hD]; abel
    rw [hD1, hcat]
    refine (norm_sub_le _ _).trans ?_
    have hmul : L * (((min s (zn i) : ℝ≥0) : ℝ) - (min s (zp i) : ℝ≥0) + 1) ≤ L * (h + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) hL
    have hmul' : L * (((min s (zn i) : ℝ≥0) : ℝ) - s₀ - (((min s (zp i) : ℝ≥0) : ℝ) - s₀) + 1) ≤
        L * (h + 1) := by
      have : ((min s (zn i) : ℝ≥0) : ℝ) - s₀ - (((min s (zp i) : ℝ≥0) : ℝ) - s₀) =
          ((min s (zn i) : ℝ≥0) : ℝ) - (min s (zp i) : ℝ≥0) := by ring
      rw [this]; exact hmul
    linarith
  have hchain : ∀ i < K, D (min s (zp (i + 1))) = D (min s (zn i)) := by
    intro i hi
    have hz := hmono2 i hi
    by_cases hsz : s ≤ zn i
    · rw [min_eq_left hsz, min_eq_left (hsz.trans hz)]
    · rw [not_le] at hsz
      rw [min_eq_right hsz.le]
      set c := min s (zp (i + 1)) with hc
      have hzc : zn i ≤ c := le_min hsz.le hz
      have hcz : c ≤ zp (i + 1) := min_le_right _ _
      have hr := hcpl i hi (c - zn i) (by rw [add_tsub_cancel_of_le hzc]; exact hcz)
      rw [add_tsub_cancel_of_le hzc] at hr
      simp only [hD]
      have e : W c - stepCat s₀ W V₂ c - (W (zn i) - stepCat s₀ W V₂ (zn i)) =
          (W c - W (zn i)) - (stepCat s₀ W V₂ c - stepCat s₀ W V₂ (zn i)) := by abel
      exact sub_eq_zero.1 (e ▸ (by rw [hr, sub_self] : (W c - W (zn i)) -
        (stepCat s₀ W V₂ c - stepCat s₀ W V₂ (zn i)) = 0))
  -- induction along the excursions
  have key : ∀ i ≤ K, ‖D (min s (zn i))‖ ≤ 2 * ((i : ℝ) + 1) * (L * (h + 1)) := by
    intro i
    induction i with
    | zero =>
      intro hi
      have h0' : D (min s (zp 0)) = 0 := by
        rw [h0, min_eq_right hss.le]
        simp only [hD, stepCat_of_le _ _ le_rfl, sub_self]
      have := hpiece 0 hi
      rw [h0', sub_zero] at this
      simpa using this
    | succ i ih =>
      intro hi
      have h1 := ih (by omega)
      have h2 := hpiece (i + 1) hi
      have h3 : ‖D (min s (zn (i + 1)))‖ ≤ ‖D (min s (zp (i + 1)))‖ +
          ‖D (min s (zn (i + 1))) - D (min s (zp (i + 1)))‖ := by
        have := norm_add_le (D (min s (zp (i + 1)))) (D (min s (zn (i + 1))) - D (min s (zp (i + 1))))
        simpa using this
      have h4 : ‖D (min s (zp (i + 1)))‖ = ‖D (min s (zn i))‖ := by rw [hchain i (by omega)]
      push_cast
      nlinarith [h1, h2, h3, h4]
  have hfinal : min s (zn K) = s := min_eq_left (hsT.trans hend)
  have := key K le_rfl
  rw [hfinal] at this
  exact this

end ElboimSly.Paper.Step
