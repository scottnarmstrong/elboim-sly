/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Base.H1Main
public import ElboimSly.Paper.Base.BaseH234
public import ElboimSly.Paper.Base.Lemma82
public import ElboimSly.Paper.Base.Es8Constants
public import ElboimSly.Frozen.Defs.IndHyp
public import Mathlib

/-!
# The induction base

Induction base.
-/

@[expose] public section

open MeasureTheory

namespace ElboimSly.Paper

theorem exp_neg_cube_le_indFailBound (β t₀ : ℝ) (n : ℕ) :
    Real.exp (-(n : ℝ) ^ 3) ≤ indFailBound β t₀ n := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  unfold indFailBound
  split_ifs
  · exact le_rfl
  · refine Real.exp_le_exp.2 ?_
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · simp [h0]
    · have h1 : (1 : ℝ) ≤ n := by exact_mod_cast hpos
      nlinarith [pow_pos (show (0 : ℝ) < n by linarith) 2]

/-- Induction base. -/
theorem es8_base (d : ℕ) (hd : 5 ≤ d) :
    ∃ (n₀ : ℕ) (β₀ : ℝ), 20 ≤ n₀ ∧ es8n0 d ≤ n₀ ∧ es8Beta0 d ≤ β₀ ∧
      ∀ (β : ℝ) [Fact (0 < β)], β₀ ≤ β → ∀ n : ℕ, n₀ ≤ n → ∀ t₀ : ℝ, 1 < t₀ → t₀ ≤ 4 →
        indScale t₀ n ≤ β → IndHyp d β n t₀ := by
  obtain ⟨n₁, hn₁⟩ := base_H4 d (by omega)
  refine ⟨max (es8n0 d) n₁, es8Beta0 d, ?_, le_max_left _ _, le_rfl, ?_⟩
  · exact (le_es8n0 d le_rfl).1.trans (le_max_left _ _)
  intro β _ hβ n hn t₀ ht1 ht4 htβ
  have hn0 : es8n0 d ≤ n := (le_max_left _ _).trans hn
  have hn1 : n₁ ≤ n := (le_max_right _ _).trans hn
  obtain ⟨h20, h2d, h77, h1, hC, h2, h39, hK⟩ := le_es8n0 d hn0
  have : NeZero d := ⟨by omega⟩
  have hlog : Real.log (4 * d) ≤ n := by
    have hd0 : (0 : ℝ) < 4 * d := by positivity
    have hd1 : (0 : ℝ) < d := by positivity
    rw [Real.log_mul (by norm_num) hd1.ne']
    have a := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 by norm_num)
    have b := Real.log_le_sub_one_of_pos hd1
    have : (2 * d : ℝ) ≤ n := by exact_mod_cast h2d
    have : (5 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hle := exp_neg_cube_le_indFailBound β t₀ n
  refine ⟨fun Ω _ P N hN => ?_, fun Ω _ P N hN => ?_⟩
  · refine ⟨?_, base_IndH2 P N hN n htβ, base_IndH3 P N hN (by omega) hlog ht1 htβ,
      hn₁ n hn1 h77 β t₀ ht1 ht4 htβ P N hN⟩
    refine le_trans (ENNReal.ofReal_le_ofReal
      (show 1 - indFailBound β t₀ n ≤ 1 - Real.exp (-(n : ℝ) ^ 3) by linarith)) ?_
    exact es8_lemma_8_1 hd hβ h20 h2d h1 ht1 ht4 htβ hN
  · intro u₁ u₂ q₁ q₂ _ _
    refine (es8_lemma82 hN hd (by omega) hC h2 h39 hK ht1 ht4 htβ u₁ u₂ q₁ q₂).trans
      (ENNReal.ofReal_le_ofReal hle)

/-- Induction base. -/
theorem ind_base (d : ℕ) (hd : 5 ≤ d) :
    ∃ (n₀ : ℕ) (β₀ : ℝ), 10 ≤ n₀ ∧
      ∀ (β : ℝ) [Fact (0 < β)], β₀ ≤ β → ∀ n : ℕ, n₀ ≤ n → ∀ t₀ : ℝ, 1 < t₀ → t₀ ≤ 4 →
        indScale t₀ n ≤ β → IndHyp d β n t₀ := by
  obtain ⟨n₀, β₀, h20, -, -, h⟩ := es8_base d hd
  exact ⟨n₀, β₀, by omega, h⟩

end ElboimSly.Paper

end
