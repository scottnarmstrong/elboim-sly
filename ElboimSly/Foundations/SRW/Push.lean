/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.SRW.WindowExit
public import ElboimSly.Foundations.SRW.Law1dFormula
public import Mathlib

/-!
# One push

One push.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Real

namespace ElboimSly
namespace SRW

theorem exp_ten_ge : (20000 : ℝ) ≤ Real.exp 10 := by
  have h := Real.exp_one_gt_d9
  have : Real.exp 10 = Real.exp 1 ^ 10 := by
    rw [← Real.exp_nat_mul]; norm_num
  rw [this]
  calc (20000 : ℝ) ≤ (2.7182818283 : ℝ) ^ 10 := by norm_num
    _ ≤ Real.exp 1 ^ 10 := by gcongr

theorem exp_four_le : Real.exp 4 ≤ 55 := by
  have h := Real.exp_one_lt_d9
  have : Real.exp 4 = Real.exp 1 ^ 4 := by
    rw [← Real.exp_nat_mul]; norm_num
  rw [this]
  calc Real.exp 1 ^ 4 ≤ (2.7182818286 : ℝ) ^ 4 := by gcongr
    _ ≤ 55 := by norm_num

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {Y : Ω → PathSpace 1}

/-- One push: one push. -/
theorem IsSRW.push (hY : IsSRW P Y) {ρ : ℝ≥0} (hρ : 16 ≤ (ρ : ℝ)) :
    1 / 1100 ≤ P.real {ω | √(ρ : ℝ) / 2 ≤ (Y ω ρ 0 : ℝ) ∧
      ∀ s : ℝ≥0, s ≤ ρ → |(Y ω s 0 : ℝ)| < 9 * √(ρ : ℝ)} := by
  have := hY.isProbabilityMeasure
  have hρ0 : (0 : ℝ) < ρ := by linarith
  have hs4 : 4 ≤ √(ρ : ℝ) := Real.le_sqrt_of_sq_le (by nlinarith)
  have hsq : √(ρ : ℝ) ^ 2 = ρ := Real.sq_sqrt hρ0.le
  have hs0 : 0 < √(ρ : ℝ) := by linarith
  set x := √(ρ : ℝ) with hx
  set T : Set Ω := {ω | x / 2 ≤ (Y ω ρ 0 : ℝ) ∧ ∀ s : ℝ≥0, s ≤ ρ → |(Y ω s 0 : ℝ)| < 9 * x} with hT
  set B : Set Ω := {ω | ∃ s : ℝ≥0, s ≤ ρ ∧ 9 * x ≤ |(Y ω s 0 : ℝ)|} with hB
  set I : Finset ℤ := Finset.Icc ⌈x / 2⌉ ⌊x⌋ with hI
  set A : Set Ω := ⋃ k ∈ I, {ω | Y ω ρ 0 = k} with hA
  have hAsub : A ⊆ T ∪ B := by
    intro ω hω
    simp only [hA, mem_iUnion, mem_ofPred_eq, hI, Finset.mem_Icc] at hω
    obtain ⟨k, ⟨hk1, hk2⟩, hk⟩ := hω
    by_cases hb : ω ∈ B
    · exact Or.inr hb
    · refine Or.inl ⟨?_, fun s hs => ?_⟩
      · rw [hk]; exact (Int.le_ceil _).trans (by exact_mod_cast hk1)
      · by_contra hcon
        exact hb ⟨s, hs, not_lt.1 hcon⟩
  have hAB : P.real A ≤ P.real T + P.real B :=
    (measureReal_mono hAsub).trans (measureReal_union_le _ _)
  -- lower bound for A
  have hcard : x / 4 ≤ (I.card : ℝ) := by
    have hf := Int.lt_floor_add_one x
    have hc := Int.ceil_lt_add_one (x / 2)
    have hpos : (0 : ℤ) ≤ ⌊x⌋ + 1 - ⌈x / 2⌉ := by
      have : (0 : ℝ) < (⌊x⌋ : ℝ) + 1 - ⌈x / 2⌉ := by linarith
      exact_mod_cast this.le
    have hcd : (I.card : ℝ) = ((⌊x⌋ + 1 - ⌈x / 2⌉ : ℤ) : ℝ) := by
      rw [hI, Int.card_Icc]
      have := Int.toNat_of_nonneg hpos
      exact_mod_cast this
    rw [hcd]
    push_cast
    linarith
  have hAlow : (I.card : ℝ) * (Real.exp (-4) / (4 * x)) ≤ P.real A := by
    have hdisj : PairwiseDisjoint (↑I) fun k : ℤ => {ω | Y ω ρ 0 = k} := by
      intro k _ k' _ hkk'
      refine Set.disjoint_left.2 fun ω h1 h2 => hkk' ?_
      exact h1.symm.trans h2
    rw [hA, measureReal_biUnion_finset hdisj (fun k _ =>
      hY.measurable_eval1 ρ (measurableSet_singleton k))]
    rw [← nsmul_eq_mul]
    refine Finset.card_nsmul_le_sum _ _ _ fun k hk => ?_
    simp only [hI, Finset.mem_Icc] at hk
    have hkx : |(k : ℝ)| ≤ x := by
      rw [abs_le]
      constructor
      · have : (0 : ℝ) ≤ (⌈x / 2⌉ : ℤ) := by
          exact_mod_cast Int.ceil_nonneg (by positivity)
        have h1 : ((⌈x / 2⌉ : ℤ) : ℝ) ≤ k := by exact_mod_cast hk.1
        linarith
      · exact (by exact_mod_cast hk.2 : (k : ℝ) ≤ ⌊x⌋).trans (Int.floor_le x)
    exact hY.local_lower (t := ρ) (by linarith) hkx
  have hexp4 : 1 / 55 ≤ Real.exp (-4) := by
    rw [Real.exp_neg, inv_eq_one_div]
    exact one_div_le_one_div_of_le (Real.exp_pos 4) exp_four_le
  have hBb : P.real B ≤ 4 * Real.exp (-10) := by
    have h2 := hY.levy_abs ρ (9 * x)
    have h3 := hY.chernoff_abs (T := ρ) (by exact_mod_cast hρ0) (a := 9 * x) (by positivity)
    have hmin : (10 : ℝ) ≤ min ((9 * x) ^ 2 / (8 * (ρ : ℝ))) (9 * x / 2) := by
      refine le_min ?_ ?_
      · rw [mul_pow, hsq, le_div_iff₀ (by positivity)]; nlinarith
      · linarith
    have h4 : Real.exp (-min ((9 * x) ^ 2 / (8 * (ρ : ℝ))) (9 * x / 2)) ≤ Real.exp (-10) :=
      Real.exp_le_exp.2 (by linarith)
    have h5 : P.real B ≤ 2 * P.real {ω | 9 * x ≤ |(Y ω ρ 0 : ℝ)|} := h2
    linarith
  have hexp10 : Real.exp (-10) ≤ 1 / 20000 := by
    rw [Real.exp_neg, inv_eq_one_div]
    exact one_div_le_one_div_of_le (by norm_num) exp_ten_ge
  have hE0 := Real.exp_pos (-4)
  have hlow2 : x / 4 * (Real.exp (-4) / (4 * x)) ≤ (I.card : ℝ) * (Real.exp (-4) / (4 * x)) := by
    gcongr
  have e : x / 4 * (Real.exp (-4) / (4 * x)) = Real.exp (-4) / 16 := by field_simp; ring
  linarith

end SRW
end ElboimSly
