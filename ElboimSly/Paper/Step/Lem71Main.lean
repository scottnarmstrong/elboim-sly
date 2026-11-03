/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Step.Lem71
public import ElboimSly.Paper.Step.Lem71Sum
public import Mathlib

/-!
# Lemma 7.1, conditional on Theorem 6.1

ES22 Lemma 7.1, Step 6 and the choice of `c_cat`, `β_cat(n₁)`.

`stepLem71_of_es61`: if `StepEs61 d c₆ β₆` (the conclusion of ES22 Theorem 6.1), then `StepLem71 d c β_cat`
for `c = ½ min {c₆, c_f, 1/17}` and a threshold `β_cat`.
-/

@[expose] public section

open MeasureTheory Set ElboimSly.Cyclic ElboimSly.SRW
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Step

open ElboimSly.Paper

variable {d : ℕ}

theorem stepLem71_of_es61 (hd5 : 5 ≤ d) {c6 : ℝ} (hc6 : 0 < c6) {β6 : ℕ → ℝ}
    (H6 : StepEs61 d c6 β6) : ∃ c : ℝ, 0 < c ∧ ∃ βCat : ℕ → ℝ, StepLem71 d c βCat := by
  have hd1 : 1 ≤ d := by omega
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd1
  obtain ⟨Cf, cf, hCf, hcf, Hf⟩ := stepFast_prob hd1
  obtain ⟨Cc, hCc, Hc⟩ := zeta_count_prob hd5
  choose βc hβc using Hc
  obtain ⟨c, hcdef⟩ : ∃ c : ℝ, c = 1 / 2 * min c6 (min cf (1 / 17)) := ⟨_, rfl⟩
  have hcpos : 0 < c := by
    have : 0 < min c6 (min cf (1 / 17)) := lt_min hc6 (lt_min hcf (by norm_num))
    rw [hcdef]; positivity
  have hε : 0 < heavyEps d := by unfold heavyEps; positivity
  obtain ⟨N1, hN1⟩ := exists_poly_lt_rpow hε
  obtain ⟨N2, hN2⟩ := exists_const_mul_pow_le_exp hcpos (3 + 32 * Cf) (by linarith)
  refine ⟨c, hcpos, fun n₁ => max (max (β6 n₁) (βc n₁)) ((4 : ℝ) ^ (max (max N1 N2) 3 + 1)), ?_⟩
  intro n₁ hn₁ β _ n t₀ hβ hreg Ω _ P Y hY hYp a s h0 h1 hsT
  obtain ⟨N, hN⟩ : ∃ N : ℕ, N = max (max N1 N2) 3 := ⟨_, rfl⟩
  rw [← hN] at hβ
  have hβ6 : β6 n₁ ≤ β := (le_max_left _ _).trans ((le_max_left _ _).trans hβ)
  have hβc' : βc n₁ ≤ β := (le_max_right _ _).trans ((le_max_left _ _).trans hβ)
  have hβN : (4 : ℝ) ^ (N + 1) ≤ β := (le_max_right _ _).trans hβ
  have ht0 := hreg.2.2.2.1
  have hβt := hreg.2.2.2.2.1
  have hβ1 : 1 < β := hreg.2.1
  have hn1 : 1 ≤ n := hreg.2.2.1
  have hTle : indScale t₀ n ≤ (4 : ℝ) ^ (n + 1) := by
    unfold indScale; rw [pow_succ]
    nlinarith [ht0.2, pow_pos (by norm_num : (0 : ℝ) < 4) n]
  have hnN : N ≤ n := by
    by_contra hlt
    rw [not_le] at hlt
    have h4 : (4 : ℝ) ^ (n + 1) ≤ 4 ^ N := pow_le_pow_right₀ (by norm_num) (by omega)
    have h5 : (4 : ℝ) ^ N < 4 ^ (N + 1) := pow_lt_pow_right₀ (by norm_num) (by omega)
    linarith
  have hn3 : 3 ≤ n := by omega
  have hnN1 : N1 ≤ n := by omega
  have hnN2 : N2 ≤ n := by omega
  set T : ℝ := indScale t₀ n with hTdef
  have hT1 : 1 ≤ T := by linarith
  have hT0 : 0 ≤ T := by linarith
  obtain ⟨Tn, hTn⟩ : ∃ Tn : ℝ≥0, (Tn : ℝ) = T := ⟨T.toNNReal, Real.coe_toNNReal _ hT0⟩
  have hsum2 : stepPartial s 2 = s 0 + s 1 := by
    simp [stepPartial, Finset.sum_range_succ]
  rw [hsum2] at hsT
  have hs0Tn : s 0 ≤ Tn := by
    have : ((s 0 : ℝ≥0) : ℝ) ≤ Tn := by rw [hTn]; push_cast at hsT; linarith [(s 1).2]
    exact_mod_cast this
  have hsTn : s 0 + s 1 ≤ Tn := by
    have : (((s 0 + s 1 : ℝ≥0)) : ℝ) ≤ Tn := by rw [hTn]; exact hsT
    exact_mod_cast this
  -- the scale `h = t_n^ε`
  set hh : ℝ := T ^ heavyEps d with hhdef
  have hhpos : 0 < hh := Real.rpow_pos_of_pos (by linarith) _
  have hh1 : 1 ≤ hh := Real.one_le_rpow hT1 hε.le
  have hh8 : 8 * (n : ℝ) ^ 6 < hh := by
    have h4n : (4 : ℝ) ^ n ≤ T := by
      unfold indScale at hTdef; rw [hTdef]
      nlinarith [ht0.1, pow_pos (by norm_num : (0 : ℝ) < 4) n]
    have h1 : ((4 : ℝ) ^ n) ^ heavyEps d ≤ T ^ heavyEps d :=
      Real.rpow_le_rpow (by positivity) h4n hε.le
    have h2 : ((4 : ℝ) ^ n) ^ heavyEps d = ((4 : ℝ) ^ heavyEps d) ^ n := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), ← Real.rpow_natCast,
        ← Real.rpow_mul (by norm_num), mul_comm]
    have := hN1 n hnN1
    linarith
  have hK2 : T ^ (2 * heavyEps d) = hh ^ 2 := by
    rw [hhdef, show 2 * heavyEps d = heavyEps d * 2 by ring, Real.rpow_mul hT0, Real.rpow_two]
  have hn3r : (1 : ℝ) ≤ (n : ℝ) ^ 3 := one_le_pow₀ (by exact_mod_cast hn1)
  have hbound : 2 * (((n ^ 3 : ℕ) : ℝ) + 1) * ((n : ℝ) ^ 3 * (hh + 1)) < T ^ (2 * heavyEps d) := by
    rw [hK2]
    push_cast
    have h6 : ((n : ℝ) ^ 3) ^ 2 = (n : ℝ) ^ 6 := by ring
    nlinarith [mul_pos hhpos hhpos, mul_nonneg (sub_nonneg.2 hn3r) (sub_nonneg.2 hh1),
      mul_nonneg (sub_nonneg.2 hn3r) hhpos.le, mul_nonneg hhpos.le (sub_nonneg.2 hn3r)]
  rw [hsum2]
  have hL1 : (1 : ℝ) ≤ (n : ℝ) ^ 3 := hn3r
  -- the bad events
  set B1 : Set Ω := {ω | zetaN β (zw1 β a Y) (za1 β a Y) (zw2 β a (s 0) Y) (za2 β a (s 0) Y)
    (s 0) (n ^ 3) ω ≤ ENNReal.ofReal T} with hB1
  set B2 : Set Ω := {ω | ¬ WinOK T hh n
    (stepRelaxedSet β (stepWr β a Y ω) (stepAr β a Y ω))} with hB2
  set B3 : Set Ω := {ω | ¬ WinOK T hh n
    (stepRelaxedSet β (stepWr β (a + s 0) Y ω) (stepAr β (a + s 0) Y ω))} with hB3
  set B4 : Set Ω := {ω | pathTfast (stepWr β a Y ω) ((n : ℝ) ^ 3) ≤ ENNReal.ofReal T} with hB4
  set B5 : Set Ω := {ω | pathTfast (stepWr β (a + s 0) Y ω) ((n : ℝ) ^ 3) ≤ ENNReal.ofReal T}
    with hB5
  set B6 : Set Ω := {ω | ¬ (stepShift a (Y ω) ∈ StepCF (d := d) β ∧
    stepShift (a + s 0) (Y ω) ∈ StepCF (d := d) β)} with hB6
  have hPprob := hY.isProbabilityMeasure
  -- probabilities
  have p1 := hβc n₁ β n t₀ hβc' hn3 hreg hY hYp a (s 0)
  have p2 := H6 n₁ hn₁ β n t₀ hβ6 hreg Ω P Y hY hYp a
  have p3 := H6 n₁ hn₁ β n t₀ hβ6 hreg Ω P Y hY hYp (a + s 0)
  have p4 := Hf β hβ1.le hY hYp a hL1 hT1
  have p5 := Hf β hβ1.le hY hYp (a + s 0) hL1 hT1
  have p6 : P.real B6 = 0 := by
    have h1 := ae_stepShift_mem_stepCF_of_isSRW (β := β) hY hYp a
    have h2 := ae_stepShift_mem_stepCF_of_isSRW (β := β) hY hYp (a + s 0)
    have : P B6 = 0 := by
      refine measure_eq_zero_iff_ae_notMem.2 ?_
      filter_upwards [h1, h2] with ω hω1 hω2 hω
      exact hω ⟨hω1, hω2⟩
    simp [measureReal_def, this]
  have hsum := prob_sum_le (c6 := c6) (cf := cf) (Cf := Cf) (c := c) (T := T) (n := n) hCf hcdef
    hc6 hcf (hN2 n hnN2) hT1 hTle p1 p2 p3 p4 p5
  -- the inclusion
  have hsub : {ω | ∃ u : ℝ≥0, u ≤ s 0 + s 1 ∧ T ^ (2 * heavyEps d) ≤
      ‖stepReg β (stepShift a (Y ω)) u - stepNatTilde β a s 2 (Y ω) u‖} ⊆
      B1 ∪ B2 ∪ B3 ∪ B4 ∪ B5 ∪ B6 := by
    intro ω hω
    by_contra hnot
    simp only [mem_union, not_or] at hnot
    obtain ⟨⟨⟨⟨⟨n1, n2⟩, n3⟩, n4⟩, n5⟩, n6⟩ := hnot
    obtain ⟨u, hu, hnorm⟩ := hω
    have hCF : stepShift a (Y ω) ∈ StepCF (d := d) β ∧
        stepShift (a + s 0) (Y ω) ∈ StepCF (d := d) β := by
      by_contra h; exact n6 h
    have hofT : ENNReal.ofReal T = ((Tn : ℝ≥0) : WithTop ℝ≥0) := by
      rw [← hTn, ENNReal.ofReal_coe_nnreal]; rfl
    have key := lem71_det (β := β) hd1 hβ1 hY.isAdmissible_natFil hYp a (s 0) Tn n hn1 hhpos
      hs0Tn ω hCF.1 hCF.2
      (by rw [← hofT]; exact not_le.1 n1)
      (by rw [hTn]; exact not_not.1 n2) (by rw [hTn]; exact not_not.1 n3)
      (by rw [hTn]; exact not_le.1 n4) (by rw [hTn]; exact not_le.1 n5)
      u ((hu.trans hsTn))
    rw [stepNatTilde_two] at hnorm
    exact absurd (lt_of_le_of_lt key hbound) (not_lt.2 hnorm)
  calc P.real _ ≤ P.real (B1 ∪ B2 ∪ B3 ∪ B4 ∪ B5 ∪ B6) := measureReal_mono hsub
    _ ≤ P.real B1 + P.real B2 + P.real B3 + P.real B4 + P.real B5 + P.real B6 := by
      refine (measureReal_union_le _ _).trans ?_
      refine add_le_add ?_ le_rfl
      refine (measureReal_union_le _ _).trans ?_
      refine add_le_add ?_ le_rfl
      refine (measureReal_union_le _ _).trans ?_
      refine add_le_add ?_ le_rfl
      refine (measureReal_union_le _ _).trans ?_
      refine add_le_add ?_ le_rfl
      exact measureReal_union_le _ _
    _ ≤ Real.exp (-(c * (n : ℝ) ^ 3)) := by
      rw [p6, add_zero]; exact hsum

end ElboimSly.Paper.Step
