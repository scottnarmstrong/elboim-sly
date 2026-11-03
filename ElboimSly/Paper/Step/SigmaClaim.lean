/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Step.Lemma76
public import ElboimSly.Paper.Step.SigmaSmall
public import ElboimSly.Paper.Step.SigmaBm
public import ElboimSly.Paper.Step.SigmaNum
public import ElboimSly.Paper.Step.Lemma74
public import Mathlib

/-!
# The σ-estimate (the `σ`-estimate), conditional on Lemma 7.4

The σ-estimate (ES22 §7). `step_sigma_claim_of_tr` proves
`StepSigmaClaim` from `StepTr` (Lemma 7.4), splitting as in the written proof:

* **Case 1, `T > 3^{-16} β`**: the (H4) coupling at level `n(T)` (`stepRegime_level`) and the
  comparison of second moments `sigma_sq_close`.
* **Case 2, `T ≤ 3^{-16} β`**: `W = X` on `[0,T]`; `σ²` is computed from the simple random walk
  (`sigma_sq_small`).

The truncation event is `{sup < K}` on the countable set `checkTimes T` (a.s. equal to the
written proof's `{sup ≤ K}` up to the harmless strict inequality).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

namespace ElboimSly.Paper.Step

open ElboimSly.Paper ElboimSly.Cyclic

variable {d : ℕ}

theorem sigma_combine {V σ' A B C D : ℝ} (hV0 : 0 ≤ V) (hσ : 1 ≤ σ')
    (h1 : |V - σ' ^ 2| ≤ A) (h2 : A ≤ B - C) (h3 : |σ' - Real.sqrt 2| ≤ D - B) :
    |Real.sqrt V - Real.sqrt 2| ≤ D - C := by
  have hstep := abs_sqrt_sub_le hV0 hσ
  have := abs_sub_le (Real.sqrt V) σ' (Real.sqrt 2)
  linarith

theorem sigma_q_bound {n m : ℕ} {T c : ℝ} (hn100 : (100 : ℝ) ≤ n) (_hl2 : 0 < Real.log 2)
    (hy1 : 121 / 100 * Real.log 2 * n - Real.log 2 ≤ Real.log T)
    (hm5 : Real.logb 4 T - 1 ≤ m) (E5 : 1 ≤ 4 * c * n) :
    Real.exp (-((m : ℝ) ^ 2)) + Real.exp (-(c * (n : ℝ) ^ 3)) ≤
      2 * Real.exp (-((n : ℝ) ^ 2 / 4)) := by
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have hmn : (n : ℝ) / 2 ≤ m := by
    have h2 : (121 / 200 : ℝ) * n - 1 / 2 ≤ Real.logb 4 T := by
      rw [Real.logb, h4, le_div_iff₀ (by positivity)]
      have : (121 / 200 : ℝ) * n * (2 * Real.log 2) = 121 / 100 * Real.log 2 * n := by ring
      rw [sub_mul, this]
      linarith
    linarith
  have hn0 : (0 : ℝ) ≤ n / 2 := by positivity
  have e1 : Real.exp (-((m : ℝ) ^ 2)) ≤ Real.exp (-((n : ℝ) ^ 2 / 4)) := by
    apply Real.exp_le_exp.2
    have := pow_le_pow_left₀ hn0 hmn 2
    have e : ((n : ℝ) / 2) ^ 2 = (n : ℝ) ^ 2 / 4 := by ring
    linarith
  have e2 : Real.exp (-(c * (n : ℝ) ^ 3)) ≤ Real.exp (-((n : ℝ) ^ 2 / 4)) := by
    apply Real.exp_le_exp.2
    have h5 : (n : ℝ) ^ 2 / 4 ≤ c * (n : ℝ) ^ 3 := by
      have := mul_le_mul_of_nonneg_right E5 (sq_nonneg (n : ℝ))
      nlinarith
    linarith
  linarith

theorem step_sigma_claim_of_tr (hd : 1 ≤ d) {cTr : ℝ} (hcTr : 0 < cTr) {βTr : ℕ → ℝ}
    (hTr : StepTr d cTr βTr) : StepSigmaClaim d hd := by
  intro n₁ hn₁
  obtain ⟨N0, hN0⟩ := eventually_atTop.1 (sigma_eventually hcTr)
  refine ⟨max (βTr n₁) (max ((12 : ℝ) ^ 16) (max ((4 : ℝ) ^ (((n₁ : ℝ) + 2) / ((121 : ℝ) / 200)))
    ((4 : ℝ) ^ (N0 + 1)))), ?_⟩
  intro β _ n t₀ hβ hR Ω _ P N hN T hT1 hT2
  have hβ' : max (βTr n₁) (max ((12 : ℝ) ^ 16) (max ((4 : ℝ) ^ (((n₁ : ℝ) + 2) / ((121 : ℝ) / 200)))
    ((4 : ℝ) ^ (N0 + 1)))) ≤ β := hβ
  simp only [max_le_iff] at hβ'
  obtain ⟨hβtr, hβ12, hβ4, hβN⟩ := hβ'
  obtain ⟨-, hβ1, hn1, ht0, htn_lt, -⟩ := id hR
  obtain ⟨htn_gt, htn_le⟩ := indScale_bounds (n := n) ht0
  have hβ0 : 0 < β := by linarith
  have htn0 : 0 < indScale t₀ n := lt_trans (by positivity) htn_gt
  have hnN : N0 ≤ n := by
    have h1 : (4 : ℝ) ^ (N0 + 1) < 4 ^ (n + 1) :=
      lt_of_le_of_lt hβN (lt_of_lt_of_le htn_lt htn_le)
    have := (pow_lt_pow_iff_right₀ (by norm_num : (1 : ℝ) < 4)).1 h1
    omega
  obtain ⟨h100, S2, E3, E4, E5⟩ := hN0 n hnN
  have hn100 : (100 : ℝ) ≤ n := by exact_mod_cast h100
  set tn := indScale t₀ n with htn
  have hTpos : 0 < (T : ℝ) :=
    lt_of_lt_of_le (by have := Real.rpow_pos_of_pos htn0 ((121 : ℝ) / 200); positivity) hT1
  obtain ⟨hy1, hy2, hy3⟩ := log_T_bounds htn_gt htn_le hT1 hT2
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have hlogtn_lo : Real.log 4 * n ≤ Real.log tn := by
    have : Real.log ((4 : ℝ) ^ n) ≤ Real.log tn := Real.log_le_log (by positivity) htn_gt.le
    rw [Real.log_pow] at this
    linarith
  have hlogtn_hi : Real.log tn ≤ Real.log 4 * ((n : ℝ) + 1) := by
    have : Real.log tn ≤ Real.log ((4 : ℝ) ^ (n + 1)) := Real.log_le_log htn0 htn_le
    rw [Real.log_pow] at this
    push_cast at this; linarith
  -- facts about T
  have hy1' : 121 / 100 * Real.log 2 * n - Real.log 2 ≤ Real.log (T : ℝ) := by
    have := hy1; rw [h4] at this; linarith
  have hy2' : Real.log (T : ℝ) ≤ 121 / 100 * Real.log 2 * ((n : ℝ) + 1) := by
    have := hy2; rw [h4] at this; linarith
  have hlo' : 2 * Real.log 2 * n ≤ Real.log tn := by rw [← h4]; exact hlogtn_lo
  have hhi' : Real.log tn ≤ 2 * Real.log 2 * ((n : ℝ) + 1) := by rw [← h4]; exact hlogtn_hi
  have hnl : Real.log 2 * 100 ≤ Real.log 2 * n := mul_le_mul_of_nonneg_left hn100 hl2.le
  have hT_ge1 : 1 ≤ (T : ℝ) := by
    have : 0 ≤ Real.log (T : ℝ) := by nlinarith
    exact (Real.log_nonneg_iff hTpos).1 this
  have hT_le4n : (T : ℝ) ≤ 4 ^ n := by
    refine (Real.log_le_log_iff hTpos (by positivity)).1 ?_
    rw [Real.log_pow, h4]
    nlinarith
  have hT_letn : (T : ℝ) ≤ tn := by
    refine (Real.log_le_log_iff hTpos htn0).1 ?_
    nlinarith
  have hT_sqrt : Real.sqrt tn ≤ T := by
    refine Real.sqrt_le_iff.2 ⟨hTpos.le, ?_⟩
    refine (Real.log_le_log_iff htn0 (by positivity)).1 ?_
    rw [Real.log_pow]
    push_cast
    nlinarith
  have h4T : (4 : ℝ) ^ n₁ < T :=
    stepRegime_interval hR (κ := (121 : ℝ) / 200) (by norm_num) hβ4 hT1
  -- the tail bound of Lemma 7.4 at time `T`
  have hTrT := hTr n₁ hn₁ β n t₀ hβtr hR Ω P N hN (T : ℝ) hT_sqrt hT_letn
  set K : ℝ := (n : ℝ) ^ 2 * Real.sqrt T with hK
  have hKnn : 0 ≤ K := by positivity
  set p : ℝ := Real.exp (-(cTr * (n : ℝ) ^ 3)) with hp
  have hp0 : 0 < p := Real.exp_pos _
  have := hN.isProbabilityMeasure
  set V : ℝ := ∫ w, (blockY T K w ⟨0, hd⟩) ^ 2 ∂ppLaw P N T with hV
  have hV0 : 0 ≤ V := integral_nonneg fun w => sq_nonneg _
  by_cases hsm : (T : ℝ) ≤ β / 3 ^ 16
  · -- Case 2: short blocks
    have hTβ : (T : ℝ) ≤ β := hsm.trans (div_le_self hβ0.le (one_le_pow₀ (by norm_num)))
    obtain ⟨h1, h2⟩ := sigma_sq_small hd hR hN hT_ge1 hTβ hp0 hTrT
    exact (abs_sqrt_sub_sqrt_two_le hV0 h1 h2).trans
      (sigma_numeric_small hβ0 htn_lt htn_le S2)
  · -- Case 1: long blocks
    rw [not_le] at hsm
    obtain ⟨-, hm2, -, -, hm5, -, -, -, hH4⟩ := stepRegime_level hR h4T hT_le4n
    obtain ⟨σ', hσ'b, hC⟩ := hH4 Ω P N hN
    obtain ⟨hσ1, hσ2, -⟩ := step_sigma_bounds hβ12 hTpos hσ'b
    rw [Real.toNNReal_coe] at hC
    have hT16 : (T : ℝ) ^ (-(1 : ℝ) / 16) ≤ 3 * β ^ (-(1 : ℝ) / 16) := by
      have h1 : (T : ℝ) ^ (-(1 : ℝ) / 16) ≤ (β / 3 ^ 16) ^ (-(1 : ℝ) / 16) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) hsm.le (by norm_num)
      refine h1.trans (le_of_eq ?_)
      rw [Real.div_rpow hβ0.le (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
      have : ((16 : ℕ) : ℝ) * (-(1 : ℝ) / 16) = -1 := by norm_num
      rw [this, Real.rpow_neg_one]
      field_simp
    rw [max_eq_left (by linarith)] at hσ'b
    set m : ℕ := stepLevel (T : ℝ) with hm
    -- the truncation tail
    have hF : ppLaw P N T (farSet K T) ≤ ENNReal.ofReal p := by
      refine (ppLaw_tail hN T K).trans ?_
      rw [← ENNReal.ofReal_toReal (measure_ne_top P _)]
      exact ENNReal.ofReal_le_ofReal hTrT
    have hη0 : 0 ≤ Real.exp (-((m : ℝ) ^ 2)) := (Real.exp_pos _).le
    have hq0 : 0 < Real.exp (-((m : ℝ) ^ 2)) + p := by positivity
    have hTpos' : 0 < T := by exact_mod_cast hTpos
    have hclose := sigma_sq_close hd hN hTpos' (σ' := σ') (ε := (T : ℝ) ^ indThetaH)
      (η := Real.exp (-((m : ℝ) ^ 2))) (K := K) (pF := p) (by linarith)
      (Real.rpow_nonneg hTpos.le _) hη0 hKnn hp0.le hq0 hC hF
    have hKT : K / Real.sqrt (T : ℝ) = (n : ℝ) ^ 2 := by
      have : 0 < Real.sqrt (T : ℝ) := Real.sqrt_pos.2 hTpos
      rw [hK]; field_simp
    rw [hKT] at hclose
    -- the bound on the tail probabilities
    have hq := sigma_q_bound (T := (T : ℝ)) (m := m) (c := cTr) hn100 hl2 hy1' hm5 E5
    have hbig := sigma_numeric_big (n := n) (tn := tn) (T := T) (σ' := σ')
      (q := Real.exp (-((m : ℝ) ^ 2)) + p) h100 htn_gt htn_le hT1 hT2 hσ1 hσ2 hq0.le hq E3 E4
    have hθ : indThetaH = (41 : ℝ) / 100 := by unfold indThetaH; norm_num
    rw [hθ] at hclose
    exact sigma_combine hV0 hσ1 hclose hbig hσ'b

end ElboimSly.Paper.Step
