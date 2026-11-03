/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Escape.C57Thr
public import ElboimSly.Paper.Escape.C57Asym
public import ElboimSly.Paper.Escape.C57AsymN
public import ElboimSly.Paper.Avoid.Claim2Count
public import ElboimSly.Foundations.Brownian.EscapeLineProb
public import Mathlib

/-!
# ES22 Claim 5.7

ES22 Claim 5.7.

`es5_7`: for `n₀` there is `β₅₇` such that for `β ≥ β₅₇` under (S1)-(S2), for every block `u`,
`β'` and `1 ≤ i ≤ I_*`, almost surely
`P(r_i ≤ 4^{j-1}, W_i^←(r_i) ∈ F_B | ℱ^{(i)}_{S₂}) ≥ c₅₇(d)/2`.
The levels, `L₇ = (ln β)²`, `t₇ = L₇^{1/θ_H}` and all numerical thresholds of
`es5_7_thr` are discharged.  The independent process `N''` is still an extra Poisson point
process on the space (see the `Es4Space` transfer wrapper).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Escape

open ElboimSly ElboimSly.Brownian ElboimSly.Cyclic ElboimSly.Cyclic.CycSchemeEnv ElboimSly.Paper

set_option linter.unusedSectionVars false

variable {k : ℕ}

theorem es57_log_lt {β : ℝ} {n : ℕ} (hβ : 0 < β) (h : β < 4 ^ (n + 1)) :
    Real.log β < ((n : ℝ) + 1) * (3 / 2) := by
  have h1 := Real.log_lt_log hβ h
  rw [Real.log_pow] at h1
  have h2 : Real.log 4 < 3 / 2 := by
    have := Real.log_two_lt_d9
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; linarith
  push_cast at h1
  nlinarith

theorem es57_nL {x n : ℝ} (hx8 : 8 ≤ x) (hn3 : 3 ≤ n) (hxn : x ≤ 2 * n) :
    x ^ 2 + 1 < n ^ 17 / 6 - 2 ∧ x ≤ n ^ 17 / 7 := by
  have h17 : (3 : ℝ) ^ 15 ≤ n ^ 15 := pow_le_pow_left₀ (by norm_num) hn3 15
  have h16 : (3 : ℝ) ^ 16 ≤ n ^ 16 := pow_le_pow_left₀ (by norm_num) hn3 16
  have e1 : n ^ 17 = n ^ 2 * n ^ 15 := by ring
  have e2 : n ^ 17 = n * n ^ 16 := by ring
  have hx2 : x ^ 2 ≤ 4 * n ^ 2 := by nlinarith
  constructor
  · rw [e1]; nlinarith [sq_nonneg n]
  · rw [e2]; nlinarith

theorem es57_err {c e₁ e₂ e₃ : ℝ} (h₁ : 0 ≤ e₁) (h₂ : 0 ≤ e₂) (h₃ : 0 ≤ e₃) (hc : 0 ≤ c)
    (h : c / 2 + e₁ + e₂ + e₃ ≤ c) :
    ENNReal.ofReal (c / 2) ≤ ENNReal.ofReal c - ENNReal.ofReal e₁ - ENNReal.ofReal e₂ -
      ENNReal.ofReal e₃ := by
  refine ENNReal.le_sub_of_add_le_right ENNReal.ofReal_ne_top
    (ENNReal.le_sub_of_add_le_right ENNReal.ofReal_ne_top
      (ENNReal.le_sub_of_add_le_right ENNReal.ofReal_ne_top ?_))
  rw [← ENNReal.ofReal_add (by positivity) h₃, ← ENNReal.ofReal_add (by positivity) h₂,
    ← ENNReal.ofReal_add (by positivity) h₁]
  exact ENNReal.ofReal_le_ofReal (by linarith)

theorem es57_exp2 {x : ℝ} (hx : 8 ≤ x) : Real.exp 2 ≤ x := by
  have h1 := Real.exp_one_lt_d9
  have h2 := Real.exp_pos 1
  have : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
  rw [this]; nlinarith

theorem es57_S {S : ℝ≥0} {n j : ℕ} (hjn : j ≤ n) (hS : (S : ℝ) = ((2 : ℝ) ^ j) ^ 2 / 4) :
    0 < S ∧ (S : ℝ) ≤ 4 ^ n := by
  have hS0' : (0 : ℝ) < S := by rw [hS]; positivity
  refine ⟨by exact_mod_cast hS0', ?_⟩
  have h1 : ((2 : ℝ) ^ j) ^ 2 = 4 ^ j := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have h2 : (4 : ℝ) ^ j ≤ 4 ^ n := pow_le_pow_right₀ (by norm_num) hjn
  rw [hS, h1]; linarith [pow_pos (by norm_num : (0 : ℝ) < 4) j]

theorem es57_T5 {x : ℝ} {n : ℕ} (hx1 : 1 ≤ x) (hxn : x ≤ 2 * n) (hn5 : 32 * (n : ℝ) ^ 5 ≤ 4 ^ n) :
    (x ^ 2) ^ (100 / 41 : ℝ) ≤ 4 ^ n := by
  have hx0 : 0 ≤ x := by linarith
  have hT : (x ^ 2) ^ (100 / 41 : ℝ) = x ^ (200 / 41 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0]; norm_num
  rw [hT]
  calc x ^ (200 / 41 : ℝ) ≤ x ^ (5 : ℕ) := by
        rw [← Real.rpow_natCast]; exact Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
    _ ≤ (2 * n) ^ 5 := by gcongr
    _ = 32 * (n : ℝ) ^ 5 := by ring
    _ ≤ 4 ^ n := hn5

theorem es57_LT {x : ℝ} (hx1 : 1 ≤ x) : x ^ 2 ≤ (x ^ 2) ^ (100 / 41 : ℝ) := by
  have hx0 : 0 ≤ x := by linarith
  have hT : (x ^ 2) ^ (100 / 41 : ℝ) = x ^ (200 / 41 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0]; norm_num
  rw [hT, show (x ^ 2 : ℝ) = x ^ (2 : ℝ) by rw [Real.rpow_two]]
  exact Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)

theorem es57_Itop {n j I : ℕ} (hI : I = Nat.findGreatest (fun i => 1 ≤ i ∧
    16 * (i * escLambda n) ≤ 3 * 2 ^ j) (n ^ 3)) (h1 : 1 ≤ I) :
    16 * (I * escLambda n) ≤ 3 * 2 ^ j :=
  (Nat.findGreatest_of_ne_zero (P := fun i => 1 ≤ i ∧ 16 * (i * escLambda n) ≤ 3 * 2 ^ j)
    hI.symm (by omega)).2

theorem es5_7 (hd : 5 ≤ k + 2) :
    ∀ n₀ : ℕ, ∃ β₅₇ : ℝ, ∀ (β : ℝ) [Fact (0 < β)], β₅₇ ≤ β → ∀ (n : ℕ) (t₀ : ℝ),
      Es4Params (k + 2) β n₀ n t₀ → ∀ {Ω : Type} (𝒢₀ : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω]
        {Pr : Measure Ω} {N N' N'' : Ω → Measure (CycS ℕ (k + 2) β)},
        IsPoissonPointProcess N (cycIntensity ℕ (k + 2) β) Pr →
        IsPoissonPointProcess N' (cycIntensity ℕ (k + 2) β) Pr →
        IsPoissonPointProcess N''
          ((Measure.count : Measure ℕ).prod (ringIntensity (k + 2) β)) Pr →
        Indep 𝒢₀ (MeasurableSpace.comap N inferInstance) Pr →
        Indep (MeasurableSpace.comap N' inferInstance)
          (𝒢₀ ⊔ MeasurableSpace.comap N inferInstance) Pr →
        Indep (MeasurableSpace.comap N'' inferInstance)
          (𝒢₀ ⊔ MeasurableSpace.comap N inferInstance ⊔ MeasurableSpace.comap N' inferInstance ⊔
            cycNull Pr) Pr →
        𝒢₀ ≤ mΩ → ∀ (tn : ℝ) (u : EscV k) (β' i : ℕ) (hlog : 1 < Real.log β),
        1 ≤ i → i ≤ escIstar n (escJ n) →
        ∀ {S : ℝ≥0}, (S : ℝ) = ((2 : ℝ) ^ escJ n) ^ 2 / 4 →
        ∀ᵐ ω ∂Pr, ENNReal.ofReal (c57 (k + 2) / 2) ≤ resPhi (plan5 n β tn u β' i hlog) Pr N
          (lamT (plan5 n β tn u β' i hlog) N (escIstar n (escJ n) + 1))
          (exitSet (β := β) (escJ n) u S
            (((0 : ℕ), escPoint n (escJ n) u i, (β' : ℝ), false) : CycData ℕ (k + 2))) ω := by
  obtain ⟨nD, C₄₃, C₄₂, h43, h42, H⟩ := es5_7_thr (k := k) hd
  intro n₀
  have hk : 1 ≤ k := by omega
  set c : ℝ := c57 (k + 2) with hcdef
  have hc : 0 < c := ctube_pos _ _
  obtain ⟨R, hR2, hR⟩ := polylog_bound (k + 2)
  obtain ⟨N₁, hN3, hN⟩ := asym_n n₀ (2 * c / 3) (by positivity)
  obtain ⟨X, hX⟩ := eventually_atTop.1 (asym_step_e.and ((asym_step_f (k := k) hk C₄₃ C₄₂ (c / 6)
    (by positivity)).and (eventually_ge_atTop (max (max (max 8 R) (2 * ((max N₁ nD : ℕ) : ℝ)))
      ((4 : ℝ) ^ (n₀ + 1))))))
  refine ⟨Real.exp (max X (max (max 8 R) (max (2 * ((max N₁ nD : ℕ) : ℝ))
    ((4 : ℝ) ^ (n₀ + 1))))), ?_⟩
  intro β _ hβ n t₀ hp Ω 𝒢₀ mΩ Pr N N' N'' hN0 hN' hN'' hI1 hI2 hI3 h𝒢 tn u β' i hlog hi1 hiI S hS
  have hβpos : 0 < β := Fact.out
  set x : ℝ := Real.log β with hx
  have hxX := (Real.le_log_iff_exp_le hβpos).2 hβ
  have hxX' : X ≤ x := le_trans (le_max_left _ _) hxX
  have hxA := le_trans (le_max_right _ _) hxX
  simp only [max_le_iff] at hxA
  obtain ⟨⟨hx8, hRx⟩, h2M, h4x⟩ := hxA
  obtain ⟨he, hf, -⟩ := hX x hxX'
  obtain ⟨hf1, hf2⟩ := hf h43.le h42.le
  have hx0 : 0 ≤ x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hβlt : β < 4 ^ (n + 1) := by
    have h1 := hp.beta_lt
    have h2 := hp.le_four
    unfold indScale at h1
    calc β < 4 ^ n * t₀ := h1
      _ ≤ 4 ^ n * 4 := by gcongr
      _ = 4 ^ (n + 1) := by ring
  have hxlt : x < ((n : ℝ) + 1) * (3 / 2) := es57_log_lt hβpos hβlt
  have hM3 : 3 ≤ max N₁ nD := le_trans hN3 (le_max_left _ _)
  have hMn : max N₁ nD ≤ n := by
    have h3 : (3 : ℝ) ≤ ((max N₁ nD : ℕ) : ℝ) := by exact_mod_cast hM3
    have : ((max N₁ nD : ℕ) : ℝ) ≤ n := by nlinarith
    exact_mod_cast this
  have hN1n : N₁ ≤ n := le_trans (le_max_left _ _) hMn
  have hnDn : nD ≤ n := le_trans (le_max_right _ _) hMn
  have hn3 : 3 ≤ n := le_trans hN3 hN1n
  have hn3r : (3 : ℝ) ≤ n := by exact_mod_cast hn3
  have hxn : x ≤ 2 * n := by nlinarith
  obtain ⟨hjn₀, hj40, hjn, hexp, hn5⟩ := hN n hN1n
  set j := escJ n with hjdef
  have hθ : indThetaH = 41 / 100 := by unfold indThetaH; norm_num
  have hn2 : 2 ≤ n := by omega
  have hxx : x ≤ x ^ 2 := by nlinarith
  have hLT := es57_LT hx1
  have hT5 := es57_T5 hx1 hxn hn5
  have hL4 : (4 : ℝ) ^ (n₀ + 1) ≤ x ^ 2 := h4x.trans hxx
  obtain ⟨hS0, hS4⟩ := es57_S hjn hS
  have hI1' : 1 ≤ escIstar n j := le_trans hi1 hiI
  have hIlam := es57_Itop (n := n) (j := j) rfl hI1'
  have hexpr : Real.exp (-((avoidLevel ((4 : ℝ) ^ j) : ℕ) : ℝ) ^ 2) ≤ c / 6 := by
    rw [avoidLevel_pow j (by omega)]
    have := hexp; linarith
  have hsum : c / 2 + Real.exp (-((avoidLevel ((4 : ℝ) ^ j) : ℕ) : ℝ) ^ 2) +
      C₄₃ * (x ^ 2 + 1) ^ (k + 2 - 2) * ((x ^ 2) ^ (100 / 41 : ℝ)) ^ (-((k + 2 - 2 : ℕ) : ℝ) / 2) +
      C₄₂ * (x ^ 2) ^ (-(1 : ℝ) / 30) ≤ c := by
    have h1 := hf1
    have h2 := hf2
    simp only [Nat.add_sub_cancel]
    linarith
  have hnn1 : 0 ≤ Real.exp (-((avoidLevel ((4 : ℝ) ^ j) : ℕ) : ℝ) ^ 2) := (Real.exp_pos _).le
  have hnn2 : 0 ≤ C₄₃ * (x ^ 2 + 1) ^ (k + 2 - 2) * ((x ^ 2) ^ (100 / 41 : ℝ)) ^
      (-((k + 2 - 2 : ℕ) : ℝ) / 2) := by positivity
  have hnn3 : 0 ≤ C₄₂ * (x ^ 2) ^ (-(1 : ℝ) / 30) := by positivity
  have hcc := es57_err hnn1 hnn2 hnn3 hc.le hsum
  obtain ⟨hnL, hxn7⟩ := es57_nL hx8 hn3r hxn
  refine H β n₀ n t₀ hp 𝒢₀ hN0 hN' hN'' hI1 hI2 hI3 h𝒢 tn u β' i hlog hi1 hiI hn2
    (by exact_mod_cast le_two_pow_escJ n) (by omega) hIlam
    (pow_lt_pow_right₀ (by norm_num) (by omega)) (pow_le_pow_right₀ (by norm_num) hjn)
    (by rw [hθ]; exact asym_eps hj40) hS hS0 hS4 (le_trans hL4 hLT) hT5 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ hcc
  · rw [hθ, asymT_pow hx0]
    have : x ^ (200 / 41 * (41 / 100) : ℝ) = x ^ 2 := by
      rw [show (200 / 41 * (41 / 100) : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [this]; linarith
  · exact asym_step_c (by linarith)
  · exact hL4
  · exact le_trans hLT hT5
  · simp only [Nat.add_sub_cancel]; positivity
  · positivity
  · exact max_le (by linarith [hxx]) (by have h := mul_le_mul hx8 hx8 (by norm_num) hx0; have := sq x; linarith)
  · have := he; rwa [Real.exp_log hβpos] at this
  · exact hnL
  · exact hnDn
  · exact es57_exp2 hx8
  · exact hxn7
  · exact_mod_cast two_pow_escJ_lt hn2
  · exact Nat.findGreatest_le _
  · intro r hr
    exact hR r (le_trans hRx (le_trans hxx hr))

end ElboimSly.Paper.Escape
