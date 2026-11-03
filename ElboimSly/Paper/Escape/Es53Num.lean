/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Escape.Es53NumDef
public import ElboimSly.Paper.Escape.Es53NumA
public import ElboimSly.Paper.Escape.Es53NumB
public import ElboimSly.Paper.Escape.Es53NumC
public import Mathlib

/-!
# The thresholds of ES22 Lemma 5.3 hold for `β ≥ β_{53}`

ES22 Lemma 5.3, "Thresholds".  For given constants (depending only on `d`) and `n₀` there is
`β_{53}` such that `β ≥ β_{53}` implies every inequality of `Es53Num` (`es53_num`), for
`m₁ = ⌊ln ln β / 2⌋`.  This uses the explicit scales `n ≥ 10^{18}` (instead of the sharper `n ≥ 37201` of
the written proof, D11), which only strengthens the requirement `β ≥ β_{53}`.
-/

@[expose] public section

open scoped NNReal ENNReal

namespace ElboimSly.Paper.Escape

open ElboimSly ElboimSly.Paper ElboimSly.Brownian

theorem herr_of {c : ℝ} {η Eb Ebp Ec Ed : ℝ≥0∞}
    (hsum : η + Eb + Ebp + Ec + Ed ≤ ENNReal.ofReal (c / 2)) :
    ENNReal.ofReal (c / 2) ≤ ENNReal.ofReal c - η - Eb - Ebp - Ec - Ed := by
  by_cases hc : 0 ≤ c
  · have hne : η + Eb + Ebp + Ec + Ed ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hsum
    have h2 : ENNReal.ofReal (c / 2) + (η + Eb + Ebp + Ec + Ed) ≤ ENNReal.ofReal c := by
      calc ENNReal.ofReal (c / 2) + (η + Eb + Ebp + Ec + Ed) ≤
            ENNReal.ofReal (c / 2) + ENNReal.ofReal (c / 2) := by gcongr
        _ = ENNReal.ofReal c := by
            rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; congr 1; ring
    have h3 := ENNReal.le_sub_of_add_le_right hne h2
    refine h3.trans (le_of_eq ?_)
    simp only [tsub_tsub, add_assoc]
  · have : ENNReal.ofReal (c / 2) = 0 := ENNReal.ofReal_of_nonpos (by linarith [not_le.1 hc])
    rw [this]; exact bot_le

theorem pow17_facts (n : ℕ) (hn : 2 ≤ n) :
    (14 : ℝ) * n ≤ (n : ℝ) ^ 17 ∧ (84 : ℝ) ≤ (n : ℝ) ^ 17 := by
  have hn2r : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have h16 : (14 : ℝ) ≤ (n : ℝ) ^ 16 := by
    calc (14 : ℝ) ≤ 2 ^ 16 := by norm_num
      _ ≤ (n : ℝ) ^ 16 := pow_le_pow_left₀ (by norm_num) hn2r 16
  have h17 : (2 : ℝ) ^ 17 ≤ (n : ℝ) ^ 17 := pow_le_pow_left₀ (by norm_num) hn2r 17
  refine ⟨?_, by norm_num at h17; linarith⟩
  have : (n : ℝ) ^ 17 = (n : ℝ) ^ 16 * n := by ring
  rw [this]; nlinarith

/-- The scales `m₁ = ⌊ln ln β / 2⌋` and `n` for `β ≥ exp (exp (2 M))`. -/
theorem scales_of_beta {d n₀ n : ℕ} {t₀ β : ℝ} [Fact (0 < β)] (hp : Es4Params d β n₀ n t₀)
    {M : ℕ} (hM : 3 ≤ M) (hβ : Real.exp (Real.exp (2 * M)) ≤ β) :
    M ≤ ⌊Real.log (Real.log β) / 2⌋₊ ∧ (⌊Real.log (Real.log β) / 2⌋₊ : ℝ) ≤ Real.log (Real.log β) / 2 ∧
      (4 : ℝ) ^ ⌊Real.log (Real.log β) / 2⌋₊ ≤ Real.log β ∧ Real.exp (2 * M) ≤ Real.log β ∧
      M ≤ n ∧ Real.log β ≤ 2 * n ∧ ⌊Real.log (Real.log β) / 2⌋₊ ≤ n := by
  have hβ0 : 0 < β := Fact.out
  set L := Real.log β with hL
  have hL1 : Real.exp (2 * M) ≤ L := (Real.le_log_iff_exp_le hβ0).2 hβ
  have hL0 : 0 < L := lt_of_lt_of_le (Real.exp_pos _) hL1
  have hlnL : (2 * M : ℝ) ≤ Real.log L := (Real.le_log_iff_exp_le hL0).2 hL1
  have hM3 : (3 : ℝ) ≤ M := by exact_mod_cast hM
  have hlnL0 : 0 ≤ Real.log L / 2 := by linarith
  have hm1M : M ≤ ⌊Real.log L / 2⌋₊ := Nat.le_floor (by linarith)
  have hm1le : (⌊Real.log L / 2⌋₊ : ℝ) ≤ Real.log L / 2 := Nat.floor_le hlnL0
  have h4 : (4 : ℝ) ^ ⌊Real.log L / 2⌋₊ ≤ L := by
    have hlog4 : Real.log 4 ≤ 2 := by
      have : Real.log 4 = 2 * Real.log 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
      have := Real.log_two_lt_d9
      linarith
    have hlog40 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    rw [← Real.log_le_log_iff (by positivity) hL0, Real.log_pow]
    calc (⌊Real.log L / 2⌋₊ : ℝ) * Real.log 4 ≤ (Real.log L / 2) * Real.log 4 :=
          mul_le_mul_of_nonneg_right hm1le hlog40
      _ ≤ (Real.log L / 2) * 2 := mul_le_mul_of_nonneg_left hlog4 hlnL0
      _ = Real.log L := by ring
  -- `n`
  have hβn : β < 4 ^ (n + 1) := by
    have h1 := hp.beta_lt
    have h2 := hp.le_four
    have h3 : indScale t₀ n = 4 ^ n * t₀ := rfl
    rw [h3] at h1
    calc β < 4 ^ n * t₀ := h1
      _ ≤ 4 ^ n * 4 := by gcongr
      _ = 4 ^ (n + 1) := by ring
  have hlog4 : Real.log 4 ≤ 1.3863 := by
    have : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    have := Real.log_two_lt_d9
    linarith
  have hLn : L < ((n : ℝ) + 1) * 1.3863 := by
    have h1 := Real.log_lt_log hβ0 hβn
    rw [Real.log_pow] at h1
    push_cast at h1
    rw [hL]
    nlinarith
  have hexp : (2 * M : ℝ) + 1 ≤ Real.exp (2 * M) := by
    have := Real.add_one_le_exp (2 * (M : ℝ)); linarith
  have hnM : M ≤ n := by
    by_contra hh
    push Not at hh
    have : (n : ℝ) + 1 ≤ M := by exact_mod_cast hh
    nlinarith
  have hn3 : (3 : ℝ) ≤ n := by
    have : M ≤ n := hnM
    have h3 : (3 : ℝ) ≤ M := hM3
    have : (M : ℝ) ≤ n := by exact_mod_cast hnM
    linarith
  have hL2n : L ≤ 2 * n := by nlinarith
  have hm1n : ⌊Real.log L / 2⌋₊ ≤ n := by
    have h1 := Real.log_le_sub_one_of_pos hL0
    have : (⌊Real.log L / 2⌋₊ : ℝ) ≤ n := by linarith
    exact_mod_cast this
  exact ⟨hm1M, hm1le, h4, hL1, hnM, hL2n, hm1n⟩

theorem es53_num (k : ℕ) (hk : 3 ≤ k) (nD : ℕ) (CB CB' CC CD cD : ℝ) (hCB : 0 < CB)
    (hCB' : 0 < CB') (hCC : 0 < CC) (hCD : 0 < CD) (hcD : 0 < cD) (n₀ : ℕ) :
    ∃ β53 : ℝ, ∀ {β : ℝ} [Fact (0 < β)] {n : ℕ} {t₀ : ℝ},
      Es4Params (k + 2) β n₀ n t₀ → β53 ≤ β →
        ∃ m₁ : ℕ, Es53Num k n₀ n m₁ nD β CB CB' CC CD cD := by
  classical
  set c : ℝ := cline (k + 2) with hc
  set ε : ℝ := if 0 < c then c / 10 else 1 with hεdef
  have hε : 0 < ε := by
    rw [hεdef]; split_ifs with h
    · positivity
    · norm_num
  set J : ℕ := max (max 40 (n₀ + 1)) (max ⌈1 / ε⌉₊ ⌈CB' / ε⌉₊) with hJ
  set NC : ℕ := ⌈(CC / ε) ^ 2⌉₊ + 3 with hNC
  set N₀ : ℕ := max (max (max (n53 (k + 2)) nD) (max (10 ^ 18) (2 ^ J)))
    (max (4 ^ (n₀ + 1)) (max NC 400)) with hN₀
  set M₁ : ℕ := ⌈1 + CB * 8 ^ k / ε⌉₊ + 2 with hM₁
  set M₂ : ℕ := ⌈(Real.log 16 + 1) / cD⌉₊ + 1 with hM₂
  set M₃ : ℕ := ⌈2 * CD / ε⌉₊ + 1 with hM₃
  set M : ℕ := max (max (max 8 (n₀ + 1)) M₁) (max M₂ M₃) with hM
  set M' : ℕ := max (max M N₀) 3 with hM'
  refine ⟨Real.exp (Real.exp (2 * M')), ?_⟩
  intro β _ n t₀ hp hβ
  have hM'3 : 3 ≤ M' := le_max_right _ _
  obtain ⟨hm1M, hm1le, h4, hL1, hnM, hL2n, hm1n⟩ := scales_of_beta hp hM'3 hβ
  set m₁ := ⌊Real.log (Real.log β) / 2⌋₊ with hm₁
  refine ⟨m₁, ?_⟩
  -- basic facts
  have hm1M' : M' ≤ m₁ := hm1M
  have hMge : M ≤ M' := le_trans (le_max_left _ _) (le_max_left _ _)
  have hN₀ge : N₀ ≤ M' := le_trans (le_max_right _ _) (le_max_left _ _)
  have hnN₀ : N₀ ≤ n := hN₀ge.trans hnM
  have hm1ge : M ≤ m₁ := hMge.trans hm1M'
  have hn2 : 2 ≤ n := by
    have : 400 ≤ N₀ := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
    omega
  have hn400 : 400 ≤ n := by
    have : 400 ≤ N₀ := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
    omega
  have hn53 : n53 (k + 2) ≤ n := by
    have : n53 (k + 2) ≤ N₀ := le_trans (le_max_left _ _) (le_trans (le_max_left _ _)
      (le_trans (le_max_left _ _) (le_refl _)))
    omega
  have hnD : nD ≤ n := by
    have : nD ≤ N₀ := le_trans (le_max_right _ _) (le_trans (le_max_left _ _)
      (le_trans (le_max_left _ _) (le_refl _)))
    omega
  have hn18 : (10 : ℝ) ^ 18 ≤ n := by
    have : 10 ^ 18 ≤ N₀ := le_trans (le_max_left _ _) (le_trans (le_max_right _ _)
      (le_trans (le_max_left _ _) (le_refl _)))
    exact_mod_cast le_trans this hnN₀
  have hn2J : 2 ^ J ≤ n := by
    have : 2 ^ J ≤ N₀ := le_trans (le_max_right _ _) (le_trans (le_max_right _ _)
      (le_trans (le_max_left _ _) (le_refl _)))
    omega
  have hn4 : 4 ^ (n₀ + 1) ≤ n := by
    have : 4 ^ (n₀ + 1) ≤ N₀ := le_trans (le_max_left _ _) (le_max_right _ _)
    omega
  have hnNC : NC ≤ n := by
    have : NC ≤ N₀ := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
    omega
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hn2r : (2 : ℝ) ≤ n := by exact_mod_cast hn2
  -- the scale `j`
  obtain ⟨hj1, hj1'⟩ := escJ_real_bounds hn2
  have hj20 := escJ_ge_twenty hn2
  have hj20n := escJ_le_twenty_mul hn2
  have hjJ : J ≤ escJ n := by
    have h1 : n ≤ n ^ 20 := Nat.le_self_pow (by norm_num) n
    have h2 := le_two_pow_escJ n
    have : 2 ^ J ≤ 2 ^ escJ n := by omega
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 this
  have hjn₀ : n₀ + 1 ≤ escJ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hjJ |>.trans' (le_refl _)
  have hj40 : 40 ≤ escJ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hjJ
  have hjr : (40 : ℝ) ≤ escJ n := by exact_mod_cast hj40
  have hj0 : (0 : ℝ) < escJ n := by linarith
  have hj1ε : 1 / ε ≤ (escJ n : ℝ) := by
    have h1 : ⌈1 / ε⌉₊ ≤ escJ n := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hjJ
    exact (Nat.le_ceil _).trans (by exact_mod_cast h1)
  have hjB'ε : CB' / ε ≤ (escJ n : ℝ) := by
    have h1 : ⌈CB' / ε⌉₊ ≤ escJ n := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hjJ
    exact (Nat.le_ceil _).trans (by exact_mod_cast h1)
  have hjn_r : (escJ n : ℝ) ≤ 20 * n := by exact_mod_cast hj20n
  -- `j 4^j ≤ 80 n^41 ≤ 4^n`
  have h4j : (4 : ℝ) ^ escJ n ≤ 4 * (n : ℝ) ^ 40 := by
    have : (4 : ℝ) ^ escJ n = ((2 : ℝ) ^ escJ n) ^ 2 := by
      rw [← pow_mul, mul_comm, pow_mul]; norm_num
    rw [this]
    calc ((2 : ℝ) ^ escJ n) ^ 2 ≤ (2 * (n : ℝ) ^ 20) ^ 2 :=
          pow_le_pow_left₀ (by positivity) hj1'.le 2
      _ = 4 * (n : ℝ) ^ 40 := by ring
  have hjT : (escJ n : ℝ) * 4 ^ escJ n ≤ 80 * (n : ℝ) ^ 41 := by
    calc (escJ n : ℝ) * 4 ^ escJ n ≤ (20 * n) * (4 * (n : ℝ) ^ 40) :=
          mul_le_mul hjn_r h4j (by positivity) (by positivity)
      _ = 80 * (n : ℝ) ^ 41 := by ring
  have hp41 := pow_le_four_pow n hn400
  have hT2 : (escJ n : ℝ) * 4 ^ escJ n ≤ 4 ^ n := hjT.trans hp41
  have hε1 : ((escJ n : ℝ) * 4 ^ escJ n) ^ indThetaH ≤ (n : ℝ) ^ 17 / 30 :=
    (Real.rpow_le_rpow (by positivity) hjT (by unfold indThetaH; norm_num)).trans (theta_n n hn18)
  have hn17 : (n : ℝ) ^ 17 ≤ (n : ℝ) ^ 20 := pow_le_pow_right₀ (by linarith) (by norm_num)
  have hε2 : ((escJ n : ℝ) * 4 ^ escJ n) ^ indThetaH ≤ 3 * (2 : ℝ) ^ escJ n / 40 := by
    refine hε1.trans ?_
    have : (n : ℝ) ^ 20 ≤ 2 ^ escJ n := hj1
    have h0 : 0 ≤ (n : ℝ) ^ 17 := by positivity
    linarith
  have hT1 : (4 : ℝ) ^ (n₀ + 1) ≤ (escJ n : ℝ) * 4 ^ escJ n := by
    have : (4 : ℝ) ^ (n₀ + 1) ≤ 4 ^ escJ n := pow_le_pow_right₀ (by norm_num) hjn₀
    have h1 : (1 : ℝ) ≤ escJ n := by linarith
    exact this.trans (le_mul_of_one_le_left (by positivity) h1)
  obtain ⟨hn17', hn17''⟩ := pow17_facts n hn2
  have hlb : Real.log β ≤ (n : ℝ) ^ 17 / 7 := by linarith
  have hL1' : (4 : ℝ) ^ (n₀ + 1) ≤ (n : ℝ) ^ 17 / 7 := by
    have : (4 : ℝ) ^ (n₀ + 1) ≤ n := by exact_mod_cast hn4
    linarith
  have hL2' : (n : ℝ) ^ 17 / 7 ≤ 4 ^ n := by
    have : (n : ℝ) ^ 17 ≤ (n : ℝ) ^ 41 := pow_le_pow_right₀ (by linarith) (by norm_num)
    have h0 : 0 ≤ (n : ℝ) ^ 41 := by positivity
    linarith
  have hL3' : (n : ℝ) ^ 17 / 7 ≤ (n : ℝ) ^ 17 / 6 - 2 := by
    linarith
  have hβ2 : Real.exp 2 ≤ Real.log β := by
    refine le_trans (Real.exp_le_exp.2 ?_) hL1
    have : (3 : ℝ) ≤ M' := by exact_mod_cast hM'3
    linarith
  have hlnL0 : 0 ≤ Real.log (Real.log β) := by
    have h1 : (1 : ℝ) ≤ Real.log β := by
      refine le_trans ?_ hL1
      have := Real.add_one_le_exp (2 * (M' : ℝ))
      have : (0 : ℝ) ≤ M' := Nat.cast_nonneg _
      linarith
    exact Real.log_nonneg h1
  have hm8 : 8 ≤ m₁ := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _))
    (le_max_left _ _)) hm1ge
  have hm₁n₀ : n₀ + 1 ≤ m₁ := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _))
    (le_max_left _ _)) hm1ge
  -- the error terms
  have hj1n : (1 : ℕ) ≤ escJ n := by omega
  have hη : ENNReal.ofReal (Real.exp (-((avoidLevel ((escJ n : ℝ) * 4 ^ escJ n) : ℕ) : ℝ) ^ 2)) ≤
      ENNReal.ofReal ε := by
    refine ENNReal.ofReal_le_ofReal ((eta_le (escJ n) hj1n).trans ?_)
    exact ((one_div_le hj0 hε).2 hj1ε)
  have hm2 : 2 ≤ m₁ := by omega
  have hEb : errB CB k m₁ n ≤ ENNReal.ofReal ε := by
    refine (errB_le CB hCB.le k m₁ n (by omega) hm2).trans (ENNReal.ofReal_le_ofReal ?_)
    have hM₁m : M₁ ≤ m₁ := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hm1ge
    have h1 : 1 + CB * 8 ^ k / ε ≤ (M₁ : ℝ) := by
      have := Nat.le_ceil (1 + CB * 8 ^ k / ε)
      rw [hM₁]; push_cast; linarith
    have h2 : (M₁ : ℝ) ≤ m₁ := by exact_mod_cast hM₁m
    have hm1pos : (0 : ℝ) < (m₁ : ℝ) - 1 := by
      have : (2 : ℝ) ≤ m₁ := by exact_mod_cast hm2
      linarith
    rw [div_le_iff₀ hm1pos]
    have : CB * 8 ^ k / ε ≤ (m₁ : ℝ) - 1 := by linarith
    rw [div_le_iff₀ hε] at this
    linarith
  have hEbp : ENNReal.ofReal (CB' * ((2 : ℝ) ^ escJ n) ^ k *
      ((escJ n : ℝ) * 4 ^ escJ n) ^ (-(k : ℝ) / 2)) ≤ ENNReal.ofReal ε := by
    refine (ENNReal.ofReal_le_ofReal (errBp_le CB' hCB'.le k (escJ n) (by omega) hj1n)).trans
      (ENNReal.ofReal_le_ofReal ?_)
    rw [div_le_iff₀ hj0]
    have := hjB'ε
    rw [div_le_iff₀ hε] at this
    linarith
  have hEc : ENNReal.ofReal (CC * ((n : ℝ) ^ 17 / 7) ^ (-(1 : ℝ) / 30)) ≤ ENNReal.ofReal ε := by
    refine (ENNReal.ofReal_le_ofReal (errC_le CC hCC.le n (by omega))).trans
      (ENNReal.ofReal_le_ofReal ?_)
    have hsq : (CC / ε) ^ 2 ≤ n := by
      have h1 : ((CC / ε) ^ 2 : ℝ) ≤ (NC : ℝ) := by
        have := Nat.le_ceil ((CC / ε) ^ 2)
        rw [hNC]; push_cast; linarith
      exact h1.trans (by exact_mod_cast hnNC)
    have hroot : CC / ε ≤ (n : ℝ) ^ (1 / 2 : ℝ) := by
      rw [← Real.sqrt_eq_rpow]
      exact Real.le_sqrt_of_sq_le hsq
    have hpos : (0 : ℝ) < (n : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hn0 _
    rw [div_le_iff₀ hpos]
    rw [div_le_iff₀ hε] at hroot
    linarith
  have hEd : errD CD cD m₁ n ≤ ENNReal.ofReal ε := by
    have hM₂m : M₂ ≤ m₁ := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hm1ge
    have hM₃m : M₃ ≤ m₁ := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hm1ge
    have hcm : Real.log 16 + 1 ≤ cD * m₁ := by
      have h1 : (Real.log 16 + 1) / cD ≤ (M₂ : ℝ) := by
        have := Nat.le_ceil ((Real.log 16 + 1) / cD)
        rw [hM₂]; push_cast; linarith
      have h2 : (M₂ : ℝ) ≤ m₁ := by exact_mod_cast hM₂m
      rw [div_le_iff₀ hcD] at h1
      calc Real.log 16 + 1 ≤ (M₂ : ℝ) * cD := h1
        _ ≤ (m₁ : ℝ) * cD := mul_le_mul_of_nonneg_right h2 hcD.le
        _ = cD * m₁ := mul_comm _ _
    refine (errD_le CD cD hCD.le m₁ n hcm (by omega)).trans (ENNReal.ofReal_le_ofReal ?_)
    have h1 : 2 * CD / ε ≤ (M₃ : ℝ) := by
      have := Nat.le_ceil (2 * CD / ε)
      rw [hM₃]; push_cast; linarith
    have h2 : (M₃ : ℝ) ≤ m₁ := by exact_mod_cast hM₃m
    have hexp : Real.exp (-(m₁ : ℝ)) ≤ 1 / ((m₁ : ℝ) + 1) := by
      rw [Real.exp_neg, ← one_div]
      exact one_div_le_one_div_of_le (by positivity) (by
        have := Real.add_one_le_exp (m₁ : ℝ); linarith)
    have hm1p : (0 : ℝ) < (m₁ : ℝ) + 1 := by positivity
    calc CD * 2 * Real.exp (-(m₁ : ℝ)) ≤ CD * 2 * (1 / ((m₁ : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_left hexp (by positivity)
      _ = 2 * CD / ((m₁ : ℝ) + 1) := by ring
      _ ≤ ε := by
          rw [div_le_iff₀ hm1p]
          rw [div_le_iff₀ hε] at h1
          calc 2 * CD ≤ (M₃ : ℝ) * ε := h1
            _ ≤ ((m₁ : ℝ) + 1) * ε := mul_le_mul_of_nonneg_right (by linarith) hε.le
            _ = ε * ((m₁ : ℝ) + 1) := mul_comm _ _
  have herr : ENNReal.ofReal (cline (k + 2) / 2) ≤ ENNReal.ofReal (cline (k + 2)) -
      ENNReal.ofReal (Real.exp (-((avoidLevel ((escJ n : ℝ) * 4 ^ escJ n) : ℕ) : ℝ) ^ 2)) -
      errB CB k m₁ n -
      ENNReal.ofReal (CB' * ((2 : ℝ) ^ escJ n) ^ k *
        ((escJ n : ℝ) * 4 ^ escJ n) ^ (-(k : ℝ) / 2)) -
      ENNReal.ofReal (CC * ((n : ℝ) ^ 17 / 7) ^ (-(1 : ℝ) / 30)) - errD CD cD m₁ n := by
    by_cases hc0 : 0 < c
    · refine herr_of ?_
      have hεc : ε = c / 10 := by rw [hεdef, ite_eq_left hc0]
      calc _ ≤ ENNReal.ofReal ε + ENNReal.ofReal ε + ENNReal.ofReal ε + ENNReal.ofReal ε +
            ENNReal.ofReal ε := by gcongr
        _ = ENNReal.ofReal (c / 2) := by
            rw [← ENNReal.ofReal_add hε.le hε.le, ← ENNReal.ofReal_add (by positivity) hε.le,
              ← ENNReal.ofReal_add (by positivity) hε.le, ← ENNReal.ofReal_add (by positivity) hε.le]
            congr 1; rw [hεc]; ring
    · have : ENNReal.ofReal (cline (k + 2) / 2) = 0 :=
        ENNReal.ofReal_of_nonpos (by linarith [not_lt.1 hc0])
      rw [this]; exact bot_le
  exact ⟨hm8, hm₁n₀, hm1n, by linarith, h4, hβ2, hn2, hn53, hnD, hlb, hj1, hj1', (by omega),
    escIstar_le n (escJ n), escIstar_spec n (escJ n), hT1, hT2, hε1, hε2,
    fun m hm => theta_B m hm, theta_B' (escJ n) (by omega), hL1', hL2', hL3', herr⟩

end ElboimSly.Paper.Escape
