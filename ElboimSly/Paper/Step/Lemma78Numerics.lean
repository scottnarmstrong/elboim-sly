/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Step.Lemma78Excursion
public import ElboimSly.Paper.Step.Lemma78Num
public import ElboimSly.Paper.Heavy.ThrFinite
public import ElboimSly.Paper.Heavy.TauBad
public import Mathlib

/-!
# The numerics ("for `β` and `n` large")

One excursion succeeds with probability at least frac12 ("Sum"), bookkeeping of n_0; closing crefprop:ind-step. There are `N_n` and `B_β` such that for
`n ≥ N_n` and `β ≥ B_β` the conditions of `step78_excursion` hold and the bracket is `≤ 1/2`.
The terms are each `≤ 1/10`; the far term uses `(10/9)(1.9/√3.89)³ < 1`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Step

open ElboimSly ElboimSly.Paper ElboimSly.Paper.Heavy

variable {d : ℕ}

theorem step78_pow_level (_hd : 1 ≤ d) (n : ℕ) :
    ((19 / 10 : ℝ) ^ (4 * indDelta d)) ^ n / (19 / 10) ≤ (19 / 10 : ℝ) ^ heavyLevel d n := by
  have h1 := lt_heavyLevel_add_one d n
  have h2 : (19 / 10 : ℝ) ^ (4 * indDelta d * n - 1) ≤ (19 / 10 : ℝ) ^ (heavyLevel d n : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  rw [Real.rpow_natCast] at h2
  have h3 : (19 / 10 : ℝ) ^ (4 * indDelta d * n - 1) =
      ((19 / 10 : ℝ) ^ (4 * indDelta d)) ^ n / (19 / 10) := by
    rw [Real.rpow_sub (by norm_num), Real.rpow_one, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  rwa [h3] at h2

theorem step78_indScale_le (t₀ : ℝ) (ht1 : 0 ≤ t₀) (ht : t₀ ≤ 4) (hδ : 0 ≤ indDelta d) (n : ℕ) :
    indScale t₀ n ^ indDelta d ≤ (4 : ℝ) ^ indDelta d * ((4 : ℝ) ^ indDelta d) ^ n := by
  unfold indScale
  calc ((4 : ℝ) ^ n * t₀) ^ indDelta d ≤ ((4 : ℝ) ^ n * 4) ^ indDelta d :=
        Real.rpow_le_rpow (by positivity) (by gcongr) hδ
    _ = ((4 : ℝ) ^ n) ^ indDelta d * (4 : ℝ) ^ indDelta d :=
        Real.mul_rpow (by positivity) (by norm_num)
    _ = _ := by rw [pow4_rpow, mul_comm (n : ℝ), rpow4_nat, mul_comm]

/-- `ρ_k - 1` is eventually larger than any constant and than `t_n^δ`. -/
theorem step78_rho_growth (hd : 5 ≤ d) (M : ℝ) :
    ∀ᶠ n in atTop, ∀ t₀ : ℝ, 1 < t₀ → t₀ ≤ 4 →
      M ≤ step78Rho d n - 1 ∧ indScale t₀ n ^ indDelta d ≤ step78Rho d n - 1 := by
  have hδ : 0 < indDelta d := heavy_indDelta_pos (by omega)
  set b1 : ℝ := (19 / 10 : ℝ) ^ (4 * indDelta d) with hb1
  set b2 : ℝ := (4 : ℝ) ^ indDelta d with hb2
  have hb2' : 1 < b2 := Real.one_lt_rpow (by norm_num) hδ
  have h4 : (4 : ℝ) < (19 / 10 : ℝ) ^ (4 : ℝ) := by
    have : (19 / 10 : ℝ) ^ (4 : ℝ) = (19 / 10 : ℝ) ^ (4 : ℕ) := by
      exact_mod_cast Real.rpow_natCast (19 / 10 : ℝ) 4
    rw [this]; norm_num
  have hb12 : b2 < b1 := by
    have : (4 : ℝ) ^ indDelta d < ((19 / 10 : ℝ) ^ (4 : ℝ)) ^ indDelta d :=
      Real.rpow_lt_rpow (by norm_num) h4 hδ
    rwa [← Real.rpow_mul (by norm_num)] at this
  have hq : 1 < b1 / b2 := by rw [lt_div_iff₀ (by linarith)]; linarith
  set M' : ℝ := max M 0 with hM'
  obtain ⟨N, hN⟩ := eventually_mul_pow_le (3.8 * (M' + 1 + (4 : ℝ) ^ indDelta d)) 0 hq
  filter_upwards [eventually_ge_atTop N] with n hn t₀ ht1 ht4
  have hn' := hN n hn
  simp only [pow_zero, mul_one] at hn'
  have hbn : 1 ≤ b2 ^ n := one_le_pow₀ hb2'.le
  have hb1n : b1 ^ n = (b1 / b2) ^ n * b2 ^ n := by
    rw [← mul_pow]; field_simp
  have hlev := step78_pow_level (d := d) (by omega) n
  have hsc := step78_indScale_le (d := d) t₀ (by linarith) ht4 hδ.le n
  have hM0 : 0 ≤ M' := le_max_right _ _
  have hMM : M ≤ M' := le_max_left _ _
  have h4d : (0 : ℝ) < (4 : ℝ) ^ indDelta d := by positivity
  have hbig : 3.8 * (M' + 1 + (4 : ℝ) ^ indDelta d) * b2 ^ n ≤ b1 ^ n := by
    rw [hb1n]; exact mul_le_mul_of_nonneg_right hn' (by positivity)
  have hk : (19 / 10 : ℝ) ^ heavyLevel d n / 2 - 1 ≥ b1 ^ n / 3.8 - 1 := by
    have : b1 ^ n / (19 / 10) / 2 ≤ (19 / 10 : ℝ) ^ heavyLevel d n / 2 := by
      linarith [hlev]
    have e : b1 ^ n / (19 / 10) / 2 = b1 ^ n / 3.8 := by ring
    linarith
  unfold step78Rho
  constructor
  · have : M' + 1 ≤ b1 ^ n / 3.8 := by
      rw [le_div_iff₀ (by norm_num)]
      nlinarith [mul_le_mul_of_nonneg_left hbn (by positivity : (0 : ℝ) ≤ 3.8 * (M' + 1)),
        mul_nonneg (by positivity : (0 : ℝ) ≤ 3.8 * (4 : ℝ) ^ indDelta d) (by positivity : (0 : ℝ) ≤ b2 ^ n)]
    linarith
  · have : 4 ^ indDelta d * b2 ^ n + 1 ≤ b1 ^ n / 3.8 := by
      rw [le_div_iff₀ (by norm_num)]
      nlinarith [mul_le_mul_of_nonneg_left hbn (by positivity : (0 : ℝ) ≤ 3.8 * (M' + 1)),
        mul_nonneg (by positivity : (0 : ℝ) ≤ 3.8 * M') (by positivity : (0 : ℝ) ≤ b2 ^ n)]
    linarith

theorem step78_rho_le (hd : 1 ≤ d) (n : ℕ) : step78Rho d n - 1 ≤ (4 : ℝ) ^ n := by
  unfold step78Rho
  have h1 : (19 / 10 : ℝ) ^ heavyLevel d n ≤ (19 / 10 : ℝ) ^ n :=
    pow_le_pow_right₀ (by norm_num) (heavyLevel_le_self hd n)
  have h2 : (19 / 10 : ℝ) ^ n ≤ (4 : ℝ) ^ n := pow_le_pow_left₀ (by norm_num) (by norm_num) n
  have h3 : (0 : ℝ) ≤ (19 / 10 : ℝ) ^ heavyLevel d n := by positivity
  linarith

theorem step78_scaleReduced_lt {t₀ : ℝ} (_ht1 : 1 < t₀) (ht4 : t₀ ≤ 4) {n : ℕ} (hn : 3 ≤ n) :
    indScaleReduced t₀ n < (4 : ℝ) ^ n := by
  unfold indScaleReduced indScale
  have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have h4 : (4 : ℝ) < (n : ℝ) ^ 4 := by nlinarith [pow_le_pow_left₀ (by norm_num) hn3 4]
  rw [div_lt_iff₀ (by positivity)]
  have hp : (0 : ℝ) < (4 : ℝ) ^ n := by positivity
  nlinarith

theorem step78_exp_le {n : ℕ} (hn : 4 ≤ n) :
    Real.exp (-(((n - 1 : ℕ) : ℝ) ^ 2)) ≤ 1 / 10 := by
  have h1 : (3 : ℝ) ≤ ((n - 1 : ℕ) : ℝ) := by
    have : 3 ≤ n - 1 := by omega
    exact_mod_cast this
  have h2 : (9 : ℝ) ≤ ((n - 1 : ℕ) : ℝ) ^ 2 := by nlinarith
  have h3 : Real.exp (-(((n - 1 : ℕ) : ℝ) ^ 2)) ≤ Real.exp (-9) := Real.exp_le_exp.2 (by linarith)
  have h4 : (10 : ℝ) ≤ Real.exp 9 := by linarith [Real.add_one_le_exp (9 : ℝ)]
  have h5 : Real.exp (-9) = (Real.exp 9)⁻¹ := Real.exp_neg 9
  rw [h5] at h3
  have h6 : (Real.exp 9)⁻¹ ≤ 1 / 10 := by
    rw [one_div]; exact inv_anti₀ (by norm_num) h4
  linarith

theorem sqrt_pow_eq (x : ℝ) (hx : 0 ≤ x) (n : ℕ) : Real.sqrt (x ^ n) = Real.sqrt x ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, Real.sqrt_mul (by positivity), ih, pow_succ]

/-- `(10/9)(1.9/√3.89)³ < 1`. -/
theorem step78_far_ratio :
    (10 / 9 : ℝ) * ((19 / 10 : ℝ) / Real.sqrt (389 / 100)) ^ 3 < 1 := by
  set a : ℝ := (19 / 10 : ℝ) / Real.sqrt (389 / 100) with ha
  have hs : Real.sqrt (389 / 100) ^ 2 = 389 / 100 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 < Real.sqrt (389 / 100) := Real.sqrt_pos.2 (by norm_num)
  have ha0 : 0 ≤ a := by positivity
  have ha2 : a ^ 2 = 361 / 389 := by
    rw [ha, div_pow, hs]; norm_num
  have ha6 : (a ^ 3) ^ 2 = (361 / 389 : ℝ) ^ 3 := by
    rw [← pow_mul, show 3 * 2 = 2 * 3 by rfl, pow_mul, ha2]
  have h : a ^ 3 < 9 / 10 := by
    by_contra hge
    rw [not_lt] at hge
    have : (9 / 10 : ℝ) ^ 2 ≤ (a ^ 3) ^ 2 := pow_le_pow_left₀ (by norm_num) hge 2
    rw [ha6] at this
    norm_num at this
  linarith

/-- The far term is eventually `≤ 1/10`. -/
theorem step78_far_term (hd : 5 ≤ d) :
    ∀ᶠ n in atTop, 2 * (10 / 9 : ℝ) ^ n * (ElboimSly.Brownian.Cfar d *
      (3 * (19 / 10 : ℝ) ^ n / Real.sqrt ((389 / 100 : ℝ) ^ n)) ^ (d - 2)) ≤ 1 / 10 := by
  set a : ℝ := (19 / 10 : ℝ) / Real.sqrt (389 / 100) with ha
  have hs0 : 0 < Real.sqrt (389 / 100) := Real.sqrt_pos.2 (by norm_num)
  have hs : Real.sqrt (389 / 100) ^ 2 = 389 / 100 := Real.sq_sqrt (by norm_num)
  have ha0 : 0 ≤ a := by positivity
  have ha1 : a ≤ 1 := by
    rw [ha, div_le_one hs0]
    nlinarith
  set r : ℝ := (10 / 9 : ℝ) * a ^ 3 with hr
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r < 1 := step78_far_ratio
  set K : ℝ := 2 * (ElboimSly.Brownian.Cfar d * 3 ^ (d - 2)) with hK
  have hCf := ElboimSly.Brownian.Cfar_pos d
  have hT := (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).const_mul K
  rw [mul_zero] at hT
  filter_upwards [(tendsto_order.1 hT).2 (1 / 10) (by norm_num)] with n hn
  refine le_trans ?_ hn.le
  · have e : 3 * (19 / 10 : ℝ) ^ n / Real.sqrt ((389 / 100 : ℝ) ^ n) = 3 * a ^ n := by
      rw [sqrt_pow_eq _ (by norm_num), mul_div_assoc, ha, ← div_pow]
    rw [e, mul_pow, ← pow_mul]
    have hd2 : 3 ≤ d - 2 := by omega
    have hpow : a ^ (n * (d - 2)) ≤ a ^ (n * 3) :=
      pow_le_pow_of_le_one ha0 ha1 (Nat.mul_le_mul_left n hd2)
    have e2 : K * r ^ n = 2 * (10 / 9 : ℝ) ^ n * (ElboimSly.Brownian.Cfar d * (3 ^ (d - 2) *
        a ^ (n * 3))) := by
      rw [hK, hr, mul_pow, ← pow_mul, mul_comm 3 n]; ring
    rw [e2]
    gcongr

theorem step78_C42_term {C42 L : ℝ} (hC : 0 < C42) (hL : (10 * C42) ^ 30 ≤ L) :
    C42 * L ^ (-(1 : ℝ) / 30) ≤ 1 / 10 := by
  have h10 : 0 < (10 * C42) ^ 30 := by positivity
  have h1 : L ^ (-(1 : ℝ) / 30) ≤ ((10 * C42) ^ 30) ^ (-(1 : ℝ) / 30) :=
    Real.rpow_le_rpow_of_nonpos h10 hL (by norm_num)
  have h2 : ((10 * C42) ^ 30) ^ (-(1 : ℝ) / 30) = (10 * C42)⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    have : ((30 : ℕ) : ℝ) * (-(1 : ℝ) / 30) = -1 := by norm_num
    rw [this, Real.rpow_neg_one]
  calc C42 * L ^ (-(1 : ℝ) / 30) ≤ C42 * (10 * C42)⁻¹ :=
        mul_le_mul_of_nonneg_left (h1.trans h2.le) hC.le
    _ = 1 / 10 := by field_simp

/-- **Numerics of one excursion succeeds with probability at least frac12**: for `n` and `β` large, the conditions of
`step78_excursion` hold and the bracket is at most `1/2`. -/
theorem step78_numerics (hd : 5 ≤ d) {Cτ C42 : ℝ} (_hCτ : 0 < Cτ) (hC42 : 0 < C42) (n₁ : ℕ) :
    ∃ Nn : ℕ, ∃ Bβ : ℝ, 0 < Bβ ∧ ∀ n ≥ Nn, ∀ t₀ : ℝ, 1 < t₀ → t₀ ≤ 4 → ∀ β : ℝ, Bβ ≤ β →
      HeavyT d n₁ step78E0 n ∧ 4 ≤ n ∧ (4 : ℝ) ^ (n₁ + 1) ≤ step78Rho d n - 1 ∧
      step78Rho d n - 1 ≤ (4 : ℝ) ^ n ∧ indScale t₀ n ^ indDelta d ≤ step78Rho d n - 1 ∧
      (6 * 3 ^ d : ℝ) ^ 6 ≤ step78Rho d n - 1 ∧ indScaleReduced t₀ n < (4 : ℝ) ^ n ∧
      step78Bracket d Cτ C42 β n (step78Rho d n - 1) ≤ 1 / 2 := by
  have hδ : 0 < indDelta d := heavy_indDelta_pos (by omega)
  have hT1 : Tendsto (fun β : ℝ => Cτ * β ^ (-(indDelta d / 30))) atTop (𝓝 0) := by
    simpa using (tendsto_rpow_neg_atTop (by positivity : 0 < indDelta d / 30)).const_mul Cτ
  obtain ⟨B1, hB1⟩ := eventually_atTop.1 ((tendsto_order.1 hT1).2 (1 / 10) (by norm_num))
  set M : ℝ := max (max ((4 : ℝ) ^ (n₁ + 1)) ((6 * 3 ^ d : ℝ) ^ 6)) ((10 * C42) ^ 30) with hM
  have hev : ∀ᶠ n in atTop, heavyN6 d n₁ step78E0 ≤ n ∧ 4 ≤ n ∧
      (∀ t₀ : ℝ, 1 < t₀ → t₀ ≤ 4 → M ≤ step78Rho d n - 1 ∧
        indScale t₀ n ^ indDelta d ≤ step78Rho d n - 1) ∧
      2 * (10 / 9 : ℝ) ^ n * (ElboimSly.Brownian.Cfar d *
        (3 * (19 / 10 : ℝ) ^ n / Real.sqrt ((389 / 100 : ℝ) ^ n)) ^ (d - 2)) ≤ 1 / 10 :=
    (eventually_ge_atTop _).and ((eventually_ge_atTop 4).and
      ((step78_rho_growth hd M).and (step78_far_term hd)))
  obtain ⟨Nn, hNn⟩ := eventually_atTop.1 hev
  refine ⟨Nn, max B1 5, lt_of_lt_of_le (by norm_num) (le_max_right _ _), ?_⟩
  intro n hn t₀ ht1 ht4 β hβ
  obtain ⟨h6, h4, hgrow, hfar⟩ := hNn n hn
  obtain ⟨hMn, hsc⟩ := hgrow t₀ ht1 ht4
  have hβ1 : B1 ≤ β := (le_max_left _ _).trans hβ
  have hβ5 : (5 : ℝ) ≤ β := (le_max_right _ _).trans hβ
  have hLn : step78Rho d n - 1 ≥ (10 * C42) ^ 30 := (le_max_right _ _).trans hMn
  refine ⟨HeavyT.of_ge_N6 (by omega) h6, h4, ((le_max_left _ _).trans (le_max_left _ _)).trans hMn,
    step78_rho_le (by omega) n, hsc,
    ((le_max_right _ _).trans (le_max_left _ _)).trans hMn,
    step78_scaleReduced_lt ht1 ht4 (by omega), ?_⟩
  unfold step78Bracket step78BracketS
  have e1 : Cτ * β ^ (-indDelta d / 30) ≤ 1 / 10 := by
    have := hB1 β hβ1
    rw [neg_div]; exact this.le
  have e2 : 2 * (β ^ 2)⁻¹ ≤ 1 / 10 := by
    have h25 : (25 : ℝ) ≤ β ^ 2 := by nlinarith
    have : (β ^ 2)⁻¹ ≤ (25 : ℝ)⁻¹ := inv_anti₀ (by norm_num) h25
    linarith
  have e3 := step78_C42_term hC42 hLn
  have e4 := step78_exp_le h4
  linarith

end ElboimSly.Paper.Step

end
