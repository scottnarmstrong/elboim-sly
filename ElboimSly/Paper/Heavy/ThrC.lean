/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Heavy.ThrB

/-!
# The thresholds are finite, part C: (T7), (T8)

The thresholds are finite.  Both are the case `p = 2`, `p = 3` of `ev_T78`.
-/

@[expose] public section

open Filter Topology

namespace ElboimSly.Paper.Heavy

open ElboimSly ElboimSly.Paper

variable {d : ℕ}

theorem two_pow_le_exp (m : ℕ) : (2 : ℝ) ^ m ≤ Real.exp m := by
  rw [← mul_one (m : ℝ), Real.exp_nat_mul]
  exact pow_le_pow_left₀ (by norm_num) (by linarith [Real.add_one_le_exp (1 : ℝ)]) m

theorem pow_le_exp_nat {a : ℝ} (ha : 0 ≤ a) (c : ℝ) (hac : a ≤ Real.exp c) (m : ℕ) :
    a ^ m ≤ Real.exp (m * c) := by
  rw [Real.exp_nat_mul]
  exact pow_le_pow_left₀ ha hac m

/-- The size of the prefactor in (T7)/(T8): at most `e^{C n + C'}`. -/
theorem prefactor_le (hd : 1 ≤ d) (n : ℕ) :
    (9 * 2 ^ heavyLevel d n : ℝ) ^ (2 * d) * (4 ^ (n + 1) + 1) ^ 2 ≤
      Real.exp ((8 * d * indDelta d + 6) * n + (18 * d + 12)) := by
  have hδ := heavy_indDelta_pos hd
  have hle := heavyLevel_le hd n
  have h9 : (9 * 2 ^ heavyLevel d n : ℝ) ≤ Real.exp (9 + heavyLevel d n) := by
    rw [Real.exp_add]
    have : (9 : ℝ) ≤ Real.exp 9 := by linarith [Real.add_one_le_exp (9 : ℝ)]
    exact mul_le_mul this (two_pow_le_exp _) (by positivity) (by positivity)
  have h4 : ((4 : ℝ) ^ (n + 1) + 1) ≤ Real.exp (((n + 2 : ℕ) : ℝ) * 3) := by
    rw [Real.exp_nat_mul]
    have h3 : (4 : ℝ) ≤ Real.exp 3 := by linarith [Real.add_one_le_exp (3 : ℝ)]
    calc (4 : ℝ) ^ (n + 1) + 1 ≤ 4 ^ (n + 2) := by
          have : (1 : ℝ) ≤ 4 ^ (n + 1) := one_le_pow₀ (by norm_num)
          rw [pow_succ _ (n + 1)]; linarith
      _ ≤ _ := pow_le_pow_left₀ (by norm_num) h3 _
  have e1 := pow_le_exp_nat (by positivity) _ h9 (2 * d)
  have e2 := pow_le_exp_nat (by positivity) _ h4 2
  calc _ ≤ Real.exp (((2 * d : ℕ) : ℝ) * (9 + heavyLevel d n)) *
        Real.exp ((2 : ℕ) * (((n + 2 : ℕ) : ℝ) * 3)) := mul_le_mul e1 e2 (by positivity)
          (by positivity)
    _ ≤ _ := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.2
        push_cast
        have : (0 : ℝ) ≤ d := by positivity
        nlinarith

theorem assemble_exp {P br a L k : ℝ} (hP : P ≤ Real.exp a) (hbr : br ≤ Real.exp L * Real.exp (-k))
    (hbr0 : 0 ≤ br) : P * br ≤ Real.exp (a + L + -k) := by
  rw [Real.exp_add, Real.exp_add, mul_assoc]
  exact mul_le_mul hP hbr hbr0 (Real.exp_pos _).le

theorem core_exp_ineq {C C' L Q δ n x κ : ℝ} {p : ℕ} (hp2 : 2 ≤ p) (hδ : 0 < δ) (hC0 : 0 ≤ C)
    (hCL : 0 ≤ C' + L) (hQdef : Q = C / δ + C' + L) (hx : x = δ * n) (hx1 : 1 ≤ x)
    (hQx : Q ≤ 5 / 4 * x) (hκx : 3 / 2 * x ≤ κ) : C * n + C' + L + -κ ^ p ≤ -(x ^ p) := by
  have hx2p : x ^ 2 ≤ x ^ p := pow_le_pow_right₀ hx1 hp2
  have hκpow : 9 / 4 * x ^ p ≤ κ ^ p := by
    calc 9 / 4 * x ^ p ≤ (3 / 2) ^ p * x ^ p := by
          gcongr
          calc (9 / 4 : ℝ) = (3 / 2) ^ 2 := by norm_num
            _ ≤ _ := pow_le_pow_right₀ (by norm_num) hp2
      _ = (3 / 2 * x) ^ p := (mul_pow _ _ _).symm
      _ ≤ κ ^ p := pow_le_pow_left₀ (by positivity) hκx p
  have hCn : C * n = C / δ * x := by rw [hx]; field_simp
  have hC0' : 0 ≤ C / δ := by positivity
  have h1 : C * n + C' + L ≤ Q * x := by
    rw [hCn, hQdef]; nlinarith
  have h2 : Q * x ≤ 5 / 4 * x * x := by nlinarith
  nlinarith

theorem ev_T78 (hd : 1 ≤ d) (p : ℕ) (hp2 : 2 ≤ p) (hp4 : p ≤ 3) : ∀ᶠ n : ℕ in atTop,
    (9 * 2 ^ heavyLevel d n : ℝ) ^ (2 * d) * (4 ^ (n + 1) + 1) ^ 2 *
      (3 * Real.exp (-(heavyKappa d n) ^ p) +
        4 * d * Real.exp (-((heavyLevel d n : ℝ) ^ 4 / 3200))) ≤
        Real.exp (-(indDelta d ^ p * n ^ p)) ∧
    d * (n + 1) * Real.log 5 ≤ indDelta d ^ p * n ^ p / 2 := by
  have hδ := heavy_indDelta_pos hd
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  set C : ℝ := 8 * d * indDelta d + 6 with hC
  set C' : ℝ := 18 * d + 12 with hC'
  set L : ℝ := Real.log (3 + 4 * d) with hL
  have hL0 : 0 ≤ L := Real.log_nonneg (by linarith)
  set Q : ℝ := C / indDelta d + C' + L with hQdef
  have hl5 : 0 ≤ Real.log 5 := Real.log_nonneg (by norm_num)
  have hk := (tendsto_heavyLevel hd).eventually (eventually_ge_atTop (3200 : ℝ))
  filter_upwards [hk, ev_kappa_ge hd, ev_lin_ge (by positivity : 0 < 5 / 4 * indDelta d) Q,
    ev_lin_ge hδ 1, ev_lin_ge hδ (4 * d * Real.log 5 / indDelta d + 1), eventually_ge_atTop 1]
    with n hk hκ hQ hx1 hx2 hn1
  have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  set kk : ℝ := (heavyLevel d n : ℝ) with hkk
  set κ := heavyKappa d n with hκdef
  set x : ℝ := indDelta d * n with hx
  have hκ0 : 0 ≤ κ := by
    have : 0 ≤ 3 / 2 * indDelta d * (n : ℝ) := by positivity
    linarith
  have hκk : κ ≤ kk := by
    rw [hκdef]; unfold heavyKappa
    have := Real.logb_nonneg (b := 2) (by norm_num) (by linarith : (1 : ℝ) ≤ kk)
    linarith
  have hkp : kk ^ p ≤ kk ^ 4 / 3200 := by
    have h1 : kk ^ 4 = kk ^ p * kk ^ (4 - p) := by rw [← pow_add, Nat.add_sub_cancel' (by omega : p ≤ 4)]
    have h2 : (3200 : ℝ) ≤ kk ^ (4 - p) := by
      calc (3200 : ℝ) ≤ kk := hk
        _ = kk ^ 1 := (pow_one _).symm
        _ ≤ kk ^ (4 - p) := pow_le_pow_right₀ (by linarith) (by omega)
    have h3 : 0 ≤ kk ^ p := by positivity
    rw [le_div_iff₀ (by norm_num), h1]
    nlinarith
  have hκp : κ ^ p ≤ kk ^ p := pow_le_pow_left₀ hκ0 hκk p
  have hx1' : 1 ≤ x := by linarith
  have hx2p : x ^ 2 ≤ x ^ p := pow_le_pow_right₀ hx1' hp2
  have hκx : 3 / 2 * x ≤ κ := by
    have : 3 / 2 * x = 3 / 2 * indDelta d * n := by rw [hx]; ring
    linarith
  have hQx : Q ≤ 5 / 4 * x := by
    have : 5 / 4 * x = 5 / 4 * indDelta d * n := by rw [hx]; ring
    linarith
  have hdn : indDelta d ^ p * (n : ℝ) ^ p = x ^ p := by rw [hx, mul_pow]
  rw [hdn]
  constructor
  · have hP := prefactor_le hd n
    have h2 : Real.exp L = 3 + 4 * d := Real.exp_log (by linarith)
    have hbr : 3 * Real.exp (-κ ^ p) + 4 * d * Real.exp (-(kk ^ 4 / 3200)) ≤
        Real.exp L * Real.exp (-κ ^ p) := by
      have h1 : Real.exp (-(kk ^ 4 / 3200)) ≤ Real.exp (-κ ^ p) :=
        Real.exp_le_exp.2 (by linarith)
      rw [h2]
      have := Real.exp_pos (-κ ^ p)
      nlinarith
    have hbr0 : 0 ≤ 3 * Real.exp (-κ ^ p) + 4 * d * Real.exp (-(kk ^ 4 / 3200)) := by positivity
    refine (assemble_exp hP hbr hbr0).trans (Real.exp_le_exp.2 ?_)
    exact core_exp_ineq hp2 hδ (by positivity) (by positivity) hQdef hx hx1' hQx hκx
  · calc (d : ℝ) * (n + 1) * Real.log 5 ≤ 2 * d * n * Real.log 5 := by
          have : (0 : ℝ) ≤ d * Real.log 5 := by positivity
          nlinarith
      _ = (2 * d * Real.log 5 / indDelta d) * x := by rw [hx]; field_simp
      _ ≤ x / 2 * x := by
          apply mul_le_mul_of_nonneg_right _ (by linarith)
          have : 4 * d * Real.log 5 / indDelta d ≤ x := by linarith
          have e : 2 * (d : ℝ) * Real.log 5 / indDelta d = 4 * d * Real.log 5 / indDelta d / 2 := by
            ring
          linarith
      _ ≤ x ^ p / 2 := by nlinarith

theorem ev_T7 (hd : 1 ≤ d) : ∀ᶠ n : ℕ in atTop,
    (9 * 2 ^ heavyLevel d n : ℝ) ^ (2 * d) * (4 ^ (n + 1) + 1) ^ 2 *
      (3 * Real.exp (-(heavyKappa d n) ^ 2) +
        4 * d * Real.exp (-((heavyLevel d n : ℝ) ^ 4 / 3200))) ≤
        Real.exp (-(indDelta d ^ 2 * n ^ 2)) ∧
    d * (n + 1) * Real.log 5 ≤ indDelta d ^ 2 * n ^ 2 / 2 := ev_T78 hd 2 le_rfl (by norm_num)

theorem ev_T8 (hd : 1 ≤ d) : ∀ᶠ n : ℕ in atTop,
    (9 * 2 ^ heavyLevel d n : ℝ) ^ (2 * d) * (4 ^ (n + 1) + 1) ^ 2 *
      (3 * Real.exp (-(heavyKappa d n) ^ 3) +
        4 * d * Real.exp (-((heavyLevel d n : ℝ) ^ 4 / 3200))) ≤
        Real.exp (-(indDelta d ^ 3 * n ^ 3)) ∧
    d * (n + 1) * Real.log 5 ≤ indDelta d ^ 3 * n ^ 3 / 2 :=
  ev_T78 hd 3 (by norm_num) (by norm_num)

end ElboimSly.Paper.Heavy
