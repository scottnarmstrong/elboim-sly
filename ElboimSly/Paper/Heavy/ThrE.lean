/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Heavy.ThrD

/-!
# The thresholds are finite, part E: (T11) and the lemma

The thresholds are finite.

* `ev_T11`: (T11) holds eventually.
* `heavyT_eventually`: all of (T1)-(T11) hold eventually.
* `thresholds_finite`: the thresholds are finite; `heavyN6` is attained and `HeavyT` holds for
  every `n ≥ N₆`.
-/

@[expose] public section

open Filter Topology

namespace ElboimSly.Paper.Heavy

open ElboimSly ElboimSly.Paper

variable {d n₀ : ℕ} {E : HeavyEscConsts}

theorem heavyc_pos (hd : 1 ≤ d) : 0 < heavyc d E := by
  have hδ := heavy_indDelta_pos hd
  unfold heavyc
  have := E.c5_pos
  refine lt_min (lt_min this (by norm_num)) (lt_min (by positivity) (by positivity))

theorem heavyc_le : heavyc d E ≤ 1 / 17 :=
  (min_le_left _ _).trans (min_le_right _ _)

theorem heavyCJ_pos : 0 < heavyCJ d := by unfold heavyCJ; positivity

theorem heavyA_le (n : ℕ) :
    heavyA d n ≤ (4 * heavyCJ d + 3) * Real.exp ((5 * d + 16) * (n + 1)) := by
  have hE1 : (1 : ℝ) ≤ Real.exp ((5 * d + 16) * (n + 1)) := Real.one_le_exp (by positivity)
  have h16 : (16 : ℝ) ^ (n + 1) ≤ Real.exp ((5 * d + 16) * (n + 1)) := by
    have : (16 : ℝ) ≤ Real.exp 16 := by linarith [Real.add_one_le_exp (16 : ℝ)]
    calc (16 : ℝ) ^ (n + 1) ≤ Real.exp 16 ^ (n + 1) := pow_le_pow_left₀ (by norm_num) this _
      _ = Real.exp (((n + 1 : ℕ) : ℝ) * 16) := (Real.exp_nat_mul _ _).symm
      _ ≤ _ := Real.exp_le_exp.2 (by push_cast; nlinarith [(by positivity : (0 : ℝ) ≤ d)])
  have h5 : (5 : ℝ) ^ (d * (n + 1)) ≤ Real.exp (5 * d * (n + 1)) := by
    have : (5 : ℝ) ≤ Real.exp 5 := by linarith [Real.add_one_le_exp (5 : ℝ)]
    calc (5 : ℝ) ^ (d * (n + 1)) ≤ Real.exp 5 ^ (d * (n + 1)) :=
          pow_le_pow_left₀ (by norm_num) this _
      _ = Real.exp (((d * (n + 1) : ℕ) : ℝ) * 5) := (Real.exp_nat_mul _ _).symm
      _ = _ := by push_cast; ring_nf
  have hn1 : ((n : ℝ) + 1) ≤ Real.exp ((n + 1 : ℝ)) := by linarith [Real.add_one_le_exp ((n : ℝ) + 1)]
  have hmid : 2 * ((n : ℝ) + 1) * 5 ^ (d * (n + 1)) ≤ 2 * Real.exp ((5 * d + 16) * (n + 1)) := by
    have e : Real.exp ((n + 1 : ℝ)) * Real.exp (5 * d * (n + 1)) ≤
        Real.exp ((5 * d + 16) * (n + 1)) := by
      rw [← Real.exp_add]; apply Real.exp_le_exp.2; nlinarith [(by positivity : (0 : ℝ) ≤ d)]
    have : ((n : ℝ) + 1) * 5 ^ (d * (n + 1)) ≤ Real.exp ((n + 1 : ℝ)) * Real.exp (5 * d * (n + 1)) :=
      mul_le_mul hn1 h5 (by positivity) (by positivity)
    linarith
  unfold heavyA
  have hCJ := heavyCJ_pos (d := d)
  have : 4 * heavyCJ d * 16 ^ (n + 1) ≤ 4 * heavyCJ d * Real.exp ((5 * d + 16) * (n + 1)) := by
    gcongr
  nlinarith

theorem ev_T11 (hd : 1 ≤ d) : ∀ᶠ n : ℕ in atTop,
    Real.exp (-(n : ℝ) ^ 3) + ((n : ℝ) ^ 3 + 1) * heavyA d n *
      Real.exp (-(heavyc d E * n ^ 3)) ≤ Real.exp (-(heavyC6 d E * n ^ 3)) := by
  have hc := heavyc_pos (E := E) hd
  have hc17 := heavyc_le (d := d) (E := E)
  have hCJ := heavyCJ_pos (d := d)
  set c := heavyc d E with hcdef
  set G : ℝ := 4 * heavyCJ d + 3 with hG
  have hG1 : 1 ≤ G := by rw [hG]; linarith
  have hLg : 0 ≤ Real.log G := Real.log_nonneg hG1
  have hl2 : Real.log 2 ≤ 1 := by
    have := Real.log_two_lt_d9; linarith
  set F : ℝ := 5 * d + 17 with hF
  set F' : ℝ := Real.log G + 5 * d + 16 + Real.log 2 with hF'
  have hF0 : 0 ≤ F := by positivity
  have hF'0 : 0 ≤ F' := by
    have : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    positivity
  filter_upwards [ev_rpow_le_exp 3 1 one_pos 2, ev_lin_ge (by positivity : 0 < c / 2) (F + F'),
    eventually_ge_atTop 2] with n h3 hlin hn2
  have hn1' : (2 : ℝ) ≤ n := by exact_mod_cast hn2
  have hn3 : (n : ℝ) ^ (3 : ℝ) = (n : ℝ) ^ 3 := by
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [hn3] at h3
  have hn3p : (8 : ℝ) ≤ (n : ℝ) ^ 3 := by
    calc (8 : ℝ) = 2 ^ 3 := by norm_num
      _ ≤ _ := pow_le_pow_left₀ (by norm_num) hn1' 3
  have hc6 : heavyC6 d E = c / 2 := rfl
  rw [hc6]
  have hA := heavyA_le (d := d) n
  -- second term
  have hsecond : ((n : ℝ) ^ 3 + 1) * heavyA d n * Real.exp (-(c * n ^ 3)) ≤
      1 / 2 * Real.exp (-(c / 2 * n ^ 3)) := by
    have h1 : ((n : ℝ) ^ 3 + 1) ≤ Real.exp (1 * n) := by nlinarith
    have hA0 : 0 ≤ heavyA d n := by
      unfold heavyA; have := heavyCJ_pos (d := d); positivity
    have h2 : ((n : ℝ) ^ 3 + 1) * heavyA d n ≤ Real.exp (1 * n) *
        (G * Real.exp ((5 * d + 16) * (n + 1))) :=
      mul_le_mul h1 hA hA0 (Real.exp_pos _).le
    have hGexp : G = Real.exp (Real.log G) := (Real.exp_log (by linarith)).symm
    have hhalf : (1 / 2 : ℝ) = Real.exp (-Real.log 2) := by
      rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num
    calc _ ≤ Real.exp (1 * n) * (G * Real.exp ((5 * d + 16) * (n + 1))) * Real.exp (-(c * n ^ 3)) :=
          mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
      _ = Real.exp (1 * n + Real.log G + (5 * d + 16) * (n + 1) + -(c * n ^ 3)) := by
          rw [Real.exp_add, Real.exp_add, Real.exp_add, ← hGexp]; ring
      _ ≤ Real.exp (-Real.log 2 + -(c / 2 * n ^ 3)) := by
          apply Real.exp_le_exp.2
          have hcn : (F + F') ≤ c / 2 * n := hlin
          have h2' : (F + F') * n ≤ c / 2 * n * n := by nlinarith
          have h3' : c / 2 * n * n ≤ c / 2 * (n : ℝ) ^ 3 := by
            have : (n : ℝ) * n ≤ (n : ℝ) ^ 3 := by nlinarith
            nlinarith
          have h4 : 1 * (n : ℝ) + Real.log G + (5 * d + 16) * (n + 1) + Real.log 2 ≤
              (F + F') * n := by rw [hF, hF']; nlinarith
          nlinarith
      _ = _ := by rw [Real.exp_add, ← hhalf]
  have hfirst : Real.exp (-(n : ℝ) ^ 3) ≤ 1 / 2 * Real.exp (-(c / 2 * n ^ 3)) := by
    have hhalf : (1 / 2 : ℝ) = Real.exp (-Real.log 2) := by
      rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num
    rw [hhalf, ← Real.exp_add]
    apply Real.exp_le_exp.2
    nlinarith
  have : Real.exp (-(c / 2 * (n : ℝ) ^ 3)) = 1 / 2 * Real.exp (-(c / 2 * n ^ 3)) +
      1 / 2 * Real.exp (-(c / 2 * n ^ 3)) := by ring
  linarith

end ElboimSly.Paper.Heavy
