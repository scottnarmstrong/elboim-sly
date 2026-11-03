/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib

/-!
# Schauder functions

Schauder functions and index sets; Properties of Schauder functions.

The clamp `clamp u = min (max u 0) 1`, the tent `tent u = max 0 (1 - |2u - 1|)`, the Schauder
function `schauder n k u = 2^{-n/2-1} * tent (2^n u - k)`, and the Haar index set
`HaarIdx = {*} ⊔ {(n,k) : k < 2^n}`, with the coefficient function `haarFun`.
-/

@[expose] public section

open scoped NNReal

namespace ElboimSly.Brownian

/-- Schauder functions and index sets. The clamp `min (max u 0) 1`. -/
noncomputable def clamp (u : ℝ) : ℝ := min (max u 0) 1

/-- Schauder functions and index sets. The tent `Λ(u) = max 0 (1 - |2u - 1|)`. -/
noncomputable def tent (u : ℝ) : ℝ := max 0 (1 - |2 * u - 1|)

/-- The amplitude `2^{-n/2-1}` of the `n`th level Schauder functions. -/
noncomputable def schauderAmp (n : ℕ) : ℝ := (1 / 2) * (Real.sqrt 2)⁻¹ ^ n

/-- Schauder functions and index sets. The Schauder function `S_{n,k}(u) = 2^{-n/2-1} Λ(2^n u - k)`. -/
noncomputable def schauder (n k : ℕ) (u : ℝ) : ℝ := schauderAmp n * tent ((2 : ℝ) ^ n * u - k)

/-- Schauder functions and index sets. The Haar index set `{*} ⊔ {(n,k) : n ∈ ℕ, k < 2^n}`,
with `none` the point `*`. -/
abbrev HaarIdx : Type := Option (Σ n : ℕ, Fin (2 ^ n))

/-- Schauder functions and index sets. The functions `a_*  = clamp` and `a_{(n,k)} = S_{n,k}`. -/
noncomputable def haarFun : HaarIdx → ℝ → ℝ
  | none => clamp
  | some ⟨n, k⟩ => schauder n k

/-! ### Clamp -/

lemma clamp_of_nonpos {u : ℝ} (h : u ≤ 0) : clamp u = 0 := by
  unfold clamp
  rw [max_eq_right h]
  exact min_eq_left zero_le_one

lemma clamp_of_one_le {u : ℝ} (h : 1 ≤ u) : clamp u = 1 := by
  unfold clamp
  rw [max_eq_left (by linarith)]
  exact min_eq_right h

lemma clamp_of_mem {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ 1) : clamp u = u := by
  unfold clamp
  rw [max_eq_left h0]
  exact min_eq_left h1

lemma continuous_clamp : Continuous clamp := by
  unfold clamp; fun_prop

lemma clamp_nonneg (u : ℝ) : 0 ≤ clamp u := by
  unfold clamp; exact le_min (le_max_right _ _) zero_le_one

lemma clamp_le_one (u : ℝ) : clamp u ≤ 1 := min_le_right _ _

lemma clamp_mono : Monotone clamp := by
  intro a b hab
  unfold clamp
  exact min_le_min_right _ (max_le_max hab le_rfl)

lemma min_clamp (a b : ℝ) : min (clamp a) (clamp b) = clamp (min a b) := by
  rcases le_total a b with h | h
  · rw [min_eq_left h, min_eq_left (clamp_mono h)]
  · rw [min_eq_right h, min_eq_right (clamp_mono h)]

/-! ### Tent -/

lemma tent_of_nonpos {u : ℝ} (h : u ≤ 0) : tent u = 0 := by
  unfold tent
  rw [abs_of_nonpos (by linarith)]
  apply max_eq_left; linarith

lemma tent_of_one_le {u : ℝ} (h : 1 ≤ u) : tent u = 0 := by
  unfold tent
  rw [abs_of_nonneg (by linarith)]
  apply max_eq_left; linarith

lemma tent_of_mem_left {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ 1 / 2) : tent u = 2 * u := by
  unfold tent
  rw [abs_of_nonpos (by linarith), max_eq_right (by linarith)]
  ring

lemma tent_of_mem_right {u : ℝ} (h0 : 1 / 2 ≤ u) (h1 : u ≤ 1) : tent u = 2 - 2 * u := by
  unfold tent
  rw [abs_of_nonneg (by linarith), max_eq_right (by linarith)]
  ring

lemma tent_half : tent (1 / 2) = 1 := by
  rw [tent_of_mem_left (by norm_num) le_rfl]; norm_num

lemma continuous_tent : Continuous tent := by
  unfold tent; fun_prop

lemma tent_nonneg (u : ℝ) : 0 ≤ tent u := le_max_left _ _

lemma tent_le_one (u : ℝ) : tent u ≤ 1 := by
  unfold tent
  apply max_le zero_le_one
  have := abs_nonneg (2 * u - 1)
  linarith

lemma tent_int (m : ℤ) : tent m = 0 := by
  rcases le_or_gt m 0 with h | h
  · exact tent_of_nonpos (by exact_mod_cast h)
  · exact tent_of_one_le (by exact_mod_cast h)

lemma lt_of_tent_ne_zero {u : ℝ} (h : tent u ≠ 0) : 0 < u ∧ u < 1 := by
  constructor
  · by_contra hu
    exact h (tent_of_nonpos (not_lt.mp hu))
  · by_contra hu
    exact h (tent_of_one_le (not_lt.mp hu))

/-- The tent is affine on an interval `[i t, (i + 1) t]` of length `t = 1/(2c)`. -/
lemma tent_midpoint_of_int (i : ℤ) (c : ℕ) (hc : 0 < c) :
    tent (i * ((2 * c : ℕ) : ℝ)⁻¹ + ((2 * c : ℕ) : ℝ)⁻¹ / 2) =
      (tent (i * ((2 * c : ℕ) : ℝ)⁻¹) + tent ((i + 1) * ((2 * c : ℕ) : ℝ)⁻¹)) / 2 := by
  have hq : (0 : ℝ) < ((2 * c : ℕ) : ℝ) := by positivity
  set t : ℝ := ((2 * c : ℕ) : ℝ)⁻¹ with ht
  have ht0 : 0 < t := inv_pos.mpr hq
  have hct : (c : ℝ) * t = 1 / 2 := by
    rw [ht]; push_cast; field_simp
  rcases lt_or_ge i 0 with h1 | h1
  · have : (i : ℝ) + 1 ≤ 0 := by exact_mod_cast (by omega : i + 1 ≤ 0)
    have e1 : (i : ℝ) * t + t / 2 ≤ 0 := by nlinarith
    have e2 : (i : ℝ) * t ≤ 0 := by nlinarith
    have e3 : ((i : ℝ) + 1) * t ≤ 0 := by nlinarith
    rw [tent_of_nonpos e1, tent_of_nonpos e2, tent_of_nonpos e3]; norm_num
  rcases lt_or_ge i c with h2 | h2
  · have a1 : (0 : ℝ) ≤ i := by exact_mod_cast h1
    have a2 : (i : ℝ) + 1 ≤ c := by exact_mod_cast (by omega : i + 1 ≤ (c : ℤ))
    have b0 : 0 ≤ (i : ℝ) * t := by positivity
    have b1 : ((i : ℝ) + 1) * t ≤ 1 / 2 := by nlinarith
    rw [tent_of_mem_left (by nlinarith) (by nlinarith), tent_of_mem_left b0 (by nlinarith),
      tent_of_mem_left (by nlinarith) b1]
    ring
  rcases lt_or_ge i (2 * c) with h3 | h3
  · have a1 : (c : ℝ) ≤ i := by exact_mod_cast h2
    have a2 : (i : ℝ) + 1 ≤ 2 * c := by exact_mod_cast (by omega : i + 1 ≤ 2 * (c : ℤ))
    have b0 : 1 / 2 ≤ (i : ℝ) * t := by nlinarith
    have b1 : ((i : ℝ) + 1) * t ≤ 1 := by nlinarith
    rw [tent_of_mem_right (by nlinarith) (by nlinarith), tent_of_mem_right b0 (by nlinarith),
      tent_of_mem_right (by nlinarith) b1]
    ring
  · have a1 : (2 * c : ℝ) ≤ i := by exact_mod_cast h3
    have b0 : 1 ≤ (i : ℝ) * t := by nlinarith
    rw [tent_of_one_le (by nlinarith), tent_of_one_le b0, tent_of_one_le (by nlinarith)]
    norm_num

/-! ### Schauder functions -/

lemma schauderAmp_pos (n : ℕ) : 0 < schauderAmp n := by
  unfold schauderAmp; positivity

lemma schauderAmp_sq (n : ℕ) : schauderAmp n ^ 2 = (4 * (2 : ℝ) ^ n)⁻¹ := by
  unfold schauderAmp
  have h2 : ((Real.sqrt 2)⁻¹) ^ 2 = 1 / 2 := by
    rw [inv_pow, Real.sq_sqrt (by norm_num)]; norm_num
  have h4 : ((1 : ℝ) / 2) ^ n = ((2 : ℝ) ^ n)⁻¹ := by rw [one_div, inv_pow]
  rw [mul_pow, ← pow_mul, mul_comm n 2, pow_mul, h2, h4, mul_inv]
  norm_num

lemma schauder_nonneg (n k : ℕ) (u : ℝ) : 0 ≤ schauder n k u :=
  mul_nonneg (schauderAmp_pos n).le (tent_nonneg _)

lemma schauder_le_amp (n k : ℕ) (u : ℝ) : schauder n k u ≤ schauderAmp n := by
  unfold schauder
  calc schauderAmp n * tent _ ≤ schauderAmp n * 1 :=
        mul_le_mul_of_nonneg_left (tent_le_one _) (schauderAmp_pos n).le
    _ = _ := mul_one _

lemma continuous_schauder (n k : ℕ) : Continuous (schauder n k) := by
  unfold schauder
  have := continuous_tent
  fun_prop

lemma schauder_of_nonpos (n k : ℕ) {u : ℝ} (h : u ≤ 0) : schauder n k u = 0 := by
  unfold schauder
  rw [tent_of_nonpos, mul_zero]
  have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have : (0 : ℝ) < 2 ^ n := by positivity
  nlinarith

lemma schauder_of_one_le {n k : ℕ} (hk : k < 2 ^ n) {u : ℝ} (h : 1 ≤ u) :
    schauder n k u = 0 := by
  unfold schauder
  rw [tent_of_one_le, mul_zero]
  have : (k : ℝ) + 1 ≤ 2 ^ n := by exact_mod_cast hk
  have : (0 : ℝ) < 2 ^ n := by positivity
  nlinarith

lemma schauder_clamp {n k : ℕ} (hk : k < 2 ^ n) (u : ℝ) :
    schauder n k (clamp u) = schauder n k u := by
  rcases le_total u 0 with h | h
  · rw [clamp_of_nonpos h, schauder_of_nonpos _ _ h, schauder_of_nonpos _ _ le_rfl]
  rcases le_total u 1 with h' | h'
  · rw [clamp_of_mem h h']
  · rw [clamp_of_one_le h', schauder_of_one_le hk h', schauder_of_one_le hk le_rfl]

/-- At most one `k` has `S_{n,k}(u) ≠ 0`. -/
lemma schauder_unique {n k k' : ℕ} {u : ℝ} (h : schauder n k u ≠ 0) (h' : schauder n k' u ≠ 0) :
    k = k' := by
  have h1 := lt_of_tent_ne_zero (fun e => h (by unfold schauder; rw [e, mul_zero]))
  have h2 := lt_of_tent_ne_zero (fun e => h' (by unfold schauder; rw [e, mul_zero]))
  have a : (k : ℝ) < k' + 1 := by linarith [h1.1, h2.2]
  have b : (k' : ℝ) < k + 1 := by linarith [h2.1, h1.2]
  have a' : k < k' + 1 := by exact_mod_cast a
  have b' : k' < k + 1 := by exact_mod_cast b
  omega

/-- Properties of Schauder functions (S2). -/
lemma abs_sum_schauder_le (n : ℕ) (u : ℝ) (x : Fin (2 ^ n) → ℝ) {M : ℝ} (hM : 0 ≤ M)
    (hx : ∀ k, |x k| ≤ M) : |∑ k : Fin (2 ^ n), x k * schauder n k u| ≤ schauderAmp n * M := by
  by_cases h : ∃ k0 : Fin (2 ^ n), schauder n k0 u ≠ 0
  · obtain ⟨k0, hk0⟩ := h
    rw [Finset.sum_eq_single k0]
    · rw [abs_mul, abs_of_nonneg (schauder_nonneg _ _ _), mul_comm (schauderAmp n)]
      exact mul_le_mul (hx k0) (schauder_le_amp _ _ _) (schauder_nonneg _ _ _) hM
    · intro k _ hk
      have : schauder n k u = 0 := by
        by_contra hne
        exact hk (Fin.ext (schauder_unique hne hk0))
      rw [this, mul_zero]
    · simp
  · push Not at h
    simp only [h, mul_zero, Finset.sum_const_zero, abs_zero]
    exact mul_nonneg (schauderAmp_pos n).le hM

/-- The Schauder covariance identity, Step 1: the level sum is bounded by `2^{-n-2}`. -/
lemma abs_sum_schauder_mul_le (n : ℕ) (u v : ℝ) :
    |∑ k : Fin (2 ^ n), schauder n k u * schauder n k v| ≤ (4 * (2 : ℝ) ^ n)⁻¹ := by
  rw [← schauderAmp_sq, pow_two]
  have := abs_sum_schauder_le n u (fun k => schauder n k v) (M := schauderAmp n)
    (schauderAmp_pos n).le (fun k => by
      rw [abs_of_nonneg (schauder_nonneg _ _ _)]; exact schauder_le_amp _ _ _)
  simpa only [mul_comm] using this

/-- Properties of Schauder functions (S4): `S_{n,k}` vanishes on the dyadic grid of level
`N ≤ n`. -/
lemma schauder_dyadic (N e j k : ℕ) : schauder (N + e) k ((j : ℝ) / 2 ^ N) = 0 := by
  unfold schauder
  have : (2 : ℝ) ^ (N + e) * ((j : ℝ) / 2 ^ N) - k = (((j * 2 ^ e : ℕ) : ℤ) - k : ℤ) := by
    push_cast
    rw [pow_add]
    field_simp
  rw [this, tent_int, mul_zero]

/-- Properties of Schauder functions (S5): for `n < N`, `S_{n,k}` is affine on each interval
`[j 2^{-N}, (j+1) 2^{-N}]`; here in midpoint form with `N = n + m + 1`. -/
lemma schauder_midpoint (n m j k : ℕ) :
    schauder n k ((2 * j + 1 : ℝ) / 2 ^ (n + m + 1 + 1)) =
      (schauder n k ((j : ℝ) / 2 ^ (n + m + 1)) +
        schauder n k (((j : ℝ) + 1) / 2 ^ (n + m + 1))) / 2 := by
  unfold schauder
  set c : ℕ := 2 ^ m with hc
  have hc0 : 0 < c := by positivity
  have key := tent_midpoint_of_int ((j : ℤ) - k * (2 * c : ℕ)) c hc0
  have hcR : (c : ℝ) = 2 ^ m := by simp [hc]
  have e1 : (2 : ℝ) ^ n * ((j : ℝ) / 2 ^ (n + m + 1)) - k =
      (((j : ℤ) - k * (2 * c : ℕ) : ℤ) : ℝ) * ((2 * c : ℕ) : ℝ)⁻¹ := by
    push_cast; rw [hcR]; simp only [pow_succ, pow_add]; field_simp
  have e2 : (2 : ℝ) ^ n * ((j + 1 : ℝ) / 2 ^ (n + m + 1)) - k =
      ((((j : ℤ) - k * (2 * c : ℕ) : ℤ) : ℝ) + 1) * ((2 * c : ℕ) : ℝ)⁻¹ := by
    push_cast; rw [hcR]; simp only [pow_succ, pow_add]; field_simp
    try ring
  have e3 : (2 : ℝ) ^ n * ((2 * j + 1 : ℝ) / 2 ^ (n + m + 1 + 1)) - k =
      (((j : ℤ) - k * (2 * c : ℕ) : ℤ) : ℝ) * ((2 * c : ℕ) : ℝ)⁻¹ +
        ((2 * c : ℕ) : ℝ)⁻¹ / 2 := by
    push_cast; rw [hcR]; simp only [pow_succ, pow_add]; field_simp
    try ring
  rw [e1, e2, e3, key]
  ring

/-- Properties of Schauder functions (S6) and (S4): values of `S_{N,k}` on `D_{N+1}`. -/
lemma schauder_level_mid (N j k : ℕ) :
    schauder N k ((2 * j + 1 : ℝ) / 2 ^ (N + 1)) = if k = j then schauderAmp N else 0 := by
  unfold schauder
  have e : (2 : ℝ) ^ N * ((2 * j + 1 : ℝ) / 2 ^ (N + 1)) - k = (j : ℝ) - k + 1 / 2 := by
    rw [pow_succ]; field_simp; ring
  rw [e]
  split_ifs with h
  · subst h
    have : (k : ℝ) - k + 1 / 2 = 1 / 2 := by ring
    rw [this, tent_half, mul_one]
  · rcases lt_or_gt_of_ne h with h' | h'
    · have : (k : ℝ) + 1 ≤ j := by exact_mod_cast h'
      rw [tent_of_one_le (by linarith), mul_zero]
    · have : (j : ℝ) + 1 ≤ k := by exact_mod_cast h'
      rw [tent_of_nonpos (by linarith), mul_zero]

end ElboimSly.Brownian
