/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.StrongApprox.TusnadyConst
public import ElboimSly.Foundations.StrongApprox.Quantile
public import ElboimSly.Foundations.StrongApprox.BinomialFacts
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Function.Floor

/-!
# The step density of `Bin(m, 1/2)`

Tusn'ady-type bound for Bin(m,frac12), Step 1. The function `f(y) = sab m ⌈y - 1/2⌉` integrates to `sab m i`
on the cell `(i - 1/2, i + 1/2]`, so `T m j` is an integral of `f`. We use the ceiling instead of
the floor of the written proof so that each cell is half-open on the right, which makes the cell
integrals exact; nothing else changes.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped NNReal Real ENNReal

namespace ElboimSly
namespace StrongApprox

/-- The step density `f(y) = sab m ⌈y - 1/2⌉` (Step 1 of tusn'ady-type bound for Bin(m,frac12)). -/
noncomputable def tf (m : ℕ) (y : ℝ) : ℝ := sab m ⌈y - 1 / 2⌉

theorem tf_nonneg (m : ℕ) (y : ℝ) : 0 ≤ tf m y := sab_nonneg m _

theorem sab_le_one (m : ℕ) (j : ℤ) : sab m j ≤ 1 := by
  by_cases h : 0 ≤ j ∧ j ≤ m
  · have h1 := sum_sab m
    have hj : j.toNat ∈ Finset.range (m + 1) := by simp; omega
    have h2 : sab m ((j.toNat : ℕ) : ℤ) ≤ ∑ k ∈ Finset.range (m + 1), sab m k :=
      Finset.single_le_sum (f := fun k : ℕ => sab m k) (fun k _ => sab_nonneg m k) hj
    have : ((j.toNat : ℕ) : ℤ) = j := by omega
    rw [this] at h2; linarith
  · have : sab m j = 0 := by unfold sab; simp [h]
    rw [this]; norm_num

theorem tf_le_one (m : ℕ) (y : ℝ) : tf m y ≤ 1 := sab_le_one m _

theorem measurable_tf (m : ℕ) : Measurable (tf m) := by
  unfold tf
  exact (measurable_from_top (f := sab m)).comp ((Int.measurable_ceil).comp (by fun_prop))

theorem tf_eq_on_cell (m : ℕ) (i : ℤ) {y : ℝ} (h1 : (i : ℝ) - 1 / 2 < y) (h2 : y ≤ (i : ℝ) + 1 / 2) :
    tf m y = sab m i := by
  unfold tf
  congr 1
  rw [Int.ceil_eq_iff]
  constructor <;> linarith

theorem integrableOn_tf (m : ℕ) {s : Set ℝ} (hs : volume s ≠ ∞) : IntegrableOn (tf m) s :=
  Measure.integrableOn_of_bounded (M := 1) hs (measurable_tf m).aestronglyMeasurable
    (ae_of_all _ fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (tf_nonneg m y)]; exact tf_le_one m y)

theorem intervalIntegrable_tf (m : ℕ) (a b : ℝ) : IntervalIntegrable (tf m) volume a b :=
  ⟨integrableOn_tf m (by simp), integrableOn_tf m (by simp)⟩

theorem integral_tf_cell (m : ℕ) (i : ℤ) :
    ∫ y in ((i : ℝ) - 1 / 2)..((i : ℝ) + 1 / 2), tf m y = sab m i := by
  rw [intervalIntegral.integral_of_le (by linarith)]
  have : ∫ y in Ioc ((i : ℝ) - 1 / 2) ((i : ℝ) + 1 / 2), tf m y =
      ∫ y in Ioc ((i : ℝ) - 1 / 2) ((i : ℝ) + 1 / 2), sab m i :=
    setIntegral_congr_fun measurableSet_Ioc fun y hy => tf_eq_on_cell m i hy.1 hy.2
  rw [this]
  simp; ring

theorem sabT_succ (m : ℕ) (j : ℤ) : sabT m j = sab m j + sabT m (j + 1) := by
  have h1 := sabF_add_sabT m j
  have h2 := sabF_add_sabT m (j + 1)
  have h3 := sabF_sub m j
  rw [add_sub_cancel_right] at h2
  linarith

theorem sabT_of_gt (m : ℕ) {j : ℤ} (hj : (m : ℤ) < j) : sabT m j = 0 := by
  unfold sabT
  refine Finset.sum_eq_zero fun i hi => ?_
  have : ¬ j ≤ (i : ℤ) := by have := Finset.mem_range.1 hi; omega
  simp [this]

/-- `T m j` as an integral of the step density. -/
theorem sabT_eq_integral (m : ℕ) : ∀ n j : ℕ, j + n = m + 1 →
    sabT m j = ∫ y in ((j : ℝ) - 1 / 2)..((m : ℝ) + 1 / 2), tf m y := by
  intro n
  induction n with
  | zero =>
    intro j hj
    have : j = m + 1 := by omega
    subst this
    rw [sabT_of_gt m (by push_cast; omega)]
    push_cast
    have : ((m : ℝ) + 1 - 1 / 2) = (m : ℝ) + 1 / 2 := by ring
    rw [this]; simp
  | succ n ih =>
    intro j hj
    have h := ih (j + 1) (by omega)
    rw [sabT_succ]
    push_cast at h ⊢
    have e1 : ((j : ℝ) + 1 - 1 / 2) = (j : ℝ) + 1 / 2 := by ring
    rw [e1] at h
    rw [h]
    have hc := integral_tf_cell m (j : ℤ)
    push_cast at hc
    rw [← hc]
    exact intervalIntegral.integral_add_adjacent_intervals (intervalIntegrable_tf m _ _)
      (intervalIntegrable_tf m _ _)

/-- The rescaled step density `G(v) = s f(μ + s v)`. -/
noncomputable def tG (m : ℕ) (v : ℝ) : ℝ := sbS m * tf m (sbS m * v + m / 2)

theorem integral_tG (m : ℕ) (a b : ℝ) :
    ∫ v in a..b, tG m v = ∫ y in (sbS m * a + m / 2)..(sbS m * b + m / 2), tf m y := by
  unfold tG
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_mul_add (fun y => tf m y) (sbS_pos m).ne' ((m : ℝ) / 2),
    smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ (sbS_pos m).ne', one_mul]

theorem measurable_tG (m : ℕ) : Measurable (tG m) := by
  unfold tG
  exact measurable_const.mul ((measurable_tf m).comp (by fun_prop))

theorem sabT_le_exp {m : ℕ} (hm : 1 ≤ m) {n : ℕ} {ρ : ℝ} (hρ : 0 ≤ ρ)
    (h : ∀ i : ℕ, n ≤ i → ρ ≤ (i : ℝ) - m / 2) :
    sabT m n ≤ Real.exp (-(2 * ρ ^ 2 / m)) := by
  classical
  refine le_trans ?_ (sab_upper_tail m hm hρ (fun i => ρ ≤ (i : ℝ) - m / 2) (fun k hk => hk))
  unfold sabT
  refine Finset.sum_le_sum fun i _ => ?_
  by_cases hi : (n : ℤ) ≤ i
  · have : ρ ≤ (i : ℝ) - m / 2 := h i (by exact_mod_cast hi)
    simp [hi, this]
  · simp only [hi, ite_false]
    split_ifs <;> first | exact sab_nonneg m i | exact le_rfl

/-- Tusn'ady-type bound for Bin(m,frac12), `eq:sa-tail-split`. -/
theorem tus_split {m : ℕ} (hm : 2000000000 ≤ m) {j : ℕ} (_hj0 : (m : ℝ) / 2 + 1 / 2 ≤ j)
    (hjm : j ≤ m) (hvj : ((j : ℝ) - 1 / 2 - m / 2) / sbS m ≤ tV m) :
    0 ≤ sabT m j - ∫ v in (((j : ℝ) - 1 / 2 - m / 2) / sbS m)..(tV m), tG m v ∧
    sabT m j - ∫ v in (((j : ℝ) - 1 / 2 - m / 2) / sbS m)..(tV m), tG m v ≤
      Real.exp (-(tV m ^ 2 / 4)) := by
  have hm1 : 1 ≤ m := by omega
  have hm' : (2000000000 : ℝ) ≤ m := by exact_mod_cast hm
  have hs0 := sbS_pos m
  set s := sbS m with hs
  set V := tV m with hV
  have hsV_le := sbS_mul_tV_le (m := m)
  have hsV_ge := sbS_mul_tV_ge (m := m)
  rw [← hs, ← hV] at hsV_le hsV_ge
  have e1 : s * (((j : ℝ) - 1 / 2 - m / 2) / s) + m / 2 = (j : ℝ) - 1 / 2 := by
    field_simp; ring
  have hint := sabT_eq_integral m (m + 1 - j) j (by omega)
  have hGint : ∫ v in (((j : ℝ) - 1 / 2 - m / 2) / s)..V, tG m v =
      ∫ y in ((j : ℝ) - 1 / 2)..(s * V + m / 2), tf m y := by
    rw [integral_tG, e1]
  have hle1 : s * V + m / 2 ≤ (m : ℝ) + 1 / 2 := by linarith
  have hle0 : (j : ℝ) - 1 / 2 ≤ s * V + m / 2 := by
    have : (j : ℝ) - 1 / 2 - m / 2 ≤ s * V := by
      have := (div_le_iff₀ hs0).1 hvj; linarith
    linarith
  have hdecomp : sabT m j - ∫ v in (((j : ℝ) - 1 / 2 - m / 2) / s)..V, tG m v =
      ∫ y in (s * V + m / 2)..((m : ℝ) + 1 / 2), tf m y := by
    rw [hint, hGint, ← intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_tf m ((j : ℝ) - 1 / 2) (s * V + m / 2))
      (intervalIntegrable_tf m (s * V + m / 2) ((m : ℝ) + 1 / 2))]
    ring
  rw [hdecomp]
  refine ⟨intervalIntegral.integral_nonneg hle1 (fun y _ => tf_nonneg m y), ?_⟩
  -- the tail bound
  set a : ℝ := m / 2 + s * V - 1 / 2 with ha
  have ha0 : 0 ≤ a := by rw [ha]; linarith
  set n1 : ℕ := ⌈a⌉₊ with hn1
  have hn1a : a ≤ n1 := Nat.le_ceil a
  have hn1b : (n1 : ℝ) < a + 1 := Nat.ceil_lt_add_one ha0
  have hn1m : n1 ≤ m + 1 := by
    have : (n1 : ℝ) ≤ m + 1 := by rw [ha] at hn1b; linarith
    exact_mod_cast this
  have hT := sabT_eq_integral m (m + 1 - n1) n1 (by omega)
  have hmono : ∫ y in (s * V + m / 2)..((m : ℝ) + 1 / 2), tf m y ≤
      ∫ y in ((n1 : ℝ) - 1 / 2)..((m : ℝ) + 1 / 2), tf m y :=
    intervalIntegral.integral_mono_interval (by linarith) hle1 le_rfl
      (ae_of_all _ fun y => tf_nonneg m y) (intervalIntegrable_tf m _ _)
  rw [← hT] at hmono
  refine hmono.trans ?_
  have hρ : 0 ≤ s * V - 1 / 2 := by linarith
  have := sabT_le_exp (m := m) hm1 (n := n1) (ρ := s * V - 1 / 2) hρ (fun i hi => by
    have : (n1 : ℝ) ≤ i := by exact_mod_cast hi
    rw [ha] at hn1a; linarith)
  refine this.trans (Real.exp_le_exp.2 ?_)
  -- 2ρ²/m ≥ V²/4
  have hρ2 : 3 / 4 * (s * V) ≤ s * V - 1 / 2 := by linarith
  have hs2 := sbS_sq_ge (m := m)
  rw [← hs] at hs2
  have hmpos : (0 : ℝ) < m := by linarith
  have hV2 : (s * V - 1 / 2) ^ 2 ≥ 9 / 16 * (s * V) ^ 2 := by nlinarith
  rw [neg_le_neg_iff, le_div_iff₀ hmpos]
  have : (s * V) ^ 2 = s ^ 2 * V ^ 2 := by ring
  nlinarith [sq_nonneg V]

end StrongApprox
end ElboimSly
