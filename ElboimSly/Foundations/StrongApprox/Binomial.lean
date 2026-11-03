/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import Mathlib.Probability.Distributions.Binomial
public import Mathlib.Probability.HasLaw
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
public import ElboimSly.Foundations.StrongApprox.Elementary

/-!
# Binomial$(m, \tfrac12)$ notation and facts

Binomial(m,frac12) notation; Binomial facts (Part I).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology Finset
open scoped NNReal Real ENNReal unitInterval

namespace ElboimSly
namespace StrongApprox

/-- The parameter `1/2` as a point of the unit interval. -/
noncomputable def sahalf : unitInterval := ⟨1 / 2, by constructor <;> norm_num⟩

/-- Binomial(m,frac12) notation. `sab m j = binom m j / 2^m` for `0 ≤ j ≤ m` and `0` otherwise. -/
noncomputable def sab (m : ℕ) (j : ℤ) : ℝ :=
  if 0 ≤ j ∧ j ≤ m then (m.choose j.toNat : ℝ) / 2 ^ m else 0

/-- Binomial(m,frac12) notation. The lower partial sum `F m j = ∑_{i ≤ j} sab m i`. -/
noncomputable def sabF (m : ℕ) (j : ℤ) : ℝ :=
  ∑ i ∈ range (m + 1), if (i : ℤ) ≤ j then sab m i else 0

/-- Binomial(m,frac12) notation. The upper partial sum `T m j = ∑_{i ≥ j} sab m i`. -/
noncomputable def sabT (m : ℕ) (j : ℤ) : ℝ :=
  ∑ i ∈ range (m + 1), if j ≤ (i : ℤ) then sab m i else 0

theorem sab_natCast (m k : ℕ) : sab m k = (m.choose k : ℝ) / 2 ^ m := by
  unfold sab
  by_cases h : k ≤ m
  · simp [h]
  · simp [h, Nat.choose_eq_zero_of_lt (not_le.1 h)]

theorem sab_nonneg (m : ℕ) (j : ℤ) : 0 ≤ sab m j := by
  unfold sab; split_ifs <;> positivity

theorem sab_pos {m : ℕ} {j : ℤ} (h0 : 0 ≤ j) (h1 : j ≤ m) : 0 < sab m j := by
  unfold sab
  simp only [h0, h1, and_self, ite_true]
  have : 0 < m.choose j.toNat := Nat.choose_pos (by omega)
  positivity

theorem sab_natCast_symm {m k : ℕ} (hk : k ≤ m) : sab m ((m - k : ℕ) : ℤ) = sab m k := by
  rw [sab_natCast, sab_natCast, Nat.choose_symm hk]

theorem sum_sab (m : ℕ) : ∑ k ∈ range (m + 1), sab m k = 1 := by
  simp only [sab_natCast]
  rw [← Finset.sum_div, ← Nat.cast_sum, Nat.sum_range_choose]
  push_cast
  field_simp

theorem sabF_add_sabT (m : ℕ) (j : ℤ) : sabF m (j - 1) + sabT m j = 1 := by
  unfold sabF sabT
  rw [← Finset.sum_add_distrib, ← sum_sab m]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : (i : ℤ) ≤ j - 1
  · have h2 : ¬ j ≤ (i : ℤ) := by omega
    simp only [h, h2, ite_true, ite_false]; ring
  · have h2 : j ≤ (i : ℤ) := by omega
    simp only [h, h2, ite_true, ite_false]; ring

theorem sabF_nonneg (m : ℕ) (j : ℤ) : 0 ≤ sabF m j :=
  Finset.sum_nonneg fun i _ => by split_ifs <;> simp [sab_nonneg]

theorem sabT_nonneg (m : ℕ) (j : ℤ) : 0 ≤ sabT m j :=
  Finset.sum_nonneg fun i _ => by split_ifs <;> simp [sab_nonneg]

/-! ### Relation with Mathlib's binomial law -/

theorem choose_half_pow {m k : ℕ} (h : k ≤ m) :
    (m.choose k : ℝ) * (1 / 2) ^ k * (1 / 2) ^ (m - k) = (m.choose k : ℝ) / 2 ^ m := by
  rw [mul_assoc, ← pow_add, Nat.add_sub_cancel' h, one_div, inv_pow, div_eq_mul_inv]

theorem binomial_real_singleton_half (m k : ℕ) :
    (binomial m sahalf).real {k} = sab m k := by
  rw [binomial_real_singleton, sab_natCast]
  by_cases h : k ≤ m
  · have e : (sahalf : ℝ) = 1 / 2 := rfl
    have e2 : (1 : ℝ) - (sahalf : ℝ) = 1 / 2 := by rw [e]; norm_num
    rw [e2, e]; exact choose_half_pow h
  · simp [Nat.choose_eq_zero_of_lt (not_le.1 h)]

open Classical in
theorem binomial_real_apply_half (m : ℕ) (A : Set ℕ) :
    (binomial m sahalf).real A = ∑ k ∈ range (m + 1), if k ∈ A then sab m k else 0 := by
  have hA : MeasurableSet A := MeasurableSet.of_discrete
  rw [measureReal_def, binomial_eq_sum_dirac]
  have e : Finset.Iic m = range (m + 1) := by ext; simp
  rw [e, Measure.coe_finsetSum, Finset.sum_apply]
  rw [ENNReal.toReal_sum (fun k _ => ?_)]
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [Measure.smul_apply, Measure.dirac_apply' _ hA, smul_eq_mul]
    have hs := binomial_real_singleton_half m k
    rw [binomial_real_singleton] at hs
    by_cases hk : k ∈ A
    · simp only [Set.indicator_of_mem hk, hk, ite_true, Pi.one_apply, mul_one]
      rw [ENNReal.toReal_ofReal (hs ▸ sab_nonneg m k), hs]
    · simp [hk]
  · rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)

/-- A random variable `Y` is `Bin(m, 1/2)` if its law is Mathlib's `binomial m (1/2)`. -/
theorem hasLaw_real_pred_half {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {Y : Ω → ℕ} {m : ℕ}
    (hY : HasLaw Y (binomial m sahalf) P) (p : ℕ → Prop) [DecidablePred p] :
    P.real {ω | p (Y ω)} = ∑ k ∈ range (m + 1), if p k then sab m k else 0 := by
  rw [hY.measureReal_eq (p := p) MeasurableSet.of_discrete, binomial_real_apply_half]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp

end StrongApprox
end ElboimSly
