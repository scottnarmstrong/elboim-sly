/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.SRW.Law1dFormula
public import ElboimSly.Foundations.SRW.PoissonTail
public import Mathlib

/-!
# Local lower bound

Local lower bound.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Real
open scoped ENNReal NNReal

namespace ElboimSly
namespace SRW

/-- A uniform lower bound for the Poisson probabilities near the mean. -/
theorem po_ge_near {t : ℝ} (ht : 1 ≤ t) {m : ℕ} (hm1 : t - √t ≤ m) (hm2 : (m : ℝ) ≤ t + √t) :
    Real.exp (-2) / √(2 * t) ≤ po t m := by
  have ht0 : 0 < t := by linarith
  have hs : √t ^ 2 = t := Real.sq_sqrt ht0.le
  have hsq : ((m : ℝ) - t) ^ 2 ≤ t := by
    rw [← hs]
    apply sq_le_sq' <;> linarith
  have hst : √t ≤ t := by
    calc √t = √t * 1 := (mul_one _).symm
      _ ≤ √t * √t := by gcongr; rw [Real.one_le_sqrt]; exact ht
      _ = t := Real.mul_self_sqrt ht0.le
  have hmax : max (m : ℝ) 1 ≤ 2 * t := max_le (by linarith) (by linarith)
  refine le_trans ?_ (po_ge ht0 m)
  have hmaxpos : (0 : ℝ) < max (m : ℝ) 1 := lt_max_of_lt_right one_pos
  have h1 : Real.exp (-1) ≤ Real.exp (-((m : ℝ) - t) ^ 2 / t) := by
    apply Real.exp_le_exp.2
    rw [le_div_iff₀ ht0]
    nlinarith
  have h2 : √(max (m : ℝ) 1) ≤ √(2 * t) := Real.sqrt_le_sqrt hmax
  have h3 : 0 < √(max (m : ℝ) 1) := Real.sqrt_pos.2 hmaxpos
  have he : Real.exp (-2) = Real.exp (-1) / Real.exp 1 := by
    rw [← Real.exp_sub]; norm_num
  rw [he, div_div]
  apply div_le_div₀ (Real.exp_pos _).le h1 (by positivity)
  exact mul_le_mul_of_nonneg_left h2 (Real.exp_pos 1).le

/-- Local lower bound: for `t ≥ 1` and `|k| ≤ √t`,
`P(Y(t) = k) ≥ e^{-4} / (4 √t)`. -/
theorem IsSRW.local_lower {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {Y : Ω → PathSpace 1}
    (hY : IsSRW P Y) {t : ℝ≥0} (ht : 1 ≤ (t : ℝ)) {k : ℤ} (hk : |(k : ℝ)| ≤ √t) :
    Real.exp (-4) / (4 * √t) ≤ P.real {ω | Y ω t 0 = k} := by
  rw [hY.real_eval_eq]
  set r : ℝ := (t : ℝ) with hr
  have ht0 : 0 < r := by linarith
  have hsr : 0 < √r := Real.sqrt_pos.2 ht0
  have hk' : (k.natAbs : ℝ) ≤ √r := by
    rw [Nat.cast_natAbs, Int.cast_abs]; exact hk
  have hs1 : 1 ≤ √r := by rw [Real.one_le_sqrt]; exact ht
  have hsle : √r ≤ r := by
    calc √r = √r * 1 := (mul_one _).symm
      _ ≤ √r * √r := by gcongr
      _ = r := Real.mul_self_sqrt ht0.le
  set n : ℕ := ⌊√r⌋₊ with hn
  set c : ℕ := ⌈r - √r⌉₊ with hc
  have hnr : (√r) / 2 ≤ n := by
    have h1 := Nat.lt_floor_add_one (√r)
    have h2 : (1 : ℝ) ≤ n := by exact_mod_cast ((Nat.one_le_floor_iff _).2 hs1)
    linarith
  have hnle : (n : ℝ) ≤ √r := Nat.floor_le hsr.le
  have hterm : ∀ m ∈ Finset.Ico c (c + n), Real.exp (-4) / (2 * r) ≤
      po r m * po r (m + k.natAbs) := by
    intro m hm
    rw [Finset.mem_Ico] at hm
    have hc1 : r - √r ≤ c := Nat.le_ceil _
    have hc2 : (c : ℝ) < r - √r + 1 := Nat.ceil_lt_add_one (by linarith)
    have hm1 : r - √r ≤ m := hc1.trans (by exact_mod_cast hm.1)
    have hm2 : (m : ℝ) < r := by
      have : (m : ℝ) + 1 ≤ c + n := by exact_mod_cast hm.2
      linarith
    have hmk : ((m + k.natAbs : ℕ) : ℝ) ≤ r + √r := by
      push_cast; linarith
    have hmk1 : r - √r ≤ ((m + k.natAbs : ℕ) : ℝ) := by
      push_cast; linarith [Nat.cast_nonneg (α := ℝ) k.natAbs]
    have e1 := po_ge_near ht (m := m) hm1 (by linarith)
    have e2 := po_ge_near ht hmk1 hmk
    have h2r : (0 : ℝ) < √(2 * r) := Real.sqrt_pos.2 (by linarith)
    calc Real.exp (-4) / (2 * r)
        = (Real.exp (-2) / √(2 * r)) * (Real.exp (-2) / √(2 * r)) := by
          rw [div_mul_div_comm, ← Real.exp_add, Real.mul_self_sqrt (by linarith)]; norm_num
      _ ≤ po r m * po r (m + k.natAbs) :=
          mul_le_mul e1 e2 (by positivity) (po_nonneg ht0.le _)
  have hsumm : Summable (fun m : ℕ => po r m * po r (m + k.natAbs)) := by
    refine Summable.of_nonneg_of_le
      (fun m => mul_nonneg (po_nonneg ht0.le _) (po_nonneg ht0.le _))
      (fun m => ?_) (hasSum_one_poissonMeasure r.toNNReal).summable
    have hle : po r (m + k.natAbs) ≤ 1 := by
      have := po_le_inv_sqrt_pi_mul ht (m + k.natAbs)
      refine this.trans ?_
      rw [div_le_one (Real.sqrt_pos.2 (by positivity))]
      rw [Real.one_le_sqrt]; nlinarith [Real.pi_gt_three]
    have hpo : po r m = Real.exp (-(r.toNNReal : ℝ)) * (r.toNNReal : ℝ) ^ m / (Nat.factorial m : ℝ) := by
      unfold po; rw [Real.coe_toNNReal _ ht0.le]
    calc po r m * po r (m + k.natAbs) ≤ po r m * 1 :=
          mul_le_mul_of_nonneg_left hle (po_nonneg ht0.le _)
      _ = _ := by rw [mul_one, hpo]
  have hcard : (Finset.Ico c (c + n)).card = n := by simp
  calc Real.exp (-4) / (4 * √r)
      ≤ (n : ℝ) * (Real.exp (-4) / (2 * r)) := by
        have hrs : r = √r * √r := (Real.mul_self_sqrt ht0.le).symm
        rw [div_le_iff₀ (by positivity)]
        have : (n : ℝ) * (Real.exp (-4) / (2 * r)) * (4 * √r) =
            (n : ℝ) / √r * 2 * Real.exp (-4) := by
          generalize √r = s at hrs hsr ⊢
          rw [hrs]
          field_simp
          ring
        rw [this]
        have h3 : (1 / 2 : ℝ) ≤ (n : ℝ) / √r := by
          rw [le_div_iff₀ hsr]; linarith
        have := Real.exp_pos (-4)
        nlinarith
    _ = ∑ m ∈ Finset.Ico c (c + n), Real.exp (-4) / (2 * r) := by
        rw [Finset.sum_const, hcard, nsmul_eq_mul]
    _ ≤ ∑ m ∈ Finset.Ico c (c + n), po r m * po r (m + k.natAbs) :=
        Finset.sum_le_sum hterm
    _ ≤ ∑' m : ℕ, po r m * po r (m + k.natAbs) :=
        hsumm.sum_le_tsum _ (fun m _ => mul_nonneg (po_nonneg ht0.le _) (po_nonneg ht0.le _))

end SRW
end ElboimSly
