/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Brownian.Markov
public import ElboimSly.Foundations.Brownian.Gauss1d
import Mathlib

/-!
# Moments of Brownian motion

Moments.

For a standard `d`-dimensional Brownian motion `B` and `t ≥ 0`:
* `integral_eval_eq_zero`, `integral_mul_eval`: `E B(t)_i = 0`, `E[B(t)_i B(t)_j] = δ_{ij} t`;
* `integral_norm_sq_le`: `E ‖B(t)‖² ≤ d t` (so `E‖σ B(t)‖² ≤ σ² d t`);
* `integral_norm_pow_four_le`: `E ‖B(t)‖⁴ ≤ 80 d t²`.

Here `‖·‖` is the sup norm of `Fin d → ℝ`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace ElboimSly.Brownian

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {d : ℕ}

/-- The sup norm of `z : Fin d → ℝ` (with `d > 0`) is attained at a coordinate. -/
lemma exists_abs_eq_norm (z : Fin d → ℝ) (hd : 0 < d) : ∃ i, ‖z‖ = |z i| := by
  have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset (Fin d)) Finset.univ_nonempty
    (fun b => ‖z b‖₊)
  refine ⟨i, ?_⟩
  rw [Pi.norm_def, hi]; simp

/-- The sup norm to the power `n ≥ 1` is bounded by the sum of the `n`-th powers of the
coordinates. -/
lemma norm_pow_le_sum_abs_pow (z : Fin d → ℝ) {n : ℕ} (hn : n ≠ 0) :
    ‖z‖ ^ n ≤ ∑ i, |z i| ^ n := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · have : ‖z‖ = 0 := by rw [norm_eq_zero]; exact Subsingleton.elim _ _
    simp [this, hn]
  obtain ⟨i, h⟩ := exists_abs_eq_norm z hd
  rw [h]
  exact Finset.single_le_sum (f := fun i => |z i| ^ n) (fun j _ => by positivity)
    (Finset.mem_univ i)

lemma memLp_two_eval [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → (Fin d → ℝ)}
    (hB : IsStandardBrownianMotion d B P) (i : Fin d) (t : ℝ≥0) :
    MemLp (fun ω => B t ω i) 2 P :=
  ((hB.isPreBrownianReal i).isGaussianProcess.hasGaussianLaw_eval t).memLp_two

/-- Moments. `E B(t)_i = 0`. -/
theorem _root_.ElboimSly.IsStandardBrownianMotion.integral_eval_eq_zero [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → (Fin d → ℝ)} (hB : IsStandardBrownianMotion d B P) (i : Fin d) (t : ℝ≥0) :
    ∫ ω, B t ω i ∂P = 0 :=
  hB.integral_eval ⟨i, t⟩

/-- Moments. `E[B(t)_i B(t)_j] = δ_{ij} t`. -/
theorem _root_.ElboimSly.IsStandardBrownianMotion.integral_mul_eval [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → (Fin d → ℝ)} (hB : IsStandardBrownianMotion d B P) (i j : Fin d) (t : ℝ≥0) :
    ∫ ω, B t ω i * B t ω j ∂P = if i = j then (t : ℝ) else 0 := by
  have h := hB.covariance_eval ⟨i, t⟩ ⟨j, t⟩
  have m1 := hB.integral_eval_eq_zero i t
  have m2 := hB.integral_eval_eq_zero j t
  rw [covariance_eq_sub (memLp_two_eval hB i t) (memLp_two_eval hB j t)] at h
  simp only [Pi.mul_apply, m1, m2, zero_mul, sub_zero, min_self] at h
  rw [h]

/-- Moments. `E ‖B(t)‖² ≤ d t`. -/
theorem _root_.ElboimSly.IsStandardBrownianMotion.integral_norm_sq_le [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → (Fin d → ℝ)} (hB : IsStandardBrownianMotion d B P) (t : ℝ≥0) :
    ∫ ω, ‖B t ω‖ ^ 2 ∂P ≤ d * t := by
  have hi : ∀ i, Integrable (fun ω => |B t ω i| ^ 2) P := fun i => by
    simpa [sq_abs] using (memLp_two_eval hB i t).integrable_sq
  have hsum : ∫ ω, ∑ i, |B t ω i| ^ 2 ∂P = d * t := by
    rw [integral_finsetSum _ (fun i _ => hi i)]
    have : ∀ i : Fin d, ∫ ω, |B t ω i| ^ 2 ∂P = t := fun i => by
      simp only [sq_abs]
      have := hB.integral_mul_eval i i t
      simpa [sq] using this
    rw [Finset.sum_congr rfl (fun i _ => this i)]
    simp
  calc ∫ ω, ‖B t ω‖ ^ 2 ∂P ≤ ∫ ω, ∑ i, |B t ω i| ^ 2 ∂P := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω => by positivity)
          (integrable_finsetSum _ fun i _ => hi i) (Filter.Eventually.of_forall fun ω => ?_)
        exact norm_pow_le_sum_abs_pow _ (by norm_num)
    _ = d * t := hsum

/-- Moments. `E ‖B(t)‖⁴ ≤ 80 d t²`. -/
theorem _root_.ElboimSly.IsStandardBrownianMotion.integral_norm_pow_four_le
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → (Fin d → ℝ)} (hB : IsStandardBrownianMotion d B P)
    (t : ℝ≥0) : ∫ ω, ‖B t ω‖ ^ 4 ∂P ≤ 80 * d * (t : ℝ) ^ 2 := by
  have hlaw : ∀ i, HasLaw (fun ω => B t ω i) (gaussianReal 0 t) P := fun i =>
    (hB.isPreBrownianReal i).hasLaw_eval t
  have hi : ∀ i, Integrable (fun ω => |B t ω i| ^ 4) P := fun i => by
    have := (hlaw i).memLp_comp (f := fun x : ℝ => x) (p := 4)
      (memLp_id_gaussianReal' 4 (by simp))
    have h2 := this.integrable_norm_pow (p := 4) (by norm_num)
    simpa [Real.norm_eq_abs] using h2
  have h4 : ∀ i, ∫ ω, |B t ω i| ^ 4 ∂P ≤ 80 * (t : ℝ) ^ 2 := fun i => by
    have := integral_pow_four_le_of_hasLaw (hlaw i)
    simpa [pow_abs, abs_pow, Even.pow_abs (by decide : Even 4)] using this
  calc ∫ ω, ‖B t ω‖ ^ 4 ∂P ≤ ∫ ω, ∑ i, |B t ω i| ^ 4 ∂P := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω => by positivity)
          (integrable_finsetSum _ fun i _ => hi i) (Filter.Eventually.of_forall fun ω => ?_)
        exact norm_pow_le_sum_abs_pow _ (by norm_num)
    _ = ∑ i, ∫ ω, |B t ω i| ^ 4 ∂P := integral_finsetSum _ (fun i _ => hi i)
    _ ≤ ∑ _i : Fin d, 80 * (t : ℝ) ^ 2 := Finset.sum_le_sum fun i _ => h4 i
    _ = 80 * d * (t : ℝ) ^ 2 := by simp; ring

end ElboimSly.Brownian
