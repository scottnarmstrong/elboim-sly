/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import Mathlib

/-!
# Exponential inequalities for Freedman's inequality

Exponential inequalities. With `φ u = exp u - 1 - u`, we prove the inequalities used in the
exponential supermartingale argument.
-/

public section

namespace ElboimSly

/-- `φ(u) = e^u - 1 - u`. -/
@[expose] noncomputable def concPhi (u : ℝ) : ℝ := Real.exp u - 1 - u

/-- Series tail `s(u) = ∑_{m ≥ 0} u^m/(m+2)!`, so that `φ(u) = u² s(u)`. -/
noncomputable def concPhiSeries (u : ℝ) : ℝ := ∑' m : ℕ, u ^ m / ((m + 2).factorial : ℝ)

lemma concPhiSeries_summable (u : ℝ) :
    Summable (fun m : ℕ => u ^ m / ((m + 2).factorial : ℝ)) := by
  have h := NormedSpace.expSeries_div_hasSum_exp (𝔸 := ℝ) u
  have h2 := ((hasSum_nat_add_iff' 2).2 h).summable
  by_cases hu : u = 0
  · subst hu
    refine summable_of_ne_finset_zero (s := {0}) ?_
    intro m hm
    have : m ≠ 0 := by simpa using hm
    simp [this]
  · have := h2.mul_left ((u ^ 2)⁻¹)
    refine this.congr fun m => ?_
    field_simp
    ring

lemma concPhi_eq (u : ℝ) : concPhi u = u ^ 2 * concPhiSeries u := by
  have h := NormedSpace.expSeries_div_hasSum_exp (𝔸 := ℝ) u
  rw [← Real.exp_eq_exp_ℝ] at h
  have h2 := (hasSum_nat_add_iff' 2).2 h
  have h3 := (concPhiSeries_summable u).hasSum.mul_left (u ^ 2)
  have h4 : (fun m : ℕ => u ^ 2 * (u ^ m / ((m + 2).factorial : ℝ))) =
      fun m : ℕ => u ^ (m + 2) / ((m + 2).factorial : ℝ) := by
    funext m; ring
  rw [h4] at h3
  have := h3.unique h2
  unfold concPhi concPhiSeries
  simp [Finset.sum_range_succ] at this
  linarith

lemma concPhiSeries_mono {u w : ℝ} (hu : 0 ≤ u) (huw : u ≤ w) :
    concPhiSeries u ≤ concPhiSeries w := by
  refine (concPhiSeries_summable u).tsum_le_tsum (fun m => ?_) (concPhiSeries_summable w)
  gcongr

/-- Exponential inequalities (d), first claim. -/
lemma one_add_mul_exp_neg_le_one (y : ℝ) : (1 + y) * Real.exp (-y) ≤ 1 := by
  have h := Real.add_one_le_exp y
  have h2 : Real.exp y * Real.exp (-y) = 1 := by rw [← Real.exp_add]; simp
  nlinarith [Real.exp_pos (-y)]

/-- Exponential inequalities (d), second claim. -/
lemma mul_exp_neg_le_exp_neg_one (z : ℝ) : z * Real.exp (-z) ≤ Real.exp (-1) := by
  have h := Real.add_one_le_exp (z - 1)
  have h2 : Real.exp (z - 1) * Real.exp (-z) = Real.exp (-1) := by
    rw [← Real.exp_add]; congr 1; ring
  nlinarith [Real.exp_pos (-z)]

/-- Exponential inequalities (a), first half. -/
lemma concPhi_le_sq_div_two {u : ℝ} (hu : u ≤ 0) : concPhi u ≤ u ^ 2 / 2 := by
  let h : ℝ → ℝ := fun u => u ^ 2 / 2 - concPhi u
  have hd : ∀ x, HasDerivAt h (x + 1 - Real.exp x) x := by
    intro x
    have := (((hasDerivAt_pow 2 x).div_const 2).sub
      (((Real.hasDerivAt_exp x).sub_const 1).sub (hasDerivAt_id x)))
    convert this using 1
    · funext y
      simp [h, concPhi]
    · simp
      ring
  have hanti : Antitone h := by
    refine antitone_of_deriv_nonpos (fun x => (hd x).differentiableAt) (fun x => ?_)
    rw [(hd x).deriv]
    linarith [Real.add_one_le_exp x]
  have := hanti hu
  have h0 : h 0 = 0 := by simp [h, concPhi]
  simp only [h, concPhi] at this h0 ⊢
  linarith

/-- Exponential inequalities (a), second half. -/
lemma sq_div_two_le_concPhi {w : ℝ} (hw : 0 ≤ w) : w ^ 2 / 2 ≤ concPhi w := by
  have := Real.sum_le_exp_of_nonneg hw 3
  simp [Finset.sum_range_succ, Nat.factorial] at this
  unfold concPhi
  linarith

/-- Exponential inequalities (b). -/
lemma concPhi_le_mul_concPhi {u w : ℝ} (hw : 0 < w) (huw : u ≤ w) :
    concPhi u ≤ u ^ 2 * concPhi w / w ^ 2 := by
  rcases le_or_gt u 0 with hu | hu
  · have h1 := concPhi_le_sq_div_two hu
    have h2 := sq_div_two_le_concPhi hw.le
    calc concPhi u ≤ u ^ 2 / 2 := h1
      _ ≤ u ^ 2 * concPhi w / w ^ 2 := by
        rw [le_div_iff₀ (by positivity)]
        have : w ^ 2 / 2 ≤ concPhi w := h2
        nlinarith [sq_nonneg u]
  · rw [concPhi_eq u, concPhi_eq w]
    have := concPhiSeries_mono hu.le huw
    field_simp
    gcongr

/-- Exponential inequalities (c). -/
lemma concPhi_le_of_lt_three {w : ℝ} (hw0 : 0 ≤ w) (hw3 : w < 3) :
    concPhi w ≤ w ^ 2 / (2 * (1 - w / 3)) := by
  have hr : w / 3 < 1 := by linarith
  have hg : HasSum (fun m : ℕ => (1 / 2 : ℝ) * (w / 3) ^ m) ((1 / 2) * (1 - w / 3)⁻¹) :=
    (hasSum_geometric_of_lt_one (by positivity) hr).mul_left (1 / 2)
  have hle : concPhiSeries w ≤ (1 / 2) * (1 - w / 3)⁻¹ := by
    refine hasSum_le (fun m => ?_) (concPhiSeries_summable w).hasSum hg
    have hf : (2 * 3 ^ m : ℝ) ≤ ((m + 2).factorial : ℝ) := by
      have : 2 * 3 ^ m ≤ (m + 2).factorial := by
        induction m with
        | zero => simp [Nat.factorial]
        | succ n ih =>
          rw [pow_succ, show n + 1 + 2 = (n + 2) + 1 by ring, Nat.factorial_succ]
          nlinarith
      exact_mod_cast this
    rw [div_le_iff₀ (by positivity)]
    have : (1 / 2 : ℝ) * (w / 3) ^ m * ((m + 2).factorial : ℝ) ≥
        (1 / 2) * (w / 3) ^ m * (2 * 3 ^ m) :=
      mul_le_mul_of_nonneg_left hf (by positivity)
    calc w ^ m = (1 / 2) * (w / 3) ^ m * (2 * 3 ^ m) := by
          rw [div_pow]; field_simp
      _ ≤ _ := this
  rw [concPhi_eq]
  have hpos : 0 < 1 - w / 3 := by linarith
  calc w ^ 2 * concPhiSeries w ≤ w ^ 2 * ((1 / 2) * (1 - w / 3)⁻¹) := by gcongr
    _ = w ^ 2 / (2 * (1 - w / 3)) := by field_simp

end ElboimSly
