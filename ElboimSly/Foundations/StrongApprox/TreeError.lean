/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.StrongApprox.DyadicTree
public import ElboimSly.Foundations.StrongApprox.Tusnady

/-!
# Pathwise error bounds in the dyadic tree

Pathwise error bounds. For the recursive tree of `DyadicTree.lean`:
* `Spart_le`: parts (a), (b), (d), (e) combined, `2^n |S_j| ≤ j |e_root| + 2^(n+1) Ψ(j)`;
* `abs_Delta_le`: part (c) (Tusnády);
* `Psi_le`: the deterministic bound of exponential moments along a path, Step 1.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set

namespace ElboimSly
namespace StrongApprox

section Sums

theorem sum_LP (n : ℕ) (m : ℕ) (d : DT n) :
    ∑ i ∈ Finset.range (2 ^ n), LP n m d i = m := by
  induction n generalizing m with
  | zero => simp [LP]
  | succ n ih =>
    rw [pow_succ, mul_two, Finset.sum_range_add]
    have h1 : ∑ i ∈ Finset.range (2 ^ n), LP (n + 1) m d i = saq m d.1 := by
      rw [← ih (saq m d.1) d.2.1]
      refine Finset.sum_congr rfl fun i hi => ?_
      simp [LP, Finset.mem_range.1 hi]
    have h2 : ∑ x ∈ Finset.range (2 ^ n), LP (n + 1) m d (2 ^ n + x) = m - saq m d.1 := by
      rw [← ih (m - saq m d.1) d.2.2]
      refine Finset.sum_congr rfl fun i hi => ?_
      simp [LP]
    rw [h1, h2]
    have := saq_le_m m d.1
    omega

theorem sum_LG (n : ℕ) (g : ℝ) (d : DT n) :
    ∑ i ∈ Finset.range (2 ^ n), LG n g d i = g := by
  induction n generalizing g with
  | zero => simp [LG]
  | succ n ih =>
    rw [pow_succ, mul_two, Finset.sum_range_add]
    have h1 : ∑ i ∈ Finset.range (2 ^ n), LG (n + 1) g d i = gL n g d.1 := by
      rw [← ih (gL n g d.1) d.2.1]
      refine Finset.sum_congr rfl fun i hi => ?_
      simp [LG, Finset.mem_range.1 hi]
    have h2 : ∑ x ∈ Finset.range (2 ^ n), LG (n + 1) g d (2 ^ n + x) = gR n g d.1 := by
      rw [← ih (gR n g d.1) d.2.2]
      refine Finset.sum_congr rfl fun i hi => ?_
      simp [LG]
    rw [h1, h2]
    unfold gL gR
    ring

/-- Pathwise error bounds(a): the error of a node is the sum of the errors of its leaves. -/
theorem Spart_full (n : ℕ) (m : ℕ) (g : ℝ) (d : DT n) :
    Spart n m g d (2 ^ n) = m - 2 ^ n - g := by
  unfold Spart
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
    ← Nat.cast_sum, sum_LP, sum_LG]
  simp

theorem Spart_left (n : ℕ) (m : ℕ) (g : ℝ) (d : DT (n + 1)) {j : ℕ} (hj : j ≤ 2 ^ n) :
    Spart (n + 1) m g d j = Spart n (saq m d.1) (gL n g d.1) d.2.1 j := by
  unfold Spart
  refine Finset.sum_congr rfl fun i hi => ?_
  have : i < 2 ^ n := lt_of_lt_of_le (Finset.mem_range.1 hi) hj
  simp [LP, LG, this]

theorem Spart_right (n : ℕ) (m : ℕ) (g : ℝ) (d : DT (n + 1)) {j : ℕ} (hj : 2 ^ n ≤ j) :
    Spart (n + 1) m g d j = Spart n (saq m d.1) (gL n g d.1) d.2.1 (2 ^ n) +
      Spart n (m - saq m d.1) (gR n g d.1) d.2.2 (j - 2 ^ n) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hj
  rw [Nat.add_sub_cancel_left]
  unfold Spart
  rw [Finset.sum_range_add]
  congr 1
  · refine Finset.sum_congr rfl fun i hi => ?_
    have : i < 2 ^ n := Finset.mem_range.1 hi
    simp [LP, LG, this]
  · refine Finset.sum_congr rfl fun i hi => ?_
    simp [LP, LG]

end Sums

section Path

theorem Psi_nonneg (n : ℕ) (m : ℕ) (d : DT n) (j : ℕ) : 0 ≤ Psi n m d j := by
  induction n generalizing m j with
  | zero => simp [Psi]
  | succ n ih =>
    unfold Psi
    have h1 := ih (saq m d.1) d.2.1 j
    have h2 := ih (m - saq m d.1) d.2.2 (j - 2 ^ n)
    have h3 := abs_nonneg (Delta n m d.1)
    split_ifs <;> linarith

theorem err_left (n : ℕ) (m : ℕ) (g y : ℝ) :
    (saq m y : ℝ) - 2 ^ n - gL n g y = ((m : ℝ) - 2 ^ (n + 1) - g) / 2 + Delta n m y := by
  unfold gL Delta; rw [pow_succ]; ring

theorem err_right (n : ℕ) (m : ℕ) (g y : ℝ) :
    ((m - saq m y : ℕ) : ℝ) - 2 ^ n - gR n g y = ((m : ℝ) - 2 ^ (n + 1) - g) / 2 - Delta n m y := by
  rw [Nat.cast_sub (saq_le_m m y)]
  unfold gR Delta; rw [pow_succ]; ring

/-- Pathwise error bounds(a), (b), (d), (e) in recursive form:
`2^n |S_j| ≤ j |e_root| + 2^(n+1) Ψ(j)` for `0 ≤ j ≤ 2^n`. -/
theorem Spart_le (n : ℕ) (m : ℕ) (g : ℝ) (d : DT n) (j : ℕ) (hj : j ≤ 2 ^ n) :
    (2 : ℝ) ^ n * |Spart n m g d j| ≤
      j * |(m : ℝ) - 2 ^ n - g| + 2 ^ (n + 1) * Psi n m d j := by
  induction n generalizing m g j with
  | zero =>
    have hj' : j = 0 ∨ j = 1 := by omega
    rcases hj' with rfl | rfl
    · simp [Spart, Psi]
    · simp [Spart, Psi, LP, LG]
  | succ n ih =>
    have hT : (0 : ℝ) < 2 ^ n := by positivity
    have hD := abs_nonneg (Delta n m d.1)
    have hPl := Psi_nonneg n (saq m d.1) d.2.1 j
    have hPr := Psi_nonneg n (m - saq m d.1) d.2.2 (j - 2 ^ n)
    have hel : |(saq m d.1 : ℝ) - 2 ^ n - gL n g d.1| ≤
        |(m : ℝ) - 2 ^ (n + 1) - g| / 2 + |Delta n m d.1| := by
      rw [err_left]
      calc _ ≤ |((m : ℝ) - 2 ^ (n + 1) - g) / 2| + |Delta n m d.1| := abs_add_le _ _
        _ = _ := by rw [abs_div]; norm_num
    have her : |((m - saq m d.1 : ℕ) : ℝ) - 2 ^ n - gR n g d.1| ≤
        |(m : ℝ) - 2 ^ (n + 1) - g| / 2 + |Delta n m d.1| := by
      rw [err_right]
      calc _ ≤ |((m : ℝ) - 2 ^ (n + 1) - g) / 2| + |Delta n m d.1| := abs_sub _ _
        _ = _ := by rw [abs_div]; norm_num
    have hpsi : Psi (n + 1) m d j = |Delta n m d.1| +
        if j < 2 ^ n then Psi n (saq m d.1) d.2.1 j
        else Psi n (m - saq m d.1) d.2.2 (j - 2 ^ n) := rfl
    by_cases hlt : j < 2 ^ n
    · rw [hpsi, Spart_left n m g d hlt.le]
      simp only [hlt, ↓reduceIte]
      have h1 := ih (saq m d.1) (gL n g d.1) d.2.1 j hlt.le
      have hJ : (j : ℝ) ≤ 2 ^ n := by exact_mod_cast hlt.le
      have h2 : (j : ℝ) * |Delta n m d.1| ≤ 2 ^ n * |Delta n m d.1| :=
        mul_le_mul_of_nonneg_right hJ hD
      have h3 : (j : ℝ) * |(saq m d.1 : ℝ) - 2 ^ n - gL n g d.1| ≤
          j * (|(m : ℝ) - 2 ^ (n + 1) - g| / 2 + |Delta n m d.1|) :=
        mul_le_mul_of_nonneg_left hel (Nat.cast_nonneg _)
      have e1 : (2 : ℝ) ^ (n + 1) = 2 * 2 ^ n := by ring
      have e2 : (2 : ℝ) ^ (n + 1 + 1) = 4 * 2 ^ n := by ring
      generalize |(m : ℝ) - 2 ^ (n + 1) - g| = E at *
      rw [e1] at h1
      rw [e2, e1]
      nlinarith
    · rw [not_lt] at hlt
      have hn : ¬ j < 2 ^ n := not_lt.2 hlt
      rw [hpsi, Spart_right n m g d hlt]
      simp only [hn, ↓reduceIte]
      have h1 := ih (m - saq m d.1) (gR n g d.1) d.2.2 (j - 2 ^ n) (by omega)
      have hJ : ((j - 2 ^ n : ℕ) : ℝ) ≤ 2 ^ n := by
        have : j - 2 ^ n ≤ 2 ^ n := by omega
        exact_mod_cast this
      have hjj : (j : ℝ) = 2 ^ n + ((j - 2 ^ n : ℕ) : ℝ) := by
        rw [Nat.cast_sub hlt]; push_cast; ring
      have h2 : ((j - 2 ^ n : ℕ) : ℝ) * |Delta n m d.1| ≤ 2 ^ n * |Delta n m d.1| :=
        mul_le_mul_of_nonneg_right hJ hD
      have h3 : ((j - 2 ^ n : ℕ) : ℝ) *
          |((m - saq m d.1 : ℕ) : ℝ) - 2 ^ n - gR n g d.1| ≤
          ((j - 2 ^ n : ℕ) : ℝ) * (|(m : ℝ) - 2 ^ (n + 1) - g| / 2 + |Delta n m d.1|) :=
        mul_le_mul_of_nonneg_left her (Nat.cast_nonneg _)
      have hfull := Spart_full n (saq m d.1) (gL n g d.1) d.2.1
      have h4 : |Spart n (saq m d.1) (gL n g d.1) d.2.1 (2 ^ n) +
          Spart n (m - saq m d.1) (gR n g d.1) d.2.2 (j - 2 ^ n)| ≤
          |(saq m d.1 : ℝ) - 2 ^ n - gL n g d.1| +
            |Spart n (m - saq m d.1) (gR n g d.1) d.2.2 (j - 2 ^ n)| := by
        rw [hfull]; exact abs_add_le _ _
      have h5 : (2 : ℝ) ^ n * |Spart n (saq m d.1) (gL n g d.1) d.2.1 (2 ^ n) +
          Spart n (m - saq m d.1) (gR n g d.1) d.2.2 (j - 2 ^ n)| ≤
          2 ^ n * (|(saq m d.1 : ℝ) - 2 ^ n - gL n g d.1| +
            |Spart n (m - saq m d.1) (gR n g d.1) d.2.2 (j - 2 ^ n)|) :=
        mul_le_mul_of_nonneg_left h4 hT.le
      have h6 : (2 : ℝ) ^ n * |(saq m d.1 : ℝ) - 2 ^ n - gL n g d.1| ≤
          2 ^ n * (|(m : ℝ) - 2 ^ (n + 1) - g| / 2 + |Delta n m d.1|) :=
        mul_le_mul_of_nonneg_left hel hT.le
      have e1 : (2 : ℝ) ^ (n + 1) = 2 * 2 ^ n := by ring
      have e2 : (2 : ℝ) ^ (n + 1 + 1) = 4 * 2 ^ n := by ring
      generalize |(m : ℝ) - 2 ^ (n + 1) - g| = E at *
      rw [e1] at h1
      rw [e2, e1, hjj]
      nlinarith

end Path

section Bounds

/-- Pathwise error bounds(c). -/
theorem abs_Delta_le (n : ℕ) (m : ℕ) (y : ℝ) :
    |Delta n m y| ≤ 2000000000 * (1 + y ^ 2) + 1 / 2 * |√(m : ℝ) - sc n| * |y| := by
  have h := tusnady m y
  have e : Delta n m y = ((saq m y : ℝ) - m / 2 - √(m : ℝ) / 2 * y) +
      1 / 2 * (√(m : ℝ) - sc n) * y := by unfold Delta; ring
  rw [e]
  calc _ ≤ |(saq m y : ℝ) - m / 2 - √(m : ℝ) / 2 * y| + |1 / 2 * (√(m : ℝ) - sc n) * y| :=
        abs_add_le _ _
    _ ≤ _ := by
      rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
      linarith

theorem sq_child (m : ℕ) (n : ℕ) (a : ℝ) :
    (a - √((2 : ℝ) ^ n)) ^ 2 ≤
      3 / 4 * (√(m : ℝ) - √((2 : ℝ) ^ (n + 1))) ^ 2 + 3 * (a - √((m : ℝ) / 2)) ^ 2 := by
  have hm : √(m : ℝ) = √2 * √((m : ℝ) / 2) := by
    rw [← Real.sqrt_mul (by norm_num)]; congr 1; ring
  have hc : √((2 : ℝ) ^ (n + 1)) = √2 * √((2 : ℝ) ^ n) := by
    rw [pow_succ, mul_comm, Real.sqrt_mul (by norm_num)]
  have h2 : √(2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have e : (√(m : ℝ) - √((2 : ℝ) ^ (n + 1))) ^ 2 =
      2 * (√((m : ℝ) / 2) - √((2 : ℝ) ^ n)) ^ 2 := by
    rw [hm, hc]; ring_nf; rw [h2]; ring
  rw [e]
  nlinarith [sq_nonneg (2 * (a - √((m : ℝ) / 2)) - (√((m : ℝ) / 2) - √((2 : ℝ) ^ n)))]

theorem psi_step_alg {CT n y s β S' Θ Ψ' D : ℝ} (hD : D ≤ CT * (1 + y ^ 2) + 1 / 2 * |s| * |y|)
    (hΨ : Ψ' ≤ CT * n + S' ^ 2 + Θ) (hS : S' ^ 2 ≤ 3 / 4 * s ^ 2 + 3 * β ^ 2) :
    D + Ψ' ≤ CT * (n + 1) + s ^ 2 + (3 * β ^ 2 + (CT + 1 / 4) * y ^ 2 + Θ) := by
  have h : |s| * |y| ≤ (s ^ 2 + y ^ 2) / 2 := by
    nlinarith [sq_abs s, sq_abs y, sq_nonneg (|s| - |y|)]
  nlinarith

/-- Exponential moments along a path, Step 1 (deterministic bound):
`Ψ ≤ C_T n + s_n² + Σ (3 β² + c_T η²)` along the path. -/
theorem Psi_le (n : ℕ) (m : ℕ) (d : DT n) (j : ℕ) :
    Psi n m d j ≤ 2000000000 * n + (√(m : ℝ) - √((2 : ℝ) ^ n)) ^ 2 + Theta n m d j := by
  induction n generalizing m j with
  | zero => simp only [Psi, Theta]; push_cast; nlinarith [sq_nonneg (√(m : ℝ) - √((2 : ℝ) ^ 0))]
  | succ n ih =>
    have hcT : cT = 2000000000 + 1 / 4 := rfl
    have hD := abs_Delta_le n m d.1
    have hsc : sc n = √((2 : ℝ) ^ (n + 1)) := rfl
    rw [hsc] at hD
    by_cases hlt : j < 2 ^ n
    · have h1 := ih (saq m d.1) d.2.1 j
      have h2 := sq_child m n (√((saq m d.1 : ℕ) : ℝ))
      have := psi_step_alg (CT := 2000000000) (n := (n : ℝ)) hD h1 h2
      simp only [Psi, Theta, hlt, ↓reduceIte, hcT]
      push_cast
      linarith
    · have h1 := ih (m - saq m d.1) d.2.2 (j - 2 ^ n)
      have h2 := sq_child m n (√((m - saq m d.1 : ℕ) : ℝ))
      have := psi_step_alg (CT := 2000000000) (n := (n : ℝ)) hD h1 h2
      simp only [Psi, Theta, hlt, ↓reduceIte, hcT]
      push_cast
      linarith

end Bounds

end StrongApprox
end ElboimSly
