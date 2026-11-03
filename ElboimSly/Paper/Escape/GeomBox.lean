/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Escape.GeomBase
public import Mathlib

/-!
# Geometry of the curve: staying inside `B^-`

Geometry of the curve (b), the convexity step: a lattice point within `θ (a/4 - 1)` of
`p + θ (q - p)`, for `p` in the real box of `B^-`, lies in `B^-`.
-/

@[expose] public section

namespace ElboimSly.Paper

variable {k : ℕ}

/-- The real box of `B^-` contains `p`. -/
def EscRealBox (j : ℕ) (u : Fin (k + 2) → ℤ) (p : Fin (k + 2) → ℝ) : Prop :=
  ((u 0 : ℝ) ≤ p 0 ∧ p 0 ≤ u 0 + (2 : ℝ) ^ j / 2 - 1) ∧
    ∀ c, c ≠ 0 → ((u c : ℝ) ≤ p c ∧ p c ≤ u c + (2 : ℝ) ^ j - 1)

lemma escRealBox_cast {j : ℕ} {u : Fin (k + 2) → ℤ} {y : Fin (k + 2) → ℤ} (hj : 4 ≤ j)
    (hy : y ∈ escBlockMinus j u) : EscRealBox j u (escCast y) := by
  have hh := cast_two_pow_pred (by omega : 1 ≤ j)
  refine ⟨⟨?_, ?_⟩, fun c hc => ⟨?_, ?_⟩⟩
  · simp only [escCast]; exact_mod_cast hy.1.1
  · have : y 0 + 1 ≤ u 0 + 2 ^ (j - 1) := hy.1.2
    have h2 : (y 0 : ℝ) + 1 ≤ u 0 + (2 : ℝ) ^ j / 2 := by rw [← hh]; exact_mod_cast this
    simp only [escCast]; linarith
  · simp only [escCast]; exact_mod_cast (hy.2 c hc).1
  · have : y c + 1 ≤ u c + 2 ^ j := (hy.2 c hc).2
    have h2 : (y c : ℝ) + 1 ≤ u c + (2 : ℝ) ^ j := by exact_mod_cast this
    simp only [escCast]; linarith

theorem mem_blockMinus_of_margin {j : ℕ} {u : Fin (k + 2) → ℤ} (hj : 4 ≤ j)
    {p : Fin (k + 2) → ℝ} (hp : EscRealBox j u p) {θ R : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hR : R ≤ θ * ((2 : ℝ) ^ j / 4 - 1)) {y : Fin (k + 2) → ℤ}
    (hy : ‖escCast y - (p + θ • (escCentre j u - p))‖ ≤ R) : y ∈ escBlockMinus j u := by
  have ha : (16 : ℝ) ≤ (2 : ℝ) ^ j :=
    calc (16 : ℝ) = 2 ^ 4 := by norm_num
      _ ≤ 2 ^ j := pow_le_pow_right₀ (by norm_num) hj
  set a : ℝ := (2 : ℝ) ^ j with ha'
  have hh := cast_two_pow_pred (by omega : 1 ≤ j)
  have hcoord : ∀ c, |(y c : ℝ) - (p c + θ * (escCentre j u c - p c))| ≤ R := fun c => by
    have := norm_le_pi_norm (escCast y - (p + θ • (escCentre j u - p))) c
    simpa [escCast, Real.norm_eq_abs] using this.trans hy
  have hθa : 0 ≤ θ * (a / 4 - 1) := mul_nonneg hθ0 (by linarith)
  refine ⟨⟨?_, ?_⟩, fun c hc => ⟨?_, ?_⟩⟩
  · have h1 := hcoord 0
    rw [abs_le] at h1
    have q0' := EscGeom.q0 (j := j) (u := u)
    have := mul_nonneg (by linarith : 0 ≤ 1 - θ) (sub_nonneg.2 hp.1.1)
    have h4 : (u 0 : ℝ) ≤ y 0 := by nlinarith [h1.1, h1.2, hp.1.1, hp.1.2]
    exact_mod_cast h4
  · have h1 := hcoord 0
    rw [abs_le] at h1
    have q0' := EscGeom.q0 (j := j) (u := u)
    have := mul_nonneg (by linarith : 0 ≤ 1 - θ) (sub_nonneg.2 hp.1.2)
    have h4 : (y 0 : ℝ) + 1 ≤ u 0 + a / 2 := by nlinarith [h1.1, h1.2, hp.1.1, hp.1.2]
    have h5 : y 0 + 1 ≤ u 0 + 2 ^ (j - 1) := by
      have hpow : (2 : ℝ) ^ (j - 1) = a / 2 := by
        obtain ⟨i, hi⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
        rw [ha', hi]; simp [pow_succ]
      have : ((y 0 + 1 : ℤ) : ℝ) ≤ ((u 0 + 2 ^ (j - 1) : ℤ) : ℝ) := by
        push_cast; rw [hpow]; linarith
      exact_mod_cast this
    omega
  · have h1 := hcoord c
    rw [abs_le] at h1
    have qc' := EscGeom.qc (j := j) (u := u) hc
    have := mul_nonneg (by linarith : 0 ≤ 1 - θ) (sub_nonneg.2 (hp.2 c hc).1)
    have h4 : (u c : ℝ) ≤ y c := by nlinarith [h1.1, h1.2, (hp.2 c hc).1, (hp.2 c hc).2]
    exact_mod_cast h4
  · have h1 := hcoord c
    rw [abs_le] at h1
    have qc' := EscGeom.qc (j := j) (u := u) hc
    have := mul_nonneg (by linarith : 0 ≤ 1 - θ) (sub_nonneg.2 (hp.2 c hc).2)
    have h4 : (y c : ℝ) + 1 ≤ u c + a := by nlinarith [h1.1, h1.2, (hp.2 c hc).1, (hp.2 c hc).2]
    have : ((y c + 1 : ℤ) : ℝ) ≤ ((u c + 2 ^ j : ℤ) : ℝ) := by push_cast; linarith
    have := (by exact_mod_cast this : y c + 1 ≤ u c + 2 ^ j)
    omega

end ElboimSly.Paper
