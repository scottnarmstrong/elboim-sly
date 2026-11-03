/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Escape.Phases
public import Mathlib

/-!
# Geometry of the curve: coordinates of `v`, `z`, `q`

Geometry of the curve, first sentence (`‖q-v‖ ∈ [a/4,a/2]`, `‖q-w‖ ∈ [a/4-1,a/4]`), and the
coordinate bounds used throughout.  Here `a = 2^j`, `v ∈ ∂B ∩ B^-`, `z ∈ F_B` (the point `w`
of the written proof).
-/

@[expose] public section

namespace ElboimSly.Paper

variable {k : ℕ}

/-- The data of Claim 5.6 for the geometry: `v ∈ ∂B ∩ B^-`, `w = z ∈ F_B`, `j ≥ 6`. -/
structure EscGeom (j : ℕ) (u v z : Fin (k + 2) → ℤ) : Prop where
  hj : 6 ≤ j
  hv : v ∈ escBoundary j u
  hvm : v ∈ escBlockMinus j u
  hz : z ∈ escFace j u

lemma cast_two_pow_pred {j : ℕ} (hj : 1 ≤ j) : (((2 : ℤ) ^ (j - 1) : ℤ) : ℝ) = (2 : ℝ) ^ j / 2 := by
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  push_cast; rw [pow_succ]; simp

lemma cast_two_pow_div_four {j : ℕ} (hj : 2 ≤ j) :
    ((((2 : ℤ) ^ j / 4 : ℤ)) : ℝ) = (2 : ℝ) ^ j / 4 := by
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 2 := ⟨j - 2, by omega⟩
  have : (2 : ℤ) ^ (i + 2) = 4 * 2 ^ i := by rw [pow_add]; ring
  rw [this, Int.mul_ediv_cancel_left _ (by norm_num)]
  push_cast; rw [pow_add]; ring

namespace EscGeom

variable {j : ℕ} {u v z : Fin (k + 2) → ℤ}

lemma a_ge (h : EscGeom j u v z) : (64 : ℝ) ≤ (2 : ℝ) ^ j := by
  calc (64 : ℝ) = 2 ^ 6 := by norm_num
    _ ≤ 2 ^ j := pow_le_pow_right₀ (by norm_num) h.hj

lemma hj4 (h : EscGeom j u v z) : 4 ≤ j := by have := h.hj; omega

lemma v0 (h : EscGeom j u v z) :
    (u 0 : ℝ) ≤ v 0 ∧ (v 0 : ℝ) ≤ u 0 + (2 : ℝ) ^ j / 2 - 1 := by
  have := h.hvm.1
  have hh := cast_two_pow_pred (by linarith [h.hj] : 1 ≤ j)
  constructor
  · exact_mod_cast this.1
  · have : v 0 < u 0 + 2 ^ (j - 1) := this.2
    have : v 0 + 1 ≤ u 0 + 2 ^ (j - 1) := this
    have h2 : (v 0 : ℝ) + 1 ≤ u 0 + (2 : ℝ) ^ j / 2 := by
      rw [← hh]; exact_mod_cast this
    linarith

lemma vc (h : EscGeom j u v z) {c : Fin (k + 2)} (hc : c ≠ 0) :
    (u c : ℝ) ≤ v c ∧ (v c : ℝ) ≤ u c + (2 : ℝ) ^ j - 1 := by
  have := h.hvm.2 c hc
  constructor
  · exact_mod_cast this.1
  · have : v c + 1 ≤ u c + 2 ^ j := this.2
    have h2 : (v c : ℝ) + 1 ≤ u c + (2 : ℝ) ^ j := by exact_mod_cast this
    linarith

lemma z0 (h : EscGeom j u v z) : (z 0 : ℝ) = u 0 + (2 : ℝ) ^ j / 2 - 1 := by
  have := h.hz.1
  have hh := cast_two_pow_pred (by linarith [h.hj] : 1 ≤ j)
  have : (z 0 : ℝ) = ((u 0 + 2 ^ (j - 1) - 1 : ℤ) : ℝ) := by rw [this]
  rw [this]; have h3 := hh; push_cast at h3 ⊢; linarith

lemma zc (h : EscGeom j u v z) {c : Fin (k + 2)} (hc : c ≠ 0) :
    (u c : ℝ) + (2 : ℝ) ^ j / 4 ≤ z c ∧ (z c : ℝ) ≤ u c + 3 * ((2 : ℝ) ^ j / 4) := by
  have := h.hz.2 c hc
  have hh := cast_two_pow_div_four (by linarith [h.hj] : 2 ≤ j)
  constructor
  · have : ((u c + 2 ^ j / 4 : ℤ) : ℝ) ≤ z c := by exact_mod_cast this.1
    push_cast at this; rw [hh] at this; exact this
  · have : (z c : ℝ) ≤ ((u c + 3 * (2 ^ j / 4) : ℤ) : ℝ) := by exact_mod_cast this.2
    push_cast at this; rw [hh] at this; exact this

lemma q0 : escCentre j u 0 = u 0 + (2 : ℝ) ^ j / 4 := by
  simp [escCentre]

lemma qc {c : Fin (k + 2)} (hc : c ≠ 0) : escCentre j u c = u c + (2 : ℝ) ^ j / 2 := by
  simp [escCentre, hc]; ring

/-- A boundary vertex of `B^-` touches a face of the block (other than the half-block face). -/
lemma boundary_cases (h : EscGeom j u v z) :
    v 0 = u 0 ∨ ∃ c, c ≠ 0 ∧ (v c = u c ∨ v c = u c + 2 ^ j - 1) := by
  obtain ⟨-, c, s, hs, hout⟩ := h.hv
  have hin : ∀ c', u c' ≤ v c' ∧ v c' < u c' + 2 ^ j := h.hv.1
  by_cases hc0 : c = 0
  · subst hc0
    left
    have hnot : ¬ ∀ c', u c' ≤ Function.update v 0 (v 0 + s) c' ∧
        Function.update v 0 (v 0 + s) c' < u c' + 2 ^ j := hout
    push Not at hnot
    obtain ⟨c', hc'⟩ := hnot
    by_cases e : c' = 0
    · subst e
      simp at hc'
      have h1 := (hin 0)
      have hv0 : v 0 < u 0 + 2 ^ (j - 1) := h.hvm.1.2
      have : (2 : ℤ) ^ (j - 1) < 2 ^ j := pow_lt_pow_right₀ (by norm_num) (by have := h.hj; omega)
      rcases hs with rfl | rfl <;> omega
    · simp [e] at hc'
      exact absurd (hin c') (by intro hh; have := hc' hh.1; omega)
  · right
    refine ⟨c, hc0, ?_⟩
    have hnot : ¬ ∀ c', u c' ≤ Function.update v c (v c + s) c' ∧
        Function.update v c (v c + s) c' < u c' + 2 ^ j := hout
    push Not at hnot
    obtain ⟨c', hc'⟩ := hnot
    by_cases e : c' = c
    · subst e
      simp at hc'
      have h1 := (hin c')
      rcases hs with rfl | rfl
      · right; omega
      · left; omega
    · simp [e] at hc'
      exact absurd (hin c') (by intro hh; have := hc' hh.1; omega)

lemma norm_qv_le (h : EscGeom j u v z) : ‖escCentre j u - escCast v‖ ≤ (2 : ℝ) ^ j / 2 := by
  have ha := h.a_ge
  refine (pi_norm_le_iff_of_nonneg (by linarith)).2 fun c => ?_
  rw [Real.norm_eq_abs, abs_le]
  by_cases hc : c = 0
  · subst hc
    have := h.v0
    simp only [Pi.sub_apply, escCast, q0]
    constructor <;> linarith [this.1, this.2]
  · have := h.vc hc
    simp only [Pi.sub_apply, escCast, qc hc]
    constructor <;> linarith [this.1, this.2]

lemma norm_qv_ge (h : EscGeom j u v z) : (2 : ℝ) ^ j / 4 ≤ ‖escCentre j u - escCast v‖ := by
  have ha := h.a_ge
  rcases h.boundary_cases with h0 | ⟨c, hc, hcc⟩
  · refine le_trans ?_ (norm_le_pi_norm (escCentre j u - escCast v) 0)
    simp only [Pi.sub_apply, escCast, q0, h0, Real.norm_eq_abs]
    rw [abs_of_nonneg (by linarith)]; linarith
  · refine le_trans ?_ (norm_le_pi_norm (escCentre j u - escCast v) c)
    simp only [Pi.sub_apply, escCast, qc hc, Real.norm_eq_abs]
    rcases hcc with e | e
    · rw [e]; rw [abs_of_nonneg (by linarith)]; linarith
    · rw [e]; push_cast
      rw [abs_of_nonpos (by linarith)]; linarith

lemma norm_qz_le (h : EscGeom j u v z) : ‖escCentre j u - escCast z‖ ≤ (2 : ℝ) ^ j / 4 := by
  have ha := h.a_ge
  refine (pi_norm_le_iff_of_nonneg (by linarith)).2 fun c => ?_
  rw [Real.norm_eq_abs, abs_le]
  by_cases hc : c = 0
  · subst hc
    simp only [Pi.sub_apply, escCast, q0, h.z0]
    constructor <;> linarith
  · have := h.zc hc
    simp only [Pi.sub_apply, escCast, qc hc]
    constructor <;> linarith [this.1, this.2]

lemma norm_qz_ge (h : EscGeom j u v z) : (2 : ℝ) ^ j / 4 - 1 ≤ ‖escCentre j u - escCast z‖ := by
  have ha := h.a_ge
  refine le_trans ?_ (norm_le_pi_norm (escCentre j u - escCast z) 0)
  simp only [Pi.sub_apply, escCast, q0, h.z0, Real.norm_eq_abs]
  rw [abs_of_nonpos (by linarith)]; linarith

/-- Geometry of the curve (a), Transversality. -/
theorem transversality (h : EscGeom j u v z) {x y : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) (hy : 0 ≤ y)
    (_hy1 : y ≤ 1) :
    max x y * ((2 : ℝ) ^ j / 12 - 1) ≤
      ‖x • (escCast z - escCentre j u) - y • (escCast v - escCentre j u)‖ := by
  have ha := h.a_ge
  set a : ℝ := (2 : ℝ) ^ j with ha'
  have hz0 : (escCast z - escCentre j u) 0 = a / 4 - 1 := by
    simp only [Pi.sub_apply, escCast, q0, h.z0]; linarith
  have hv0 : (escCast v - escCentre j u) 0 ≤ a / 4 - 1 := by
    simp only [Pi.sub_apply, escCast, q0]; linarith [h.v0.2]
  have key : ∀ i : Fin (k + 2),
      |(x • (escCast z - escCentre j u) - y • (escCast v - escCentre j u)) i| ≤
      ‖x • (escCast z - escCentre j u) - y • (escCast v - escCentre j u)‖ := fun i => by
    simpa [Real.norm_eq_abs] using norm_le_pi_norm
      (x • (escCast z - escCentre j u) - y • (escCast v - escCentre j u)) i
  rcases h.boundary_cases with h0 | ⟨c, hc, hcc⟩
  · have e : (escCast v - escCentre j u) 0 = -(a / 4) := by
      simp only [Pi.sub_apply, escCast, q0, h0]; ring
    refine le_trans ?_ (key 0)
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [show (escCast z 0 - escCentre j u 0) = a / 4 - 1 from hz0,
      show (escCast v 0 - escCentre j u 0) = -(a / 4) from e]
    rw [abs_of_nonneg (by nlinarith)]
    rcases le_total x y with hxy | hxy
    · rw [max_eq_right hxy]; nlinarith
    · rw [max_eq_left hxy]; nlinarith
  · have hr : a / 2 - 1 ≤ |(escCast v - escCentre j u) c| := by
      simp only [Pi.sub_apply, escCast, qc hc]
      rcases hcc with e | e
      · rw [e]; rw [abs_of_nonpos (by linarith)]; linarith
      · rw [e]; push_cast; rw [abs_of_nonneg (by linarith)]; linarith
    have hζ : |(escCast z - escCentre j u) c| ≤ a / 4 := by
      have := h.zc hc
      simp only [Pi.sub_apply, escCast, qc hc]
      rw [abs_le]; constructor <;> linarith [this.1, this.2]
    set r := (escCast v - escCentre j u) c
    set ζ := (escCast z - escCentre j u) c
    have h1 : |y * r| - |x * ζ| ≤ |x * ζ - y * r| := by
      rw [abs_sub_comm]; exact abs_sub_abs_le_abs_sub _ _
    have h2 : y * (a / 2 - 1) ≤ |y * r| := by
      rw [abs_mul, abs_of_nonneg hy]; exact mul_le_mul_of_nonneg_left hr hy
    have h3 : |x * ζ| ≤ x * (a / 4) := by
      rw [abs_mul, abs_of_nonneg hx]; exact mul_le_mul_of_nonneg_left hζ hx
    have hcoord : y * (a / 2 - 1) - x * (a / 4) ≤
        |(x • (escCast z - escCentre j u) - y • (escCast v - escCentre j u)) c| := by
      show _ ≤ |x * ζ - y * r|
      linarith
    by_cases hxy : x ≤ y
    · refine le_trans ?_ ((hcoord).trans (key c))
      rw [max_eq_right hxy]
      nlinarith [mul_le_mul_of_nonneg_right hxy (by linarith : (0 : ℝ) ≤ a / 4)]
    · push Not at hxy
      by_cases hy2 : 2 * x / 3 ≤ y
      · refine le_trans ?_ ((hcoord).trans (key c))
        rw [max_eq_left hxy.le]
        nlinarith [mul_le_mul_of_nonneg_right hy2 (by linarith : (0 : ℝ) ≤ a / 2 - 1)]
      · push Not at hy2
        refine le_trans ?_ (key 0)
        simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        rw [show (escCast z 0 - escCentre j u 0) = a / 4 - 1 from hz0]
        have hv0' : (escCast v 0 - escCentre j u 0) ≤ a / 4 - 1 := hv0
        have : y * (escCast v 0 - escCentre j u 0) ≤ y * (a / 4 - 1) :=
          mul_le_mul_of_nonneg_left hv0' hy
        refine le_trans ?_ (le_abs_self _)
        rw [max_eq_left hxy.le]
        nlinarith

end EscGeom

end ElboimSly.Paper
