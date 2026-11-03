/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.SRW.Levy
public import ElboimSly.Foundations.SRW.Chernoff
public import Mathlib

/-!
# The maximal inequality

Maximal inequality.  For every SRW `X` in dimension `d ≥ 1`, `T > 0` and `a ≥ 0`,
`P(∃ s ≤ T, ‖X(s)‖ ≥ a) ≤ 4 d exp(-min{a²/(8T), a/2})`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ElboimSly
namespace SRW

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {Z : Ω → PathSpace d}

/-- The sup norm of an integer vector is at least `a ≥ 0` iff some coordinate is. -/
theorem exists_coord_of_norm_ge [NeZero d] {x : Fin d → ℤ} {a : ℝ} (ha : 0 ≤ a)
    (h : a ≤ ‖x‖) : ∃ i, a ≤ |(x i : ℝ)| := by
  by_contra hcon
  push Not at hcon
  rcases ha.eq_or_lt with rfl | hpos
  · obtain ⟨i⟩ : Nonempty (Fin d) := ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩⟩
    exact absurd (hcon i) (not_lt.2 (abs_nonneg _))
  · have : ‖x‖ < a := (pi_norm_lt_iff hpos).2 fun i => by
      rw [Int.norm_eq_abs]; exact hcon i
    linarith

/-- Maximal inequality. -/
theorem IsSRW.maximal [NeZero d] (hZ : IsSRW P Z) {T : ℝ≥0} (hT : 0 < T) {a : ℝ} (ha : 0 ≤ a) :
    P.real {ω | ∃ s, s ≤ T ∧ a ≤ ‖Z ω s‖} ≤
      4 * d * Real.exp (-min (a ^ 2 / (8 * T)) (a / 2)) := by
  have := hZ.isProbabilityMeasure
  have hsub : {ω | ∃ s, s ≤ T ∧ a ≤ ‖Z ω s‖} ⊆
      ⋃ i : Fin d, {ω | ∃ s, s ≤ T ∧ a ≤ |((fun s (_ : Fin 1) => Z ω s i) s 0 : ℝ)|} := by
    intro ω ⟨s, hs, h⟩
    obtain ⟨i, hi⟩ := exists_coord_of_norm_ge ha h
    exact mem_iUnion.2 ⟨i, s, hs, hi⟩
  have hi : ∀ i : Fin d, P.real {ω | ∃ s, s ≤ T ∧
      a ≤ |(((fun ω s (_ : Fin 1) => Z ω s i) ω s 0 : ℤ) : ℝ)|} ≤
      4 * Real.exp (-min (a ^ 2 / (8 * T)) (a / 2)) := by
    intro i
    have hY := hZ.coord i
    refine (hY.levy_abs T a).trans ?_
    have := hY.chernoff_abs hT ha
    linarith
  calc P.real {ω | ∃ s, s ≤ T ∧ a ≤ ‖Z ω s‖}
      ≤ P.real (⋃ i : Fin d, {ω | ∃ s, s ≤ T ∧
          a ≤ |(((fun ω s (_ : Fin 1) => Z ω s i) ω s 0 : ℤ) : ℝ)|}) :=
        measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ ∑ i : Fin d, P.real {ω | ∃ s, s ≤ T ∧
          a ≤ |(((fun ω s (_ : Fin 1) => Z ω s i) ω s 0 : ℤ) : ℝ)|} :=
        measureReal_iUnion_fintype_le _
    _ ≤ ∑ _i : Fin d, 4 * Real.exp (-min (a ^ 2 / (8 * T)) (a / 2)) :=
        Finset.sum_le_sum fun i _ => hi i
    _ = 4 * d * Real.exp (-min (a ^ 2 / (8 * T)) (a / 2)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

/-- Maximal inequality, the Gaussian regime `a = λ √T`, `0 ≤ λ ≤ 4√T`. -/
theorem IsSRW.maximal_gauss [NeZero d] (hZ : IsSRW P Z) {T : ℝ≥0} (hT : 0 < T) {lam : ℝ}
    (h0 : 0 ≤ lam) (h1 : lam ≤ 4 * √T) :
    P.real {ω | ∃ s, s ≤ T ∧ lam * √T ≤ ‖Z ω s‖} ≤ 4 * d * Real.exp (-(lam ^ 2 / 8)) := by
  have hT' : (0 : ℝ) < T := hT
  have hs : (0 : ℝ) < √T := Real.sqrt_pos.2 hT'
  have hsq : √T ^ 2 = T := Real.sq_sqrt hT'.le
  have := hZ.maximal hT (a := lam * √T) (by positivity)
  refine this.trans (le_of_eq ?_)
  have hm : min ((lam * √T) ^ 2 / (8 * T)) (lam * √T / 2) = lam ^ 2 / 8 := by
    have e : (lam * √T) ^ 2 / (8 * T) = lam ^ 2 / 8 := by
      rw [mul_pow, hsq]; field_simp
    rw [e]
    apply min_eq_left
    have : lam ^ 2 / 8 = lam / 2 * (lam / 4) := by ring
    rw [this]
    have h3 : lam / 4 ≤ √T := by linarith
    calc lam / 2 * (lam / 4) ≤ lam / 2 * √T := by gcongr
      _ = lam * √T / 2 := by ring
  rw [hm]

/-- Maximal inequality, the exponential regime `a ≥ 4T`. -/
theorem IsSRW.maximal_exp [NeZero d] (hZ : IsSRW P Z) {T : ℝ≥0} (hT : 0 < T) {a : ℝ}
    (h : 4 * (T : ℝ) ≤ a) :
    P.real {ω | ∃ s, s ≤ T ∧ a ≤ ‖Z ω s‖} ≤ 4 * d * Real.exp (-(a / 2)) := by
  have hT' : (0 : ℝ) < T := hT
  have := hZ.maximal hT (a := a) (by linarith)
  refine this.trans (le_of_eq ?_)
  have hm : min (a ^ 2 / (8 * T)) (a / 2) = a / 2 := by
    apply min_eq_right
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  rw [hm]

end SRW
end ElboimSly
