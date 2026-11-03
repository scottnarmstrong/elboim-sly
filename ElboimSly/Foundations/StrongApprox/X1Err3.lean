/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.StrongApprox.X1Err2
public import Mathlib

/-!
# The coupling error

The coupling error (Part II).

For `ℓ ≥ 2` and `1 ≤ γ ≤ 2ℓ`,
`P(∃ j, ‖∑_{i ≤ j} (X_i - Y_i)‖ ≥ 59 M ℓ^{1/4} γ^{3/4}) ≤ 10 d ℓ e^{-γ}`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace ElboimSly.StrongApprox

open ElboimSly.Brownian

lemma Lambda_lt_thr {M ℓ γ : ℝ} (hM : 1 ≤ M) (hℓ : 1 ≤ ℓ) (hγ : 1 ≤ γ) :
    4 * Real.sqrt (215 * M ^ 2 * Real.sqrt (ℓ * γ) * γ) <
      59 * M * ℓ ^ (1 / 4 : ℝ) * γ ^ (3 / 4 : ℝ) := by
  have hℓ0 : 0 < ℓ := by linarith
  have hγ0 : 0 < γ := by linarith
  set a : ℝ := ℓ ^ (1 / 4 : ℝ) with ha
  set b : ℝ := γ ^ (3 / 4 : ℝ) with hb
  have ha0 : 0 < a := Real.rpow_pos_of_pos hℓ0 _
  have hb0 : 0 < b := Real.rpow_pos_of_pos hγ0 _
  have ha2 : a ^ 2 = Real.sqrt ℓ := by
    rw [ha, ← Real.rpow_natCast, ← Real.rpow_mul hℓ0.le, Real.sqrt_eq_rpow]; norm_num
  have hb2 : b ^ 2 = γ * Real.sqrt γ := by
    rw [hb, ← Real.rpow_natCast, ← Real.rpow_mul hγ0.le, Real.sqrt_eq_rpow]
    have h1 : γ * γ ^ (1 / 2 : ℝ) = γ ^ ((1 : ℝ) + 1 / 2) := by
      rw [Real.rpow_add hγ0, Real.rpow_one]
    rw [h1]; norm_num
  set X : ℝ := M * a * b with hX
  have hX0 : 0 < X := by positivity
  have hin : 215 * M ^ 2 * Real.sqrt (ℓ * γ) * γ = 215 * X ^ 2 := by
    rw [hX, mul_pow, mul_pow, ha2, hb2, Real.sqrt_mul hℓ0.le]
    ring
  rw [hin, Real.sqrt_mul (by norm_num), Real.sqrt_sq hX0.le]
  have : 59 * M * a * b = 59 * X := by rw [hX]; ring
  rw [this]
  have h215 : Real.sqrt 215 < 59 / 4 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  nlinarith

variable {d ℓ : ℕ}

/-- The coupling error. -/
theorem tail_general (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ] (hℓ : 2 ≤ ℓ) {M : ℝ}
    (hM : 1 ≤ M) (hμM : μ {x | ‖x‖ ≤ M} = 1) (hsq : ∀ k, ∫ x, x k ^ 2 ∂μ = 1) {γ : ℝ}
    (hγ1 : 1 ≤ γ) (hγ : γ ≤ 2 * ℓ) :
    (P1 d ℓ (μ.map absVec)) {ω | ∃ j : Fin ℓ,
        59 * M * (ℓ : ℝ) ^ (1 / 4 : ℝ) * γ ^ (3 / 4 : ℝ) ≤ ‖x1Spart ω j‖} ≤
      ENNReal.ofReal (10 * d * ℓ * Real.exp (-γ)) := by
  have : IsProbabilityMeasure (μ.map absVec) :=
    (Measure.isProbabilityMeasure_map_iff (measurable_absVec d).aemeasurable).2 inferInstance
  have hlam0 : ∀ᵐ x ∂(μ.map absVec), ∀ k, 0 ≤ x k :=
    (ae_lam_bound μ hμM).mono fun x hx k => (hx k).1
  have hℓR : (2 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hγ0 : 0 < γ := by linarith
  set D : ℝ := 215 * M ^ 2 * Real.sqrt (ℓ * γ) with hD
  set Λ : ℝ := 4 * Real.sqrt (D * γ) with hΛ
  have hsqrt1 : 1 ≤ Real.sqrt (ℓ * γ) := by
    rw [Real.one_le_sqrt]; nlinarith
  have hD1 : 1 ≤ D := by
    have : 1 ≤ M ^ 2 := one_le_pow₀ hM
    rw [hD]; nlinarith
  have hD0 : 0 ≤ D := by linarith
  have hDγ : 0 < D * γ := by positivity
  have hΛ0 : 0 < Λ := by rw [hΛ]; positivity
  have hΛthr : Λ < 59 * M * (ℓ : ℝ) ^ (1 / 4 : ℝ) * γ ^ (3 / 4 : ℝ) :=
    Lambda_lt_thr hM (by linarith) hγ1
  set D' : ℝ≥0 := D.toNNReal with hD'
  have hD'R : (D' : ℝ) = D := Real.coe_toNNReal _ hD0
  have hD'1 : 1 ≤ D' := by rw [← NNReal.coe_le_coe, hD'R]; simpa using hD1
  have hD'0 : D' ≠ 0 := by intro h; rw [h] at hD'1; simp at hD'1
  -- the inclusion
  have hsub : {ω | ∃ j : Fin ℓ, 59 * M * (ℓ : ℝ) ^ (1 / 4 : ℝ) * γ ^ (3 / 4 : ℝ) ≤ ‖x1Spart ω j‖} ⊆
      ({ω : Ω1 d ℓ | ¬ ∀ k i, Tp k (Vfull ℓ ω) i < ⊤} ∪ ⋃ k : Fin d, ClockEvent D k) ∪
        OscEvent ((ℓ : ℝ≥0) + D') D' Λ := by
    intro ω hω
    by_contra hcon
    simp only [Set.mem_union, Set.mem_iUnion, not_or] at hcon
    obtain ⟨⟨hG0, hC⟩, hO⟩ := hcon
    obtain ⟨j, hj⟩ := hω
    have hG0' : ∀ k i, Tp k (Vfull ℓ ω) i < ⊤ := by
      by_contra h; exact hG0 h
    have := x1Spart_norm_lt hD0 hΛ0 ω hG0' (fun k hk => hC ⟨k, hk⟩) hO j
    linarith
  have hP0 : (P1 d ℓ (μ.map absVec)) {ω : Ω1 d ℓ | ¬ ∀ k i, Tp k (Vfull ℓ ω) i < ⊤} = 0 := by
    have := ae_Tcoord_lt_top (μ.map absVec) hlam0 (ℓ := ℓ)
    rwa [ae_iff] at this
  have hPC : (P1 d ℓ (μ.map absVec)) (⋃ k : Fin d, ClockEvent D k) ≤
      ENNReal.ofReal (d * (2 * ℓ * Real.exp (-γ))) := by
    refine (measure_iUnion_fintype_le _ _).trans ?_
    calc ∑ k : Fin d, (P1 d ℓ (μ.map absVec)) (ClockEvent D k)
        ≤ ∑ _k : Fin d, ENNReal.ofReal (2 * ℓ * Real.exp (-γ)) :=
          Finset.sum_le_sum fun k _ =>
            chernoff_clocks_event (by omega) hM hμM hsq hγ0 hγ k
      _ = ENNReal.ofReal (d * (2 * ℓ * Real.exp (-γ))) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            ← ENNReal.ofReal_natCast d, ← ENNReal.ofReal_mul (by positivity)]
  have hPO : (P1 d ℓ (μ.map absVec)) (OscEvent ((ℓ : ℝ≥0) + D') D' Λ) ≤
      ENNReal.ofReal (8 * d * ℓ * Real.exp (-γ)) := by
    have hT : ((ℓ : ℝ≥0) + D') ≠ 0 := by
      intro h
      have : (1 : ℝ≥0) ≤ (ℓ : ℝ≥0) + D' := le_add_left hD'1
      rw [h] at this; simp at this
    have hosc := (isStandardBM_Bd d).oscillation_le (T := (ℓ : ℝ≥0) + D') (h := D') hT hD'0
      (l := Λ) (σ := 1) hΛ0 one_pos
    have hsnd : (P1 d ℓ (μ.map absVec)).map Prod.snd = PB d := by
      rw [P1, Measure.map_snd_prod]; simp
    have hle : (P1 d ℓ (μ.map absVec)) (OscEvent ((ℓ : ℝ≥0) + D') D' Λ) ≤
        PB d {ωB | ∃ s s' : ℝ≥0, s ≤ (ℓ : ℝ≥0) + D' ∧ s' ≤ (ℓ : ℝ≥0) + D' ∧ dist s s' ≤ D' ∧
          Λ ≤ ‖(1 : ℝ) • Bd d s ωB - (1 : ℝ) • Bd d s' ωB‖} := by
      have := Measure.le_map_apply (μ := P1 d ℓ (μ.map absVec)) (f := Prod.snd)
        measurable_snd.aemeasurable
        {ωB | ∃ s s' : ℝ≥0, s ≤ (ℓ : ℝ≥0) + D' ∧ s' ≤ (ℓ : ℝ≥0) + D' ∧ dist s s' ≤ D' ∧
          Λ ≤ ‖(1 : ℝ) • Bd d s ωB - (1 : ℝ) • Bd d s' ωB‖}
      rw [hsnd] at this
      exact this
    refine hle.trans (hosc.trans ?_)
    have hexp : -Λ ^ 2 / (16 * (1 : ℝ) ^ 2 * (D' : ℝ)) = -γ := by
      have hΛ2 : Λ ^ 2 = 16 * (D * γ) := by
        rw [hΛ, mul_pow, Real.sq_sqrt hDγ.le]; ring
      rw [hD'R, hΛ2]
      field_simp
    rw [hexp]
    have hceil : ⌈((ℓ : ℝ≥0) + D') / D'⌉₊ ≤ ℓ + 1 := by
      rw [Nat.ceil_le]
      rw [div_le_iff₀ (by positivity)]
      push_cast
      have : (ℓ : ℝ≥0) * 1 ≤ (ℓ : ℝ≥0) * D' := by gcongr
      calc (ℓ : ℝ≥0) + D' ≤ (ℓ : ℝ≥0) * D' + D' := by simpa using add_le_add_right this D'
        _ = ((ℓ : ℝ≥0) + 1) * D' := by ring
    have hnat : 4 * d * ⌈((ℓ : ℝ≥0) + D') / D'⌉₊ ≤ 8 * d * ℓ := by
      calc 4 * d * ⌈((ℓ : ℝ≥0) + D') / D'⌉₊ ≤ 4 * d * (ℓ + 1) := by gcongr
        _ ≤ 8 * d * ℓ := by nlinarith [Nat.zero_le d]
    calc (4 * d * (⌈((ℓ : ℝ≥0) + D') / D'⌉₊ : ℕ) : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-γ))
        ≤ ((8 * d * ℓ : ℕ) : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-γ)) := by
          gcongr; exact_mod_cast hnat
      _ = ENNReal.ofReal (8 * d * ℓ * Real.exp (-γ)) := by
          rw [ENNReal.ofReal_mul (by positivity)]
          congr 1
          rw [show (8 * (d : ℝ) * ℓ) = ((8 * d * ℓ : ℕ) : ℝ) by push_cast; ring,
            ENNReal.ofReal_natCast]
  calc _ ≤ (P1 d ℓ (μ.map absVec)) (({ω : Ω1 d ℓ | ¬ ∀ k i, Tp k (Vfull ℓ ω) i < ⊤} ∪
        ⋃ k : Fin d, ClockEvent D k) ∪ OscEvent ((ℓ : ℝ≥0) + D') D' Λ) := measure_mono hsub
    _ ≤ (P1 d ℓ (μ.map absVec)) ({ω : Ω1 d ℓ | ¬ ∀ k i, Tp k (Vfull ℓ ω) i < ⊤} ∪
        ⋃ k : Fin d, ClockEvent D k) + (P1 d ℓ (μ.map absVec)) (OscEvent ((ℓ : ℝ≥0) + D') D' Λ) :=
        measure_union_le _ _
    _ ≤ ((P1 d ℓ (μ.map absVec)) {ω : Ω1 d ℓ | ¬ ∀ k i, Tp k (Vfull ℓ ω) i < ⊤} +
        (P1 d ℓ (μ.map absVec)) (⋃ k : Fin d, ClockEvent D k)) +
        (P1 d ℓ (μ.map absVec)) (OscEvent ((ℓ : ℝ≥0) + D') D' Λ) := by
        gcongr; exact measure_union_le _ _
    _ ≤ (0 + ENNReal.ofReal (d * (2 * ℓ * Real.exp (-γ)))) +
        ENNReal.ofReal (8 * d * ℓ * Real.exp (-γ)) := by
        rw [hP0]; gcongr
    _ = ENNReal.ofReal (10 * d * ℓ * Real.exp (-γ)) := by
        rw [zero_add, ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1; ring

end ElboimSly.StrongApprox
