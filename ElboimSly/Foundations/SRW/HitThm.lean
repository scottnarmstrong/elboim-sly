/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.SRW.HitMain
public import Mathlib

/-!
# Hitting a box after a given time

Hitting a box after a given time.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Real

namespace ElboimSly
namespace SRW

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {Z : Ω → PathSpace d}

theorem norm_cast_vec (z : Fin d → ℤ) : ‖fun i => ((z i : ℤ) : ℝ)‖ = ‖z‖ := by
  apply le_antisymm
  · refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_
    exact (Int.norm_cast_real (z i)).le.trans (norm_le_pi_norm z i)
  · refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_
    exact (Int.norm_cast_real (z i)).symm.le.trans (norm_le_pi_norm (fun i => ((z i : ℤ) : ℝ)) i)

theorem stayBall_prob (hZ : IsSRW P Z) [NeZero d] (hd : 1 ≤ d) {ρ : ℝ} (hρ : 1 ≤ ρ) :
    1 / 2 ≤ P.real {ω | Z ω ∈ stayBall (kappa d * ρ) (ρ ^ 2).toNNReal} := by
  have := hZ.isProbabilityMeasure
  have hκ := kappa_ge hd
  set κ := kappa d with hκdef
  have hρ0 : 0 < ρ := by linarith
  set h : ℝ≥0 := (ρ ^ 2).toNNReal with hh
  have hhc : (h : ℝ) = ρ ^ 2 := Real.coe_toNNReal _ (by positivity)
  have hhpos : 0 < h := by
    have : (0 : ℝ) < h := by rw [hhc]; positivity
    exact_mod_cast this
  set S := {ω | Z ω ∈ stayBall (κ * ρ) h} with hS
  set T := {ω | ∃ s : ℝ≥0, s ≤ h ∧ κ * ρ ≤ ‖Z ω s‖} with hT
  have hsub : Sᶜ ⊆ T := by
    intro ω hω
    simp only [hS, mem_compl_iff, mem_ofPred_eq, stayBall, evalForall, mem_univ, true_and,
      not_forall] at hω
    obtain ⟨s, hs, hns⟩ := hω
    refine ⟨s, hs, ?_⟩
    simp only [not_lt] at hns
    rwa [norm_cast_vec] at hns
  have h1 := real_one_sub_le P S T hsub
  have h2 := hZ.maximal hhpos (a := κ * ρ) (by positivity)
  have hmin : κ / 2 ≤ min ((κ * ρ) ^ 2 / (8 * (h : ℝ))) (κ * ρ / 2) := by
    refine le_min ?_ ?_
    · rw [hhc, mul_pow, le_div_iff₀ (by positivity)]
      have : κ * (8 * ρ ^ 2) / 2 ≤ κ ^ 2 * ρ ^ 2 := by nlinarith [sq_nonneg ρ]
      linarith
    · have : κ * 1 ≤ κ * ρ := by gcongr
      linarith
  have h3 : Real.exp (-min ((κ * ρ) ^ 2 / (8 * (h : ℝ))) (κ * ρ / 2)) ≤ Real.exp (-(κ / 2)) :=
    Real.exp_le_exp.2 (by linarith)
  have h4 := four_d_exp_le hd
  have h5 : 4 * (d : ℝ) * Real.exp (-min ((κ * ρ) ^ 2 / (8 * (h : ℝ))) (κ * ρ / 2)) ≤
      4 * (d : ℝ) * Real.exp (-(κ / 2)) := by gcongr
  have h6 : P.real T ≤ 4 * (d : ℝ) * Real.exp (-min ((κ * ρ) ^ 2 / (8 * (h : ℝ))) (κ * ρ / 2)) := h2
  linarith

/-- Hitting a box after a given time: hitting a ball after a given time. -/
theorem hit (hZ : IsSRW P Z) (hd : 3 ≤ d) (x y : Fin d → ℤ) {ρ : ℝ} (hρ : 1 ≤ ρ) {a : ℝ≥0}
    (ha : 0 < a) :
    P.real {ω | ∃ s : ℝ≥0, a ≤ s ∧ ‖fun i => ((x i + Z ω s i - y i : ℤ) : ℝ)‖ ≤ ρ} ≤
      Chit d * (ρ / √(a : ℝ)) ^ (d - 2) := by
  have : NeZero d := ⟨by omega⟩
  have := hZ.isProbabilityMeasure
  have hd1 : 1 ≤ d := by omega
  have hκ := kappa_ge hd1
  set κ := kappa d with hκdef
  have hρ0 : 0 < ρ := by linarith
  set ρ₁ := κ * ρ with hρ₁
  have hρ₁1 : ρ ≤ ρ₁ := by nlinarith
  have hρ₁8 : 8 ≤ ρ₁ := by nlinarith
  set h : ℝ≥0 := (ρ ^ 2).toNNReal with hh
  have hhc : (h : ℝ) = ρ ^ 2 := Real.coe_toNNReal _ (by positivity)
  set K : Set (Fin d → ℤ) := {z : Fin d → ℤ | ‖fun i => ((x i + z i - y i : ℤ) : ℝ)‖ ≤ ρ₁}
    with hK
  have hmax := stayBall_prob hZ hd1 hρ
  have hmark := hit_markov hZ ρ₁ h a K hmax
  have hcount := hit_count hZ x y (ρ₁ := ρ₁) h a
  have hsumb := tsum_ballVisit_le hZ hd (y - x) (R := 2 * ρ₁) (by positivity)
    (K₀ := ⌈a⌉₊) (Nat.ceil_pos.2 ha)
  -- E ⊆ {τ < ⊤}
  set E := {ω | ∃ s : ℝ≥0, a ≤ s ∧ ‖fun i => ((x i + Z ω s i - y i : ℤ) : ℝ)‖ ≤ ρ} with hE
  have hEsub : E ⊆ {ω | hitTime Z a K ω < ⊤} := by
    intro ω ⟨s, hs, hn⟩
    show hitTime Z a K ω < ⊤
    unfold hitTime
    rw [ite_eq_left ⟨s, hs, le_trans hn hρ₁1⟩]
    exact WithTop.coe_lt_top _
  set G := {ω | hitTime Z a K ω < ⊤ ∧ thetaAt (hitTime Z a K) Z ω ∈ stayBall ρ₁ h} with hG
  -- the real inequality ⌊h⌋ P(G) ≤ M
  set K₀ := ⌈a⌉₊ with hK₀
  set M : ℝ := (2 * (2 * ρ₁) + 1) ^ d * π ^ (-(d : ℝ) / 2) * (3 * (K₀ : ℝ) ^ (1 - (d : ℝ) / 2))
    with hM
  have hM0 : 0 ≤ M := by positivity
  have hcount' : (⌊h⌋₊ : ℝ) * P.real G ≤ M := by
    have h1 := hcount.trans hsumb
    have h2 : ((⌊h⌋₊ : ℝ≥0∞) * P G).toReal ≤ M :=
      ENNReal.toReal_le_of_le_ofReal hM0 h1
    rw [ENNReal.toReal_mul] at h2
    simpa [measureReal_def] using h2
  have hfl : ρ ^ 2 / 2 ≤ (⌊h⌋₊ : ℝ) := by
    have h1 : (1 : ℝ≥0) ≤ h := by
      rw [← NNReal.coe_le_coe, hhc]; push_cast; nlinarith
    have h2 : (h : ℝ) < (⌊h⌋₊ : ℝ) + 1 := by exact_mod_cast Nat.lt_floor_add_one h
    have h4 : (1 : ℝ) ≤ (⌊h⌋₊ : ℝ) := by exact_mod_cast Nat.le_floor (by simpa using h1)
    rw [hhc] at h2
    linarith
  have hG0 : 0 ≤ P.real G := measureReal_nonneg
  have hEle : P.real E ≤ P.real {ω | hitTime Z a K ω < ⊤} :=
    measureReal_mono hEsub
  have hPG : P.real E ≤ 4 * M / ρ ^ 2 := by
    have h1 : P.real E ≤ 2 * P.real G := by linarith
    have h2 : ρ ^ 2 / 2 * P.real G ≤ M := le_trans (by gcongr) hcount'
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  refine hPG.trans ?_
  -- algebra
  have hK₀a : (a : ℝ) ≤ K₀ := Nat.le_ceil _
  have ha0 : (0 : ℝ) < a := by exact_mod_cast ha
  have hpow : (K₀ : ℝ) ^ (1 - (d : ℝ) / 2) ≤ (a : ℝ) ^ (1 - (d : ℝ) / 2) := by
    apply Real.rpow_le_rpow_of_nonpos ha0 hK₀a
    have : (3 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hb : (2 * (2 * ρ₁) + 1) ^ d ≤ (5 * κ) ^ d * ρ ^ d := by
    rw [← mul_pow]
    apply pow_le_pow_left₀ (by positivity)
    nlinarith
  have hsq : (ρ / √(a : ℝ)) ^ (d - 2) = ρ ^ (d - 2) * (a : ℝ) ^ (1 - (d : ℝ) / 2) := by
    rw [div_pow, Real.sqrt_eq_rpow, ← Real.rpow_natCast ((a : ℝ) ^ (1 / 2 : ℝ)),
      ← Real.rpow_mul ha0.le]
    have hd2 : ((d - 2 : ℕ) : ℝ) = (d : ℝ) - 2 := by
      rw [Nat.cast_sub (by omega)]; norm_num
    rw [hd2]
    have : (1 - (d : ℝ) / 2) = -(1 / 2 * ((d : ℝ) - 2)) := by ring
    rw [this, Real.rpow_neg ha0.le, div_eq_mul_inv]
  have hρd : ρ ^ d = ρ ^ (d - 2) * ρ ^ 2 := by
    rw [← pow_add]; congr 1; omega
  unfold Chit
  rw [hsq]
  calc 4 * M / ρ ^ 2
      = 12 * ((2 * (2 * ρ₁) + 1) ^ d * π ^ (-(d : ℝ) / 2) * (K₀ : ℝ) ^ (1 - (d : ℝ) / 2)) /
          ρ ^ 2 := by rw [hM]; ring
    _ ≤ 12 * ((5 * κ) ^ d * ρ ^ d * π ^ (-(d : ℝ) / 2) * (a : ℝ) ^ (1 - (d : ℝ) / 2)) /
          ρ ^ 2 := by gcongr
    _ = _ := by rw [hρd, hκdef]; field_simp

end SRW
end ElboimSly
