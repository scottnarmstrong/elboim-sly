/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Heavy.Jumps
public import ElboimSly.Paper.Heavy.ScalesFactsB
public import Mathlib

/-!
# Eq. (taufast) (first piece)

Eq. (taufast) (ES22 eq. (taufast), ES22 §6).  For `β ≥ 2` and `t₀ ∈ (1, 4]`,
`P(τ_fast ≤ t_n) ≤ P(τ_jump ≤ t_n) ≤ ϖ_n := C_J 16^{n+1} e^{-n³/2}`, for the first piece
`W^ν_{0,0}` of a Poisson environment.  The statements are in the exact form (event
`≤ min (t_n, t_reg)`) of the hypotheses `hfast`, `hjump` of `es6_tauhat_of`.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal ENNReal

namespace ElboimSly.Paper.Heavy

open ElboimSly ElboimSly.Paper ElboimSly.Cyclic ElboimSly.Interchange

variable {d : ℕ} {β : ℝ} [Fact (0 < β)] {Ω : Type*} [MeasurableSpace Ω] {Pe : Measure Ω}
  {ν : Ω → Measure (RingSpace d β)}

theorem heavyCJ_ge_one (d : ℕ) : 1 ≤ heavyCJ d := by
  unfold heavyCJ
  have : 1 ≤ Real.exp (4 * d * (Real.exp 1 - 1)) := Real.one_le_exp (by
    have := Real.add_one_le_exp 1
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    nlinarith)
  linarith

theorem varpi_scale_le {t₀ : ℝ} (ht1 : 1 < t₀) (ht4 : t₀ ≤ 4) (n : ℕ) :
    1 ≤ indScale t₀ n ∧ indScale t₀ n ^ 2 ≤ (16 : ℝ) ^ (n + 1) := by
  refine ⟨?_, ?_⟩
  · unfold indScale
    have : (1 : ℝ) ≤ 4 ^ n := one_le_pow₀ (by norm_num)
    nlinarith
  · have h1 := indScale_le_four_pow ht4 n
    have h0 : 0 ≤ indScale t₀ n := by unfold indScale; positivity
    calc indScale t₀ n ^ 2 ≤ ((4 : ℝ) ^ (n + 1)) ^ 2 := by gcongr
      _ = 16 ^ (n + 1) := by rw [← pow_mul, mul_comm, pow_mul]; norm_num

/-- Eq. (taufast): `P(τ_jump ≤ t_n) ≤ ϖ_n`. -/
theorem es6_taujump_prob {t₀ : ℝ} (ht1 : 1 < t₀) (ht4 : t₀ ≤ 4) (hβ : 2 ≤ β)
    (hν : IsPoissonPointProcess ν (ringIntensity d β) Pe) (n : ℕ) :
    Pe {ω | pathTjumpCube (fun s : ℝ => cycWalk (ν ω) 0 0 s) n ≤
        min (ENNReal.ofReal (indScale t₀ n)) (cycTreg (ν ω))} ≤
      ENNReal.ofReal (heavyCJ d * 16 ^ (n + 1) * Real.exp (-((n : ℝ) ^ 3 / 2))) := by
  have := hν.isProbabilityMeasure
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine (prob_le_one).trans ?_
    rw [← ENNReal.ofReal_one]
    apply ENNReal.ofReal_le_ofReal
    have := heavyCJ_ge_one d
    simp only [CharP.cast_eq_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      zero_div, neg_zero, Real.exp_zero, mul_one, zero_add, pow_one]
    linarith
  · obtain ⟨hs1, hs2⟩ := varpi_scale_le ht1 ht4 n
    have hL : (1 : ℝ) ≤ (n : ℝ) ^ 3 := one_le_pow₀ (by exact_mod_cast hn)
    refine le_trans (le_trans (measure_mono fun ω hω => ?_)
      (pathTjump_first_prob hβ hν hL hs1)) ?_
    · exact (show pathTjumpCube (fun s : ℝ => cycWalk (ν ω) 0 0 s) n ≤ _ from hω).trans (min_le_left _ _)
    · apply ENNReal.ofReal_le_ofReal
      have : 0 ≤ heavyCJ d * Real.exp (-((n : ℝ) ^ 3 / 2)) := by
        have := heavyCJ_ge_one d
        positivity
      calc heavyCJ d * indScale t₀ n ^ 2 * Real.exp (-((n : ℝ) ^ 3 / 2))
          = indScale t₀ n ^ 2 * (heavyCJ d * Real.exp (-((n : ℝ) ^ 3 / 2))) := by ring
        _ ≤ 16 ^ (n + 1) * (heavyCJ d * Real.exp (-((n : ℝ) ^ 3 / 2))) :=
            mul_le_mul_of_nonneg_right hs2 this
        _ = _ := by ring

/-- Eq. (taufast): `P(τ_fast ≤ t_n) ≤ P(τ_jump ≤ t_n) ≤ ϖ_n`. -/
theorem es6_taufast_prob {t₀ : ℝ} (ht1 : 1 < t₀) (ht4 : t₀ ≤ 4) (hβ : 2 ≤ β)
    (hν : IsPoissonPointProcess ν (ringIntensity d β) Pe) (n : ℕ) :
    Pe {ω | pathTfastCube (fun s : ℝ => cycWalk (ν ω) 0 0 s) n ≤
        min (ENNReal.ofReal (indScale t₀ n)) (cycTreg (ν ω))} ≤
      ENNReal.ofReal (heavyCJ d * 16 ^ (n + 1) * Real.exp (-((n : ℝ) ^ 3 / 2))) := by
  have hgood : ∀ᵐ ω ∂Pe, Good (ν ω) := ae_good hν
  refine le_trans (measure_mono_ae ?_) (es6_taujump_prob ht1 ht4 hβ hν n)
  filter_upwards [hgood] with ω hω h
  exact (pathTjump_le_pathTfast (isCyclicPath_cycWalk hω) _).trans h

end ElboimSly.Paper.Heavy
