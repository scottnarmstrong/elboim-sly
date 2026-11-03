/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Frozen.Defs.ExtPoissonMeasure
import Mathlib

/-!
# Facts about the extended Poisson law

Extended Poisson law (extension of falling factorials), facts about pppPo.

* `extPoissonMeasure_conv`: (a) convolution.
* `continuous_extPoisson_Iic`: (b) continuity of `a ↦ Po*(a)[0,c]`.
* `extPoissonMeasure_zero_singleton`, `extPoissonMeasure_one_singleton`,
  `extPoissonMeasure_range_natCast`, `extPoissonMeasure_Ici_two_le`: (c) small values.
* `lintegral_extDescFactorial`: (d) factorial moments.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Nat

namespace ElboimSly

theorem extPoissonMeasure_top : extPoissonMeasure ∞ = Measure.dirac ∞ := by
  simp [extPoissonMeasure]

theorem extPoissonMeasure_coe (r : ℝ≥0) :
    extPoissonMeasure r = (poissonMeasure r).map (Nat.cast : ℕ → ℝ≥0∞) := by
  simp [extPoissonMeasure]

theorem measurable_natCast_ennreal : Measurable (Nat.cast : ℕ → ℝ≥0∞) :=
  measurable_from_top

instance isProbabilityMeasure_extPoissonMeasure (a : ℝ≥0∞) :
    IsProbabilityMeasure (extPoissonMeasure a) := by
  by_cases h : a = ∞
  · subst h; rw [extPoissonMeasure_top]; infer_instance
  · have : extPoissonMeasure a = (poissonMeasure a.toNNReal).map (Nat.cast : ℕ → ℝ≥0∞) := by
      simp [extPoissonMeasure, h]
    rw [this]
    infer_instance

/-- Facts about pppPo (a): convolution of extended Poisson laws. -/
theorem extPoissonMeasure_conv (a b : ℝ≥0∞) :
    extPoissonMeasure a ∗ extPoissonMeasure b = extPoissonMeasure (a + b) := by
  by_cases ha : a = ∞
  · subst ha
    rw [extPoissonMeasure_top, Measure.dirac_conv, top_add, extPoissonMeasure_top]
    have : (fun x : ℝ≥0∞ => ∞ + x) = fun _ => ∞ := by ext x; simp
    rw [this, Measure.map_const, measure_univ, one_smul]
  by_cases hb : b = ∞
  · subst hb
    rw [extPoissonMeasure_top, Measure.conv_dirac, add_top, extPoissonMeasure_top]
    have : (fun x : ℝ≥0∞ => x + ∞) = fun _ => ∞ := by ext x; simp
    rw [this, Measure.map_const, measure_univ, one_smul]
  · lift a to ℝ≥0 using ha
    lift b to ℝ≥0 using hb
    rw [extPoissonMeasure_coe, extPoissonMeasure_coe, ← ENNReal.coe_add, extPoissonMeasure_coe]
    exact map_cast_poissonMeasure_conv a b

/-! ### Small values -/

theorem extPoissonMeasure_singleton_natCast (r : ℝ≥0) (n : ℕ) :
    extPoissonMeasure r {(n : ℝ≥0∞)} = ENNReal.ofReal (Real.exp (-r) * r ^ n / (n)!) := by
  rw [extPoissonMeasure_coe, Measure.map_apply measurable_natCast_ennreal (measurableSet_singleton _)]
  have : (Nat.cast : ℕ → ℝ≥0∞) ⁻¹' {(n : ℝ≥0∞)} = {n} := by
    ext m; simp
  rw [this, poissonMeasure_singleton]

/-- Facts about pppPo (c), the value at `0`. -/
theorem extPoissonMeasure_zero_singleton (r : ℝ≥0) :
    extPoissonMeasure r {0} = ENNReal.ofReal (Real.exp (-r)) := by
  have := extPoissonMeasure_singleton_natCast r 0
  simpa using this

/-- Facts about pppPo (c), the value at `1`. -/
theorem extPoissonMeasure_one_singleton (r : ℝ≥0) :
    extPoissonMeasure r {1} = ENNReal.ofReal (r * Real.exp (-r)) := by
  have := extPoissonMeasure_singleton_natCast r 1
  simp only [Nat.cast_one, pow_one, Nat.factorial_one, Nat.cast_one, div_one] at this
  rw [this, mul_comm]

/-- Facts about pppPo (c): `Po*(a)` is carried by `ℕ`. -/
theorem extPoissonMeasure_range_natCast (r : ℝ≥0) :
    extPoissonMeasure r (Set.range (Nat.cast : ℕ → ℝ≥0∞)) = 1 := by
  rw [extPoissonMeasure_coe, Measure.map_apply measurable_natCast_ennreal
    (Set.countable_range _).measurableSet]
  simp

theorem real_poisson_tail_bound (a : ℝ) (ha : 0 ≤ a) :
    1 - (Real.exp (-a) + a * Real.exp (-a)) ≤ a ^ 2 / 2 := by
  let f : ℝ → ℝ := fun a => Real.exp (-a) * (1 + a) - 1 + a ^ 2 / 2
  have hderiv : ∀ x : ℝ, HasDerivAt f (x * (1 - Real.exp (-x))) x := by
    intro x
    have h1 : HasDerivAt (fun x : ℝ => Real.exp (-x)) (-Real.exp (-x)) x := by
      have := (hasDerivAt_neg x).exp
      simpa using this
    have h2 := ((h1.mul ((hasDerivAt_id x).const_add 1)).sub_const 1).add
      ((hasDerivAt_pow 2 x).div_const 2)
    refine h2.congr_deriv ?_
    simp only [id]
    push_cast
    ring
  have hmono : MonotoneOn f (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · exact fun x _ => (hderiv x).continuousAt.continuousWithinAt
    · exact fun x _ => (hderiv x).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      rw [(hderiv x).deriv]
      have hx0 : 0 < x := hx
      have : Real.exp (-x) ≤ 1 := by
        rw [Real.exp_le_one_iff]; linarith
      nlinarith
  have := hmono (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 ha) ha
  have h0 : f 0 = 0 := by simp [f]
  simp only [f] at this h0
  nlinarith

/-- Facts about pppPo (c): `Po*(a)([2,∞]) ≤ a²/2`. -/
theorem extPoissonMeasure_Ici_two_le (r : ℝ≥0) :
    extPoissonMeasure r (Set.Ici 2) ≤ ENNReal.ofReal ((r : ℝ) ^ 2 / 2) := by
  rw [extPoissonMeasure_coe, Measure.map_apply measurable_natCast_ennreal measurableSet_Ici]
  have hpre : (Nat.cast : ℕ → ℝ≥0∞) ⁻¹' Set.Ici 2 = ({0, 1} : Set ℕ)ᶜ := by
    ext n
    simp only [Set.mem_preimage, Set.mem_Ici, Set.mem_compl_iff, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    constructor
    · intro h h'
      rcases h' with rfl | rfl <;> norm_num at h
    · intro h
      have : 2 ≤ n := by omega
      exact_mod_cast this
  rw [hpre, prob_compl_eq_one_sub (Set.toFinite _).measurableSet]
  have h01 : (poissonMeasure r) ({0, 1} : Set ℕ) =
      ENNReal.ofReal (Real.exp (-r) + r * Real.exp (-r)) := by
    have e : ({0, 1} : Set ℕ) = {0} ∪ {1} := rfl
    rw [e, measure_union (by simp) (measurableSet_singleton _), poissonMeasure_singleton,
      poissonMeasure_singleton, ← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    simp
    ring
  rw [h01, ← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ (by positivity)]
  exact ENNReal.ofReal_le_ofReal (real_poisson_tail_bound r r.2)

end ElboimSly
