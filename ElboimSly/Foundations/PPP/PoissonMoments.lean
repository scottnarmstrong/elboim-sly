/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.PPP.PoissonFacts
import Mathlib

/-!
# Factorial moments and continuity of the extended Poisson law

Extended Poisson law (falling factorial on `[0,∞]`), facts about pppPo (b), (d).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal Nat

namespace ElboimSly

/-- The falling factorial `(x)_k` on `[0,∞]`: `x (x-1) ⋯ (x-k+1)` for `x ∈ ℕ` and `0` otherwise.
Extended Poisson law. -/
noncomputable def extDescFactorial (x : ℝ≥0∞) (k : ℕ) : ℝ≥0∞ :=
  ∑' n : ℕ, if x = n then (n.descFactorial k : ℝ≥0∞) else 0

theorem extDescFactorial_natCast (n k : ℕ) :
    extDescFactorial (n : ℝ≥0∞) k = (n.descFactorial k : ℝ≥0∞) := by
  unfold extDescFactorial
  rw [tsum_eq_single n]
  · simp
  · intro m hm
    have : (n : ℝ≥0∞) ≠ m := fun h => hm (by exact_mod_cast h.symm)
    simp [this]

theorem measurable_extDescFactorial (k : ℕ) : Measurable fun x => extDescFactorial x k := by
  unfold extDescFactorial
  refine Measurable.tsum fun n => ?_
  exact Measurable.ite (measurableSet_singleton _) measurable_const measurable_const

theorem hasSum_poisson_descFactorial (a : ℝ≥0) (k : ℕ) :
    HasSum (fun n : ℕ => Real.exp (-a) * a ^ n / (n)! * (n.descFactorial k : ℝ))
      ((a : ℝ) ^ k) := by
  have h0 : ∑ i ∈ Finset.range k, Real.exp (-a) * a ^ i / (i)! * (i.descFactorial k : ℝ) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rw [Nat.descFactorial_eq_zero_iff_lt.2 (Finset.mem_range.1 hi)]
    simp
  suffices key : HasSum (fun n : ℕ => Real.exp (-a) * a ^ (n + k) / (n + k)! *
      ((n + k).descFactorial k : ℝ)) ((a : ℝ) ^ k) by
    have := (hasSum_nat_add_iff (f := fun n : ℕ => Real.exp (-a) * a ^ n / (n)! *
      (n.descFactorial k : ℝ)) k).1 key
    rwa [h0, add_zero] at this
  have := (hasSum_one_poissonMeasure a).mul_left ((a : ℝ) ^ k)
  rw [mul_one] at this
  convert this using 1
  ext n
  have hf0 : (n)! * (n + k).descFactorial k = (n + k)! := by
    simpa using Nat.factorial_mul_descFactorial (Nat.le_add_left k n)
  have hf : ((n + k).descFactorial k : ℝ) * (n)! = ((n + k)! : ℝ) := by
    exact_mod_cast (by rw [mul_comm]; exact hf0)
  have hn : ((n)! : ℝ) ≠ 0 := by positivity
  have hnk : (((n + k)! : ℕ) : ℝ) ≠ 0 := by positivity
  rw [pow_add]
  field_simp
  rw [← hf]
  ring

/-- Facts about pppPo (d): factorial moments of `Po*(a)` are `a^k`. -/
theorem lintegral_extDescFactorial (a : ℝ≥0) (k : ℕ) :
    ∫⁻ x, extDescFactorial x k ∂extPoissonMeasure a = (a : ℝ≥0∞) ^ k := by
  rw [extPoissonMeasure_coe, lintegral_map (measurable_extDescFactorial k)
    measurable_natCast_ennreal, lintegral_countable']
  have h1 : ∀ n : ℕ, extDescFactorial (n : ℝ≥0∞) k * poissonMeasure a {n} =
      ENNReal.ofReal (Real.exp (-a) * a ^ n / (n)! * (n.descFactorial k : ℝ)) := by
    intro n
    rw [extDescFactorial_natCast, poissonMeasure_singleton, mul_comm,
      ENNReal.ofReal_mul (by positivity)]
    simp
  simp_rw [h1]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity)
    (hasSum_poisson_descFactorial a k).summable, (hasSum_poisson_descFactorial a k).tsum_eq,
    ENNReal.ofReal_pow a.coe_nonneg, ENNReal.ofReal_coe_nnreal]

/-! ### Continuity -/

theorem extPoissonMeasure_natCast_singleton (a : ℝ≥0∞) (m : ℕ) :
    extPoissonMeasure a {(m : ℝ≥0∞)} =
      if a = ∞ then 0 else
        ENNReal.ofReal (Real.exp (-a.toReal) * a.toReal ^ m / (m)!) := by
  by_cases h : a = ∞
  · simp [h, extPoissonMeasure_top]
  · lift a to ℝ≥0 using h
    simp [extPoissonMeasure_singleton_natCast]

theorem continuous_extPoissonMeasure_singleton (m : ℕ) :
    Continuous fun a : ℝ≥0∞ => extPoissonMeasure a {(m : ℝ≥0∞)} := by
  have hfun : (fun a : ℝ≥0∞ => extPoissonMeasure a {(m : ℝ≥0∞)}) = fun a =>
      if a = ∞ then 0 else ENNReal.ofReal (Real.exp (-a.toReal) * a.toReal ^ m / (m)!) :=
    funext fun a => extPoissonMeasure_natCast_singleton a m
  rw [hfun, continuous_iff_continuousAt]
  intro a
  by_cases ha : a = ∞
  · subst ha
    show Tendsto _ _ (𝓝 (if (∞ : ℝ≥0∞) = ∞ then 0 else _))
    rw [ite_eq_left rfl, ENNReal.tendsto_nhds_zero]
    intro ε hε
    obtain ⟨r, hr0, hrε⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hε
    have hr : (0 : ℝ) < r := by exact_mod_cast hr0
    have hT := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero m).eventually (Iio_mem_nhds hr)
    obtain ⟨T, hT⟩ := eventually_atTop.1 hT
    have hU : Set.Ioi ((⌈T⌉₊ : ℝ≥0) : ℝ≥0∞) ∈ 𝓝 (∞ : ℝ≥0∞) := Ioi_mem_nhds (by simp)
    filter_upwards [hU] with b hb
    split_ifs with hb'
    · exact bot_le
    · have hbT : T ≤ b.toReal := by
        have : ((⌈T⌉₊ : ℝ≥0) : ℝ≥0∞) < b := hb
        have h2 := (ENNReal.toReal_lt_toReal (by simp) hb').2 this
        simp only [ENNReal.coe_toReal] at h2
        have := Nat.le_ceil T
        simp at h2
        linarith
      have h3 := hT _ hbT
      refine le_trans ?_ hrε.le
      rw [← ENNReal.ofReal_coe_nnreal]
      apply ENNReal.ofReal_le_ofReal
      have hf : (1 : ℝ) ≤ (m)! := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero m)
      have hnn : 0 ≤ Real.exp (-b.toReal) * b.toReal ^ m := by positivity
      calc Real.exp (-b.toReal) * b.toReal ^ m / (m)! ≤ Real.exp (-b.toReal) * b.toReal ^ m :=
            div_le_self hnn hf
        _ ≤ r := by rw [mul_comm]; exact h3.le
  · have hev : ∀ᶠ b in 𝓝 a, b ≠ ∞ := isOpen_ne.mem_nhds ha
    refine ContinuousAt.congr (f := fun b : ℝ≥0∞ =>
      ENNReal.ofReal (Real.exp (-b.toReal) * b.toReal ^ m / (m)!)) ?_ ?_
    · have h1 : ContinuousAt (fun b : ℝ≥0∞ => b.toReal) a := ENNReal.continuousAt_toReal ha
      exact ENNReal.continuous_ofReal.continuousAt.comp (by fun_prop)
    · filter_upwards [hev] with b hb using by simp [hb]

theorem extPoissonMeasure_compl_range (a : ℝ≥0∞) :
    extPoissonMeasure a (Set.range (Nat.cast : ℕ → ℝ≥0∞))ᶜ = 0 ∨ a = ∞ := by
  by_cases h : a = ∞
  · exact Or.inr h
  · left
    lift a to ℝ≥0 using h
    rw [prob_compl_eq_zero_iff (Set.countable_range _).measurableSet]
    exact extPoissonMeasure_range_natCast a

/-- Facts about pppPo (b): `a ↦ Po*(a)([0,c])` is continuous (in particular
continuous along nondecreasing sequences). -/
theorem continuous_extPoissonMeasure_Iic (c : ℝ≥0∞) :
    Continuous fun a : ℝ≥0∞ => extPoissonMeasure a (Set.Iic c) := by
  by_cases hc : c = ∞
  · subst hc
    simp
    exact continuous_const
  · have hfin : {m : ℕ | (m : ℝ≥0∞) ≤ c}.Finite := by
      refine (Set.finite_Iic ⌈c.toReal⌉₊).subset fun m hm => ?_
      have : (m : ℝ) ≤ c.toReal := by
        have := ENNReal.toReal_mono hc hm
        simpa using this
      exact Set.mem_Iic.2 (by exact_mod_cast this.trans (Nat.le_ceil _))
    have key : ∀ a : ℝ≥0∞, extPoissonMeasure a (Set.Iic c) =
        ∑ m ∈ hfin.toFinset, extPoissonMeasure a {(m : ℝ≥0∞)} := by
      intro a
      rcases extPoissonMeasure_compl_range a with h | h
      · rw [← measure_inter_conull h]
        have e : Set.Iic c ∩ Set.range (Nat.cast : ℕ → ℝ≥0∞) =
            ((hfin.toFinset.image (Nat.cast : ℕ → ℝ≥0∞) : Finset ℝ≥0∞) : Set ℝ≥0∞) := by
          ext x
          simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_range, Finset.coe_image,
            Set.Finite.coe_toFinset, Set.mem_image, Set.mem_ofPred_eq]
          constructor
          · rintro ⟨h1, m, rfl⟩; exact ⟨m, h1, rfl⟩
          · rintro ⟨m, h1, rfl⟩; exact ⟨h1, m, rfl⟩
        rw [e, ← sum_measure_singleton, Finset.sum_image]
        intro x _ y _ hxy
        exact_mod_cast hxy
      · subst h
        have : ∀ m : ℕ, (m : ℝ≥0∞) ≠ ∞ := fun m => ENNReal.natCast_ne_top m
        simp [extPoissonMeasure_top, Measure.dirac_apply', hc]
    simp_rw [key]
    exact continuous_finsetSum _ fun m _ => continuous_extPoissonMeasure_singleton m

end ElboimSly
