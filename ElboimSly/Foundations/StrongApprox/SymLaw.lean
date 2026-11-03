/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import Mathlib

/-!
# Symmetric two-point laws and a product decomposition

Signs, moduli, symmetric two-point laws (`ρ_s`) and exit times of Brownian motion from symmetric intervals (b), the measure-theoretic core
(Part II).

`symLaw r = ½(δ_r + δ_{-r})`. A probability measure on `ℝ × α` that is concentrated on
`{r, -r} × α` and invariant under `(x, a) ↦ (-x, a)` is the product of `symLaw r` and its second
marginal.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace ElboimSly.StrongApprox

/-- Signs, moduli, symmetric two-point laws. The symmetric two-point law `ρ_r = ½(δ_r + δ_{-r})`. -/
noncomputable def symLaw (r : ℝ) : Measure ℝ :=
  (2 : ℝ≥0∞)⁻¹ • (Measure.dirac r + Measure.dirac (-r))

instance (r : ℝ) : IsProbabilityMeasure (symLaw r) := ⟨by
  simp only [symLaw, Measure.smul_apply, Measure.add_apply, measure_univ, smul_eq_mul]
  rw [one_add_one_eq_two, mul_comm]
  exact ENNReal.mul_inv_cancel (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ∞)⟩

lemma symLaw_apply {r : ℝ} {s : Set ℝ} (hs : MeasurableSet s) :
    symLaw r s = 2⁻¹ * (s.indicator 1 r + s.indicator 1 (-r)) := by
  simp [symLaw, Measure.dirac_apply' _ hs, mul_add]

lemma measure_prod_eq_of_symm {α : Type*} [MeasurableSpace α] (ν : Measure (ℝ × α))
    [IsProbabilityMeasure ν] {r : ℝ} (hr : 0 < r)
    (hsupp : ∀ᵐ p ∂ν, p.1 = r ∨ p.1 = -r)
    (hsymm : ν.map (fun p => (-p.1, p.2)) = ν) :
    ν = (symLaw r).prod (ν.map Prod.snd) := by
  have hneg : Measurable (fun p : ℝ × α => (-p.1, p.2)) :=
    (measurable_fst.neg).prodMk measurable_snd
  have hrr : r ≠ -r := by intro h; linarith
  symm
  refine Measure.prod_eq fun s t hs ht => ?_
  have hab : ν ({r} ×ˢ t) = ν ({-r} ×ˢ t) := by
    have := congrArg (fun m => m ({-r} ×ˢ t)) hsymm
    simp only [Measure.map_apply hneg ((measurableSet_singleton _).prod ht)] at this
    have e : (fun p : ℝ × α => (-p.1, p.2)) ⁻¹' ({-r} ×ˢ t) = {r} ×ˢ t := by
      ext p; simp [neg_eq_iff_eq_neg]
    rw [e] at this
    exact this
  -- decomposition of a rectangle
  have hdec : ∀ s' : Set ℝ, MeasurableSet s' →
      ν (s' ×ˢ t) = ν ((s' ∩ {r}) ×ˢ t) + ν ((s' ∩ {-r}) ×ˢ t) := by
    intro s' hs'
    have hae : (s' ×ˢ t : Set (ℝ × α)) =ᵐ[ν] ((s' ∩ {r}) ×ˢ t ∪ (s' ∩ {-r}) ×ˢ t : Set (ℝ × α)) := by
      filter_upwards [hsupp] with p hp
      simp only [eq_iff_iff, Set.mem_prod, Set.mem_union, Set.mem_inter_iff,
        Set.mem_singleton_iff]
      rcases hp with h | h <;> simp [h, hrr, Ne.symm hrr]
    rw [measure_congr hae, measure_union (Set.disjoint_left.2 fun p hp1 hp2 => hrr (by
        have h1 : p.1 = r := hp1.1.2
        have h2 : p.1 = -r := hp2.1.2
        exact h1.symm.trans h2)) ((hs'.inter (measurableSet_singleton _)).prod ht)]
  have hmap : (ν.map Prod.snd) t = ν ({r} ×ˢ t) + ν ({-r} ×ˢ t) := by
    rw [Measure.map_apply measurable_snd ht]
    have := hdec Set.univ MeasurableSet.univ
    rw [Set.univ_prod] at this
    rw [this, Set.univ_inter, Set.univ_inter]
  have hc : ∀ c : ℝ, ν ((s ∩ {c}) ×ˢ t) = s.indicator (fun _ => ν ({c} ×ˢ t)) c := by
    intro c
    by_cases h : c ∈ s
    · rw [Set.inter_eq_right.2 (Set.singleton_subset_iff.2 h), Set.indicator_of_mem h]
    · rw [Set.inter_singleton_eq_empty.2 h, Set.indicator_of_notMem h]; simp
  set a := ν ({r} ×ˢ t) with ha
  have hb : ν ({-r} ×ˢ t) = a := hab.symm
  have hhalf : (2 : ℝ≥0∞)⁻¹ * (a + a) = a := by
    rw [← two_mul, ← mul_assoc, ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_mul]
  have h22 : (2 : ℝ≥0∞)⁻¹ * (1 + 1) = 1 := by
    rw [one_add_one_eq_two, ENNReal.inv_mul_cancel (by norm_num) (by norm_num)]
  rw [hmap, symLaw_apply hs, hdec s hs, hc, hc, hb]
  by_cases h1 : r ∈ s <;> by_cases h2 : -r ∈ s <;>
    simp [Set.indicator_of_mem, Set.indicator_of_notMem, h1, h2]
  · rw [h22, one_mul]
  · rw [hhalf]
  · rw [hhalf]

end ElboimSly.StrongApprox
