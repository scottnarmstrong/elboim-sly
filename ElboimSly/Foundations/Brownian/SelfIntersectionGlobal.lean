/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Brownian.SelfIntersectionGood
public import ElboimSly.Foundations.Brownian.Sup
public import ElboimSly.Foundations.Brownian.Oscillation
public import ElboimSly.Foundations.Brownian.Occupation

import Mathlib

/-!
# The good event is likely

ES22 Claim 9.4, Step 4.

`P (good (t+1))ᶜ` is at most the sum of three bounds:

* Gaussian maximal bound (a) for the sup condition;
* Oscillation for the oscillation condition;
* ES22 Lemma 9.3: occupation of a cube at integer times, with a union bound over the lattice points of the box, for the counts.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal ENNReal

namespace ElboimSly.Brownian

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → R5}

lemma goodSup_compl_le [IsProbabilityMeasure P] (hB : IsStandardBrownianMotion 5 B P)
    {t : ℝ} (ht : 0 < t) {a : ℝ≥0} (ha : (a : ℝ) = t + 1) :
    P (goodSup B t a)ᶜ ≤ 20 * ENNReal.ofReal (Real.exp (-t ^ 2 / (2 * (t + 1)))) := by
  have ha0 : a ≠ 0 := by
    intro h; rw [h] at ha; simp at ha; linarith
  have := hB.sup_norm_le ha0 ht
  rw [ha] at this
  refine le_trans (measure_mono ?_) (this.trans (le_of_eq ?_))
  · intro ω hω
    simp only [goodSup, mem_compl_iff, Set.mem_ofPred_eq, not_forall, not_le] at hω
    obtain ⟨u, hu, hlt⟩ := hω
    exact ⟨u, hu, hlt.le⟩
  · norm_num

lemma goodOsc_compl_le [IsProbabilityMeasure P] (hB : IsStandardBrownianMotion 5 B P)
    {ρ : ℝ} (hρ : 0 < ρ) {a : ℝ≥0} (ha : a ≠ 0) :
    P (goodOsc B ρ a)ᶜ ≤ (20 * (⌈(a : ℝ≥0) / 1⌉₊ : ℕ) : ℝ≥0∞) *
      ENNReal.ofReal (Real.exp (-ρ ^ 2 / 16)) := by
  have := hB.oscillation_le (T := a) (h := 1) ha one_ne_zero hρ one_pos
  refine le_trans (measure_mono ?_) (this.trans (le_of_eq ?_))
  · intro ω hω
    simp only [goodOsc, mem_compl_iff, Set.mem_ofPred_eq, not_forall, not_le] at hω
    obtain ⟨p, hp, hlt⟩ := hω
    refine ⟨p.1, p.2, hp.1.2, hp.2.1.2, hp.2.2, ?_⟩
    simpa using hlt.le
  · norm_num

omit mΩ in
/-- The visit count up to time `n` is bounded by the total count of visits. -/
lemma visitCount_le_tsum (ω : Ω) (x : R5) (R₃ : ℝ) (n : ℕ) :
    (visitCount B ω x R₃ n : ℝ≥0∞) ≤
      ∑' i : ℕ, {ω | (0 : R5) + (1 : ℝ) • B (i : ℝ≥0) ω ∈ Metric.closedBall x R₃}.indicator
        (1 : Ω → ℝ≥0∞) ω := by
  have h1 : (visitCount B ω x R₃ n : ℝ≥0∞) = ∑ i ∈ (Finset.range (n + 1)),
      {ω | (0 : R5) + (1 : ℝ) • B (i : ℝ≥0) ω ∈ Metric.closedBall x R₃}.indicator
        (1 : Ω → ℝ≥0∞) ω := by
    simp only [visitCount, Finset.card_filter, Nat.cast_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h : ‖B (i : ℝ≥0) ω - x‖ ≤ R₃
    · have : (0 : R5) + (1 : ℝ) • B (i : ℝ≥0) ω ∈ Metric.closedBall x R₃ := by
        simpa [dist_eq_norm] using h
      rw [Set.indicator_of_mem (show ω ∈ {ω | (0 : R5) + (1 : ℝ) • B (i : ℝ≥0) ω ∈
        Metric.closedBall x R₃} from this)]
      simp [h]
    · have : (0 : R5) + (1 : ℝ) • B (i : ℝ≥0) ω ∉ Metric.closedBall x R₃ := by
        simpa [dist_eq_norm] using h
      rw [Set.indicator_of_notMem (show ω ∉ {ω | (0 : R5) + (1 : ℝ) • B (i : ℝ≥0) ω ∈
        Metric.closedBall x R₃} from this)]
      simp [h]
  rw [h1]
  exact ENNReal.sum_le_tsum _

lemma goodOcc_compl_le [IsProbabilityMeasure P] (hB : IsStandardBrownianMotion 5 B P)
    {t R₃ M : ℝ} (hR : 1 ≤ R₃) (hM : 0 ≤ M) (a : ℝ≥0) :
    P (goodOcc B t R₃ M a)ᶜ ≤ ((latticeBox t).card : ℝ≥0∞) *
      ENNReal.ofReal (2 * Real.exp (-(cocc 5) * (M / R₃ ^ 2))) := by
  have hR0 : 0 < R₃ := by linarith
  have hsub : (goodOcc B t R₃ M a)ᶜ ⊆ ⋃ x ∈ latticeBox t,
      {ω | ENNReal.ofReal ((M / R₃ ^ 2) * R₃ ^ 2) <
        ∑' i : ℕ, {ω | (0 : R5) + (1 : ℝ) • B (i : ℝ≥0) ω ∈
          Metric.closedBall (latticePt x) R₃}.indicator (1 : Ω → ℝ≥0∞) ω} := by
    intro ω hω
    simp only [goodOcc, mem_compl_iff, Set.mem_ofPred_eq, not_forall, not_le] at hω
    obtain ⟨x, hx, hlt⟩ := hω
    simp only [mem_iUnion, Set.mem_ofPred_eq]
    refine ⟨x, hx, ?_⟩
    rw [div_mul_cancel₀ _ (by positivity)]
    calc ENNReal.ofReal M < ((visitCount B ω (latticePt x) R₃ ⌊(a : ℝ)⌋₊ : ℕ) : ℝ≥0∞) := by
          rw [← ENNReal.ofReal_natCast]
          exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 hlt
      _ ≤ _ := visitCount_le_tsum ω _ _ _
  refine le_trans (measure_mono hsub) ?_
  refine le_trans (measure_biUnion_finset_le _ _) ?_
  have hx : ∀ x ∈ latticeBox t, P {ω | ENNReal.ofReal ((M / R₃ ^ 2) * R₃ ^ 2) <
        ∑' i : ℕ, {ω | (0 : R5) + (1 : ℝ) • B (i : ℝ≥0) ω ∈
          Metric.closedBall (latticePt x) R₃}.indicator (1 : Ω → ℝ≥0∞) ω} ≤
      ENNReal.ofReal (2 * Real.exp (-(cocc 5) * (M / R₃ ^ 2))) := fun x _ =>
    occupation_le hB (by norm_num) 0 (latticePt x) le_rfl hR
      Metric.isClosed_closedBall.measurableSet (Metric.closedBall_subset_closedBall le_rfl)
      (div_nonneg hM (by positivity))
  calc _ ≤ ∑ _x ∈ latticeBox t, ENNReal.ofReal (2 * Real.exp (-(cocc 5) * (M / R₃ ^ 2))) :=
        Finset.sum_le_sum hx
    _ = _ := by simp

/-- ES22 Claim 9.4, Step 4: the good event up to time `t + 1` fails with
probability at most `20 e^{-t²/(2(t+1))} + 20 ⌈t+1⌉ e^{-ρ²/16} + #box · 2 e^{-c_occ M/R₃²}`. -/
theorem good_compl_le [IsProbabilityMeasure P] (hB : IsStandardBrownianMotion 5 B P)
    {t ρ R₃ M : ℝ} (ht : 1 ≤ t) (hρ : 0 < ρ) (hR : 1 ≤ R₃) (hM : 0 ≤ M) {a : ℝ≥0}
    (ha : (a : ℝ) = t + 1) :
    P (good B t ρ R₃ M a)ᶜ ≤
      20 * ENNReal.ofReal (Real.exp (-t ^ 2 / (2 * (t + 1)))) +
      (20 * (⌈t + 1⌉₊ : ℕ) : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-ρ ^ 2 / 16)) +
      ((latticeBox t).card : ℝ≥0∞) *
        ENNReal.ofReal (2 * Real.exp (-(cocc 5) * (M / R₃ ^ 2))) := by
  have ha0 : a ≠ 0 := by
    intro h; rw [h] at ha; simp at ha; linarith
  have h1 := goodSup_compl_le hB (by linarith : 0 < t) ha
  have h2 := goodOsc_compl_le hB hρ ha0
  have h3 := goodOcc_compl_le hB (t := t) hR hM a
  have hceil : ⌈(a : ℝ≥0) / 1⌉₊ = ⌈t + 1⌉₊ := by
    rw [div_one, ← ha]
    exact Nonneg.nat_ceil_coe a
  rw [hceil] at h2
  have e : (good B t ρ R₃ M a)ᶜ ⊆ (goodSup B t a)ᶜ ∪ (goodOsc B ρ a)ᶜ ∪ (goodOcc B t R₃ M a)ᶜ := by
    intro ω hω
    simp only [good, mem_compl_iff, mem_inter_iff, not_and_or] at hω
    simp only [mem_union, mem_compl_iff]
    tauto
  refine le_trans (measure_mono e) ?_
  refine le_trans (measure_union_le _ _) ?_
  gcongr
  refine le_trans (measure_union_le _ _) ?_
  gcongr

end ElboimSly.Brownian
