/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.PPP.Exploration.FirstPointSum
import Mathlib

/-!
# The grid argument: Riemann sums for `∫ e^{-m∘R}`

First-point law of a deterministic probe, proof of (c).
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal NNReal

namespace ElboimSly

theorem expNeg_anti {a b : ℝ≥0∞} (hab : a ≤ b) (hb : b ≠ ∞) : expNeg b ≤ expNeg a := by
  unfold expNeg
  refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
  have := (ENNReal.toReal_le_toReal (ne_top_of_le_ne_top hb hab) hb).2 hab
  linarith

theorem expNeg_le_add {a d : ℝ≥0∞} (hab : a + d ≠ ∞) : expNeg a ≤ expNeg (a + d) + d := by
  have ha : a ≠ ∞ := ne_top_of_le_ne_top hab le_self_add
  have hd : d ≠ ∞ := ne_top_of_le_ne_top hab le_add_self
  unfold expNeg
  rw [ENNReal.toReal_add ha hd]
  set x := a.toReal
  set y := d.toReal
  have hy : 0 ≤ y := ENNReal.toReal_nonneg
  have hx : 0 ≤ x := ENNReal.toReal_nonneg
  conv_rhs => rw [← ENNReal.ofReal_toReal hd]
  rw [← ENNReal.ofReal_add (Real.exp_pos _).le hy]
  refine ENNReal.ofReal_le_ofReal ?_
  have h1 := Real.add_one_le_exp (-y)
  have h2 : Real.exp (-y) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have h3 : Real.exp (-x) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have h4 : Real.exp (-(x + y)) = Real.exp (-x) * Real.exp (-y) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [h4]
  have h5 := Real.exp_pos (-x)
  nlinarith [mul_nonneg h5.le (sub_nonneg.2 h2), mul_le_mul_of_nonneg_right h3 (sub_nonneg.2 h2)]

section Riemann

variable {S : Type*} [MeasurableSpace S] {μ : Measure S} [SigmaFinite μ] {R : S → ℝ≥0∞}
  {h : ℝ≥0}

/-- `∫_{D(h) ∩ B} e^{-m(R x)} μ(dx)`. -/
noncomputable def firstIntegral (μ : Measure S) (R : S → ℝ≥0∞) (h : ℝ≥0) (B : Set S) : ℝ≥0∞ :=
  ∫⁻ x in probeRegion R h ∩ B, expNeg (probeMass μ R (R x)) ∂μ

theorem measurableSet_gridCell (hR : Measurable R) (L i : ℕ) : MeasurableSet (gridCell R h L i) :=
  (measurableSet_probeRegion hR _).diff (measurableSet_probeRegion hR _)

omit [MeasurableSpace S] in
theorem pairwise_gridCell (L : ℕ) : Pairwise (Function.onFun Disjoint (gridCell R h L)) := by
  intro i j hij
  rw [Function.onFun, Set.disjoint_left]
  rintro x ⟨hxi, hxi'⟩ ⟨hxj, hxj'⟩
  rcases lt_or_gt_of_ne hij with hlt | hlt
  · exact hxj' (probeRegion_mono (by exact_mod_cast gridTime_mono (by omega)) hxi)
  · exact hxi' (probeRegion_mono (by exact_mod_cast gridTime_mono (by omega)) hxj)

variable (hP : IsProbe μ R h) {B : Set S} (hB : MeasurableSet B) {L : ℕ} (hL : 0 < L)

include hP hB hL in
omit [SigmaFinite μ] in
theorem firstIntegral_eq_sum : firstIntegral μ R h B = ∑ i ∈ Finset.Icc 1 L,
    ∫⁻ x in gridCell R h L i ∩ B, expNeg (probeMass μ R (R x)) ∂μ := by
  have hR := hP.measurable
  have hset : probeRegion R h ∩ B =
      (probeRegion R 0 ∩ B) ∪ ⋃ i ∈ Finset.Icc 1 L, (gridCell R h L i ∩ B) := by
    ext x
    constructor
    · rintro ⟨hxh, hxB⟩
      rcases exists_grid_index hL (r := R x) hxh with h0 | ⟨i, hi1, hiL, hlt, hle⟩
      · exact Or.inl ⟨h0, hxB⟩
      · right
        simp only [Set.mem_iUnion, Finset.mem_Icc]
        exact ⟨i, ⟨hi1, hiL⟩, ⟨hle, not_le.2 hlt⟩, hxB⟩
    · rintro (⟨hx0, hxB⟩ | hx)
      · exact ⟨probeRegion_mono zero_le hx0, hxB⟩
      · simp only [Set.mem_iUnion, Finset.mem_Icc] at hx
        obtain ⟨i, ⟨_, hiL⟩, ⟨hx1, _⟩, hxB⟩ := hx
        exact ⟨probeRegion_mono (by exact_mod_cast gridTime_le hL hiL) hx1, hxB⟩
  have hmeas : ∀ i, MeasurableSet (gridCell R h L i ∩ B) :=
    fun i => (measurableSet_gridCell hR L i).inter hB
  unfold firstIntegral
  rw [hset, lintegral_union (Finset.measurableSet_biUnion _ fun i _ => hmeas i)]
  · rw [setLIntegral_measure_zero _ _ (measure_mono_null Set.inter_subset_left
      (probeMass_zero hP)), zero_add]
    exact lintegral_biUnion_finset (fun i _ j _ hij =>
      (pairwise_gridCell L hij).mono Set.inter_subset_left Set.inter_subset_left)
      (fun i _ => hmeas i) _
  · rw [Set.disjoint_left]
    rintro x ⟨hx0, _⟩ hx
    simp only [Set.mem_iUnion, Finset.mem_Icc] at hx
    obtain ⟨i, _, ⟨_, hx2⟩, _⟩ := hx
    exact hx2 (probeRegion_mono zero_le hx0)

omit hL in
include hP in
omit [SigmaFinite μ] in
theorem mass_ne_top {b : ℝ≥0∞} (hb : b ≤ h) : probeMass μ R b ≠ ∞ :=
  ne_top_of_le_ne_top hP.mass_lt_top.ne (measure_mono (probeRegion_mono hb))

include hP hB hL in
omit [SigmaFinite μ] in
theorem cell_integral_bounds {i : ℕ} (hiL : i ≤ L) {ε : ℝ≥0∞}
    (hε : μ (gridCell R h L i) ≤ ε) :
    μ (gridCell R h L i ∩ B) * expNeg (probeMass μ R (gridTime h L i)) ≤
        ∫⁻ x in gridCell R h L i ∩ B, expNeg (probeMass μ R (R x)) ∂μ ∧
      ∫⁻ x in gridCell R h L i ∩ B, expNeg (probeMass μ R (R x)) ∂μ ≤
        μ (gridCell R h L i ∩ B) * (expNeg (probeMass μ R (gridTime h L i)) + ε) := by
  have hR := hP.measurable
  have hmeas : MeasurableSet (gridCell R h L i ∩ B) := (measurableSet_gridCell hR L i).inter hB
  have hsh : (gridTime h L i : ℝ≥0∞) ≤ h := by exact_mod_cast gridTime_le hL hiL
  have hab : (gridTime h L (i - 1) : ℝ≥0∞) ≤ gridTime h L i := by
    exact_mod_cast gridTime_mono (Nat.sub_le i 1)
  have hsum : probeMass μ R (gridTime h L (i - 1)) + μ (gridCell R h L i) =
      probeMass μ R (gridTime h L i) := (measure_region_cell hR hab).symm
  constructor
  · rw [mul_comm, ← setLIntegral_const]
    refine setLIntegral_mono' hmeas fun x hx => ?_
    exact expNeg_anti (monotone_probeMass μ R hx.1.1) (mass_ne_top hP hsh)
  · rw [mul_comm (μ _), ← setLIntegral_const]
    refine setLIntegral_mono' hmeas fun x hx => ?_
    have hxR : R x ≤ h := hx.1.1.trans hsh
    have h1 : expNeg (probeMass μ R (R x)) ≤ expNeg (probeMass μ R (gridTime h L (i - 1))) :=
      expNeg_anti (monotone_probeMass μ R (not_le.1 hx.1.2).le) (mass_ne_top hP hxR)
    have h2 := expNeg_le_add (a := probeMass μ R (gridTime h L (i - 1)))
      (d := μ (gridCell R h L i)) (by rw [hsum]; exact mass_ne_top hP hsh)
    rw [hsum] at h2
    exact h1.trans (h2.trans (by gcongr))

include hP hB hL in
omit [SigmaFinite μ] in
theorem sum_measure_cell_le :
    ∑ i ∈ Finset.Icc 1 L, μ (gridCell R h L i ∩ B) ≤ μ (probeRegion R h) := by
  have hR := hP.measurable
  rw [← measure_biUnion_finset (fun i _ j _ hij =>
      (pairwise_gridCell L hij).mono Set.inter_subset_left Set.inter_subset_left)
    (fun i _ => (measurableSet_gridCell hR L i).inter hB)]
  refine measure_mono (Set.iUnion₂_subset fun i hi => ?_)
  rw [Finset.mem_Icc] at hi
  exact Set.inter_subset_left.trans fun x hx =>
    probeRegion_mono (by exact_mod_cast gridTime_le hL hi.2) hx.1

include hP hB hL in
omit [SigmaFinite μ] in
theorem sum_le_firstIntegral :
    ∑ i ∈ Finset.Icc 1 L, μ (gridCell R h L i ∩ B) * expNeg (probeMass μ R (gridTime h L i)) ≤
      firstIntegral μ R h B := by
  rw [firstIntegral_eq_sum hP hB hL]
  refine Finset.sum_le_sum fun i hi => ?_
  rw [Finset.mem_Icc] at hi
  exact (cell_integral_bounds hP hB hL hi.2 (le_top : μ _ ≤ ⊤)).1

include hP hB hL in
omit [SigmaFinite μ] in
theorem firstIntegral_le_sum_add {ε : ℝ≥0∞} (hε : ∀ i ∈ Finset.Icc 1 L, μ (gridCell R h L i) ≤ ε) :
    firstIntegral μ R h B ≤
      ∑ i ∈ Finset.Icc 1 L, μ (gridCell R h L i ∩ B) * expNeg (probeMass μ R (gridTime h L i)) +
        ε * μ (probeRegion R h) := by
  rw [firstIntegral_eq_sum hP hB hL]
  calc _ ≤ ∑ i ∈ Finset.Icc 1 L, (μ (gridCell R h L i ∩ B) *
        expNeg (probeMass μ R (gridTime h L i)) + ε * μ (gridCell R h L i ∩ B)) := by
        refine Finset.sum_le_sum fun i hi => ?_
        have hi' := Finset.mem_Icc.1 hi
        refine (cell_integral_bounds hP hB hL hi'.2 (hε i hi)).2.trans (le_of_eq ?_)
        ring
    _ = _ := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    _ ≤ _ := by
        gcongr
        exact sum_measure_cell_le hP hB hL

end Riemann

end ElboimSly
