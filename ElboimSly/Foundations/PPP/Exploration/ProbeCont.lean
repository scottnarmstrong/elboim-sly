/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.PPP.Exploration.ProbeRC
import Mathlib

/-!
# Continuity of the probed mass

Elementary properties of probes (a): `m` is nondecreasing and continuous on `[0, h]` with `m 0 = 0`.

We prove that `t ↦ m(min t h)` is continuous on `ℝ` and deduce that uniform grids eventually have
small cells: `exists_grid_small`.
-/

@[expose] public section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

namespace ElboimSly

variable {S : Type*} [MeasurableSpace S] {μ : Measure S} {R : S → ℝ≥0∞} {h : ℝ≥0}

/-- `t ↦ m(min t h)` on the reals. -/
noncomputable def massFn (μ : Measure S) (R : S → ℝ≥0∞) (h : ℝ≥0) (t : ℝ) : ℝ≥0∞ :=
  probeMass μ R (ENNReal.ofReal (min t (h : ℝ)))

theorem monotone_massFn : Monotone (massFn μ R h) := fun _ _ hab =>
  measure_mono (probeRegion_mono (ENNReal.ofReal_le_ofReal (min_le_min_right _ hab)))

theorem massFn_le (t : ℝ) : massFn μ R h t ≤ probeMass μ R h := by
  refine measure_mono (probeRegion_mono ?_)
  calc ENNReal.ofReal (min t (h : ℝ)) ≤ ENNReal.ofReal (h : ℝ) :=
        ENNReal.ofReal_le_ofReal (min_le_right _ _)
    _ = h := ENNReal.ofReal_coe_nnreal

theorem massFn_of_nonpos {t : ℝ} (ht : t ≤ 0) : massFn μ R h t = probeMass μ R 0 := by
  unfold massFn
  rw [ENNReal.ofReal_of_nonpos ((min_le_left _ _).trans ht)]

theorem massFn_of_ge {t : ℝ} (ht : (h : ℝ) ≤ t) : massFn μ R h t = probeMass μ R h := by
  unfold massFn
  rw [min_eq_right ht, ENNReal.ofReal_coe_nnreal]

theorem massFn_of_mem {t : ℝ} (_h0 : 0 ≤ t) (ht : t ≤ (h : ℝ)) :
    massFn μ R h t = probeMass μ R (ENNReal.ofReal t) := by
  unfold massFn
  rw [min_eq_left ht]

theorem massFn_lt_top (hP : IsProbe μ R h) (t : ℝ) : massFn μ R h t < ∞ :=
  lt_of_le_of_lt (massFn_le t) hP.mass_lt_top

theorem probeMass_zero (hP : IsProbe μ R h) : probeMass μ R 0 = 0 := by
  unfold probeMass
  have : probeRegion R 0 = {x | R x = ((0 : ℝ≥0) : ℝ≥0∞)} := by
    ext x; simp [probeRegion]
  rw [this]
  exact hP.measure_eq_zero 0 bot_le

section Cont

theorem measure_region_eq_iInf' [SigmaFinite μ] (hP : IsProbe μ R h) {r : ℝ≥0∞} (hr : r < h) :
    probeMass μ R r = ⨅ q : RatBetween h r, probeMass μ R (ratTime q.1) := by
  have := measure_region_eq_iInf hP.measurable hr MeasurableSet.univ
    (ν := μ) (by simpa using hP.mass_lt_top.ne)
  simpa [probeMass] using this


variable (hP : IsProbe μ R h)
include hP

theorem probeMass_eq_iSup_rat {t : ℝ} (h0 : 0 < t) (hth : t ≤ (h : ℝ)) :
    probeMass μ R (ENNReal.ofReal t) =
      ⨆ q : {q : ℚ // 0 ≤ q ∧ ratTime q < ENNReal.ofReal t}, probeMass μ R (ratTime q.1) := by
  have hmeas := hP.measurable
  have hunion : ⋃ q : {q : ℚ // 0 ≤ q ∧ ratTime q < ENNReal.ofReal t},
      probeRegion R (ratTime q.1) = {x | R x < ENNReal.ofReal t} := by
    ext x
    simp only [mem_iUnion, probeRegion, mem_ofPred_eq]
    constructor
    · rintro ⟨q, hq⟩
      exact lt_of_le_of_lt hq q.2.2
    · intro hx
      obtain ⟨q, hq0, hq1, hq2⟩ := exists_ratTime_btwn hx
      exact ⟨⟨q, hq0, hq2⟩, hq1.le⟩
  have hnull : μ {x | R x = ENNReal.ofReal t} = 0 := by
    have := hP.measure_eq_zero (Real.toNNReal t) (by
      rw [← NNReal.coe_le_coe]; simpa [Real.coe_toNNReal t h0.le] using hth)
    simpa [ENNReal.ofReal] using this
  have hsplit : probeMass μ R (ENNReal.ofReal t) = μ {x | R x < ENNReal.ofReal t} := by
    unfold probeMass
    have : probeRegion R (ENNReal.ofReal t) =
        {x | R x < ENNReal.ofReal t} ∪ {x | R x = ENNReal.ofReal t} := by
      ext x; simp [probeRegion, le_iff_lt_or_eq]
    rw [this]
    exact le_antisymm ((measure_union_le _ _).trans (by simp [hnull])) (measure_mono subset_union_left)
  rw [hsplit, ← hunion]
  refine Directed.measure_iUnion ?_
  intro q q'
  refine ⟨⟨max q.1 q'.1, le_max_of_le_left q.2.1, ?_⟩, ?_, ?_⟩
  · rcases le_total q.1 q'.1 with hle | hle
    · rw [max_eq_right hle]; exact q'.2.2
    · rw [max_eq_left hle]; exact q.2.2
  · exact probeRegion_mono (ratTime_mono (le_max_left _ _))
  · exact probeRegion_mono (ratTime_mono (le_max_right _ _))

theorem tendsto_massFn_nhdsLT (t : ℝ) :
    Tendsto (massFn μ R h) (𝓝[<] t) (𝓝 (massFn μ R h t)) := by
  by_cases h0 : t ≤ 0
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    rw [massFn_of_nonpos (le_of_lt (lt_of_lt_of_le hs h0)), massFn_of_nonpos h0]
  push Not at h0
  by_cases hth : (h : ℝ) < t
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [Ioo_mem_nhdsLT hth] with s hs
    rw [massFn_of_ge hs.1.le, massFn_of_ge hth.le]
  push Not at hth
  have key := Monotone.tendsto_nhdsLT (monotone_massFn (μ := μ) (R := R) (h := h)) t
  suffices hs : sSup (massFn μ R h '' Iio t) = massFn μ R h t by rwa [hs] at key
  refine le_antisymm (csSup_le ⟨_, mem_image_of_mem _ (show t - 1 ∈ Iio t by simp)⟩ ?_) ?_
  · rintro _ ⟨s, hs, rfl⟩
    exact monotone_massFn hs.le
  · rw [massFn_of_mem h0.le hth, probeMass_eq_iSup_rat hP h0 hth]
    refine iSup_le fun q => ?_
    have hq : (q.1 : ℝ) < t := by
      have h1 : ratTime q.1 = ENNReal.ofReal (q.1 : ℝ) := rfl
      have := q.2.2
      rw [h1] at this
      exact (ENNReal.ofReal_lt_ofReal_iff h0).1 this
    have hqh : (q.1 : ℝ) ≤ h := hq.le.trans hth
    have e : massFn μ R h (q.1 : ℝ) = probeMass μ R (ratTime q.1) := by
      rw [massFn_of_mem (Rat.cast_nonneg.2 q.2.1) hqh]; rfl
    rw [← e]
    exact le_sSup (mem_image_of_mem _ hq)

theorem tendsto_massFn_nhdsGT [SigmaFinite μ] (t : ℝ) :
    Tendsto (massFn μ R h) (𝓝[>] t) (𝓝 (massFn μ R h t)) := by
  by_cases hth : (h : ℝ) ≤ t
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    rw [massFn_of_ge (hth.trans (le_of_lt hs)), massFn_of_ge hth]
  push Not at hth
  by_cases h0 : t < 0
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT h0] with s hs
    rw [massFn_of_nonpos hs.2.le, massFn_of_nonpos h0.le]
  push Not at h0
  have key := Monotone.tendsto_nhdsGT (monotone_massFn (μ := μ) (R := R) (h := h)) t
  suffices hs : sInf (massFn μ R h '' Ioi t) = massFn μ R h t by rwa [hs] at key
  refine le_antisymm ?_ (le_csInf ⟨_, mem_image_of_mem _ (show t + 1 ∈ Ioi t by simp)⟩ ?_)
  · have hlt : ENNReal.ofReal t < h := by
      rw [← ENNReal.ofReal_coe_nnreal]
      exact (ENNReal.ofReal_lt_ofReal_iff (lt_of_le_of_lt h0 hth)).2 hth
    rw [massFn_of_mem h0 hth.le, measure_region_eq_iInf' hP hlt]
    refine le_iInf fun q => ?_
    have hq : t < (q.1 : ℝ) := by
      have h1 : ratTime q.1 = ENNReal.ofReal (q.1 : ℝ) := rfl
      have h2 : ENNReal.ofReal t < ratTime q.1 := q.2.2.1
      rw [h1] at h2
      exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg h0).1 h2
    have hqh : (q.1 : ℝ) ≤ h := by
      have h1 : ratTime q.1 = ENNReal.ofReal (q.1 : ℝ) := rfl
      have h2 : ratTime q.1 < (h : ℝ≥0∞) := q.2.2.2
      have h3 : ENNReal.ofReal (q.1 : ℝ) < ENNReal.ofReal (h : ℝ) :=
        lt_of_eq_of_lt h1.symm (h2.trans_eq ENNReal.ofReal_coe_nnreal.symm)
      exact ((ENNReal.ofReal_lt_ofReal_iff (lt_of_le_of_lt h0 hth)).1 h3).le
    have e : massFn μ R h (q.1 : ℝ) = probeMass μ R (ratTime q.1) := by
      rw [massFn_of_mem (Rat.cast_nonneg.2 q.2.1) hqh]; rfl
    rw [← e]
    exact csInf_le ⟨0, by rintro _ ⟨s, _, rfl⟩; exact bot_le⟩ (mem_image_of_mem _ hq)
  · rintro _ ⟨s, hs, rfl⟩
    exact monotone_massFn hs.le

theorem continuous_massFn [SigmaFinite μ] : Continuous (massFn μ R h) := by
  refine continuous_iff_continuousAt.2 fun t => ?_
  rw [continuousAt_iff_continuous_left_right]
  exact ⟨continuousWithinAt_Iio_iff_Iic.1 (tendsto_massFn_nhdsLT hP t),
    continuousWithinAt_Ioi_iff_Ici.1 (tendsto_massFn_nhdsGT hP t)⟩

theorem continuous_massFn_toReal [SigmaFinite μ] :
    Continuous fun t => (massFn μ R h t).toReal :=
  continuous_iff_continuousAt.2 fun t =>
    (ENNReal.continuousAt_toReal (massFn_lt_top hP t).ne).comp (continuous_massFn hP).continuousAt

end Cont

/-- The uniform grid `i h / L`. -/
noncomputable def gridTime (h : ℝ≥0) (L i : ℕ) : ℝ≥0 := h * i / L

theorem gridTime_le {L i : ℕ} (hL : 0 < L) (hi : i ≤ L) : gridTime h L i ≤ h := by
  unfold gridTime
  rw [div_le_iff₀ (by exact_mod_cast hL)]
  gcongr

theorem gridTime_mono {L i j : ℕ} (hij : i ≤ j) : gridTime h L i ≤ gridTime h L j := by
  unfold gridTime
  gcongr

theorem coe_gridTime_sub {L : ℕ} (hL : 0 < L) (j : ℕ) :
    (gridTime h L (j + 1) : ℝ) - gridTime h L j = h / L := by
  unfold gridTime
  push_cast
  have : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  field_simp
  ring

theorem measure_diff_region [SigmaFinite μ] (hP : IsProbe μ R h) {a b : ℝ≥0} (hab : a ≤ b)
    (hb : b ≤ h) :
    μ (probeRegion R b \ probeRegion R a) = massFn μ R h b - massFn μ R h a := by
  have ha' : (a : ℝ) ≤ h := by exact_mod_cast hab.trans hb
  have hb' : (b : ℝ) ≤ h := by exact_mod_cast hb
  rw [massFn_of_mem (NNReal.coe_nonneg a) ha', massFn_of_mem (NNReal.coe_nonneg b) hb', ENNReal.ofReal_coe_nnreal,
    ENNReal.ofReal_coe_nnreal]
  unfold probeMass
  rw [measure_sdiff (probeRegion_mono (by exact_mod_cast hab))
    (measurableSet_probeRegion hP.measurable _).nullMeasurableSet]
  refine ne_top_of_le_ne_top hP.mass_lt_top.ne (measure_mono (probeRegion_mono ?_))
  exact_mod_cast hab.trans hb

/-- Uniform grids eventually have small cells. -/
theorem exists_grid_small [SigmaFinite μ] (hP : IsProbe μ R h) {ε : ℝ≥0} (hε : 0 < ε) :
    ∃ L : ℕ, 0 < L ∧ ∀ i, 1 ≤ i → i ≤ L →
      μ (probeRegion R (gridTime h L i) \ probeRegion R (gridTime h L (i - 1))) ≤ ε := by
  have hcont := continuous_massFn_toReal hP
  have huc := (isCompact_Icc (a := (0 : ℝ)) (b := h)).uniformContinuousOn_of_continuous
    hcont.continuousOn
  obtain ⟨δ, hδ, hδ'⟩ := Metric.uniformContinuousOn_iff.1 huc (ε : ℝ) (by exact_mod_cast hε)
  obtain ⟨L, hL⟩ := exists_nat_gt ((h : ℝ) / δ)
  have hL0 : 0 < L := by
    have : (0 : ℝ) < L := lt_of_le_of_lt (by positivity) hL
    exact_mod_cast this
  refine ⟨L, hL0, fun i hi1 hiL => ?_⟩
  obtain ⟨j, hj⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  subst hj
  rw [Nat.add_sub_cancel]
  have hab : gridTime h L j ≤ gridTime h L (j + 1) := gridTime_mono (Nat.le_succ j)
  have hb : gridTime h L (j + 1) ≤ h := gridTime_le hL0 hiL
  have ha : gridTime h L j ≤ h := hab.trans hb
  rw [measure_diff_region hP hab hb]
  have hsub0 := coe_gridTime_sub (h := h) hL0 j
  have hdist : dist ((gridTime h L j : ℝ≥0) : ℝ) (gridTime h L (j + 1)) < δ := by
    rw [Real.dist_eq, abs_sub_comm, abs_of_nonneg (by rw [hsub0]; positivity), hsub0,
      div_lt_iff₀ (by exact_mod_cast hL0)]
    rw [div_lt_iff₀ hδ] at hL
    linarith
  have hmem : ∀ x : ℝ≥0, x ≤ h → (x : ℝ) ∈ Set.Icc (0 : ℝ) h := fun x hx =>
    ⟨x.2, by exact_mod_cast hx⟩
  have key := hδ' _ (hmem _ ha) _ (hmem _ hb) hdist
  have hle : massFn μ R h (gridTime h L j) ≤ massFn μ R h (gridTime h L (j + 1)) :=
    monotone_massFn (by exact_mod_cast hab)
  have hfin1 := (massFn_lt_top hP (gridTime h L (j + 1))).ne
  have hfin0 := (massFn_lt_top hP (gridTime h L j)).ne
  simp only [Real.dist_eq] at key
  rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.2 ((ENNReal.toReal_le_toReal hfin0 hfin1).2 hle))]
    at key
  have hsub : (massFn μ R h (gridTime h L (j + 1)) - massFn μ R h (gridTime h L j)).toReal <
      (ε : ℝ) := by
    rw [ENNReal.toReal_sub_of_le hle hfin1]; exact key
  exact (ENNReal.toReal_le_toReal (ENNReal.sub_ne_top hfin1) ENNReal.coe_ne_top).1
    (by simpa using hsub.le)

end ElboimSly
