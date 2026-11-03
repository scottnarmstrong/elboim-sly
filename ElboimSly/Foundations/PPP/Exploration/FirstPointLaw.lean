/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.PPP.Exploration.FirstPointV
import Mathlib

/-!
# First-point law of a deterministic probe

First-point law of a deterministic probe: for `N ~ PPP(μ)`, `Law(St(N)) = K`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal NNReal

namespace ElboimSly

variable {S : Type*} [MeasurableSpace S] {μ : Measure S} [SigmaFinite μ] {R : S → ℝ≥0∞}
  {h : ℝ≥0} {W : Measure (Measure S)}

theorem measure_lt_rho_eq_zero {ν : Measure S} (hν : ν ∈ lfSet μ)
    (hreg : Reg R h Set.univ ν) : ν {x | R x < probeRho μ R h ν} = 0 := by
  refine measure_mono_null (t := ⋃ q : {q : ℚ // 0 ≤ q ∧ ratTime q < probeRho μ R h ν},
    probeRegion R (ratTime q.1)) ?_ (measure_iUnion_null fun q => ?_)
  · intro x hx
    obtain ⟨q, hq0, hq1, hq2⟩ := exists_ratTime_btwn hx
    simp only [Set.mem_iUnion]
    exact ⟨⟨q, hq0, hq2⟩, hq1.le⟩
  · exact measure_region_eq_zero_of_lt hν hreg q.2.2

theorem lintegral_probeV (hR : Measurable R) {ν : Measure S} (hν : ν ∈ lfSet μ)
    (hreg : Reg R h Set.univ ν) (hV : probeV μ R h ν Set.univ = 1) :
    ∫⁻ x, R x ∂(probeV μ R h ν) = probeRho μ R h ν := by
  have hV' : ν (probeRegion R (probeRho μ R h ν)) = 1 := by rwa [probeV_univ hν] at hV
  have hA := measurableSet_probeRegion hR (probeRho μ R h ν)
  have hnull := measure_lt_rho_eq_zero hν hreg
  unfold probeV
  rw [tau_of_mem μ hν]
  calc ∫⁻ x, R x ∂(ν.restrict (probeRegion R (probeRho μ R h ν)))
      = ∫⁻ x, probeRho μ R h ν ∂(ν.restrict (probeRegion R (probeRho μ R h ν))) := by
        refine lintegral_congr_ae ?_
        filter_upwards [ae_restrict_mem hA,
          ae_restrict_of_ae (measure_eq_zero_iff_ae_notMem.1 hnull)] with x hx hx'
        exact le_antisymm hx (not_lt.1 hx')
    _ = probeRho μ R h ν := by
        rw [lintegral_const, Measure.restrict_apply_univ, hV', mul_one]

theorem measurableSet_succ (hR : Measurable R) :
    MeasurableSet {ν : Measure S | 1 ≤ tau μ ν (probeRegion R h)} :=
  measurableSet_le measurable_const
    ((Measure.measurable_coe (measurableSet_probeRegion hR h)).comp (measurable_tau μ))

theorem map_step_restrict_succ (hW : IsPPPLaw μ W) (hP : IsProbe μ R h) :
    (W.restrict {ν | 1 ≤ tau μ ν (probeRegion R h)}).map (probeStep μ R h) =
      ((μ.restrict (probeRegion R h)).withDensity fun x => expNeg (probeMass μ R (R x))).map
        fun x => (R x, Measure.dirac x) := by
  have hR := hP.measurable
  have := hW.isProbabilityMeasure
  by_cases hh : 0 < h
  · set succ := {ν : Measure S | 1 ≤ tau μ ν (probeRegion R h)} with hsucc
    have hΦ : Measurable fun ν : Measure S => ((∫⁻ x, R x ∂ν : ℝ≥0∞), ν) :=
      (measurable_lintegral_measure hR).prodMk measurable_id
    have hV := measurable_probeV μ (h := h) hR
    have hae : probeStep μ R h =ᵐ[W.restrict succ]
        (fun ν : Measure S => ((∫⁻ x, R x ∂ν : ℝ≥0∞), ν)) ∘ probeV μ R h := by
      refine (ae_restrict_iff' (measurableSet_succ hR)).2 ?_
      filter_upwards [ae_goodSet hW hP MeasurableSet.univ, ae_succ_V_univ hW hP hh] with ν hν hV1
        hs
      obtain ⟨hlf, hreg, -, -⟩ := hν
      have := lintegral_probeV hR hlf hreg (hV1 hs)
      exact Prod.ext this.symm rfl
    rw [Measure.map_congr hae, ← Measure.map_map hΦ hV, map_probeV_restrict hW hP hh,
      diracLaw, Measure.map_map hΦ Measure.measurable_dirac]
    refine Measure.map_congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [Function.comp]
    rw [lintegral_dirac' _ hR]
  · have h0 : h = 0 := by simpa using hh
    subst h0
    have hμZ : μ (probeRegion R ((0 : ℝ≥0) : ℝ≥0∞)) = 0 := by
      have := probeMass_zero hP
      unfold probeMass at this
      simpa using this
    have hz : W {ν : Measure S | 1 ≤ tau μ ν (probeRegion R ((0 : ℝ≥0) : ℝ≥0∞))} = 0 := by
      refine measure_eq_zero_iff_ae_notMem.2 ?_
      filter_upwards [ae_goodSet hW hP MeasurableSet.univ, ae_region_zero_eq_zero hW hP] with ν hν
        h0'
      obtain ⟨hlf, -, -, -⟩ := hν
      have h0 : ν (probeRegion R ((0 : ℝ≥0) : ℝ≥0∞)) = 0 := by simpa using h0'
      simp [tau_of_mem μ hlf, h0']
    rw [Measure.restrict_eq_zero.2 hz, Measure.restrict_eq_zero.2 hμZ]
    simp

/-- First-point law of a deterministic probe: `Law(St(N)) = K`. -/
theorem map_probeStep_eq_kernel (hW : IsPPPLaw μ W) (hP : IsProbe μ R h) :
    W.map (probeStep μ R h) = probeKernel μ R h := by
  have hR := hP.measurable
  have := hW.isProbabilityMeasure
  have hstep := measurable_probeStep μ (h := h) hR
  have hsm := measurableSet_succ (μ := μ) (h := h) hR
  have hF : (W.restrict {ν : Measure S | 1 ≤ tau μ ν (probeRegion R h)}ᶜ).map
      (probeStep μ R h) = expNeg (probeMass μ R h) • Measure.dirac ((h : ℝ≥0∞), (0 : Measure S)) := by
    have hae : probeStep μ R h =ᵐ[W.restrict {ν : Measure S | 1 ≤ tau μ ν (probeRegion R h)}ᶜ]
        fun _ => ((h : ℝ≥0∞), (0 : Measure S)) := by
      refine (ae_restrict_iff' hsm.compl).2 ?_
      filter_upwards [ae_goodSet hW hP MeasurableSet.univ] with ν hν hns
      obtain ⟨hlf, hreg, -, -⟩ := hν
      obtain ⟨n, hn⟩ := hreg.2
      simp only [Set.inter_univ] at hn
      have h0 : ν (probeRegion R h) = 0 := by
        have hns' : ¬ 1 ≤ tau μ ν (probeRegion R h) := hns
        rw [tau_of_mem μ hlf, hn] at hns'
        have : n = 0 := by
          by_contra hn0
          exact hns' (by exact_mod_cast Nat.one_le_iff_ne_zero.2 hn0)
        rw [hn, this]; simp
      exact Prod.ext (probeRho_eq_h_of_measure_zero hlf h0) (probeV_eq_zero_of_measure_zero hlf h0)
    rw [Measure.map_congr hae, Measure.map_const, Measure.restrict_apply_univ]
    exact congrArg (· • _) (measure_not_succ hW hP)
  conv_lhs => rw [← Measure.restrict_add_restrict_compl (μ := W) hsm]
  rw [Measure.map_add _ _ hstep, map_step_restrict_succ hW hP, hF, probeKernel, add_comm]

omit [SigmaFinite μ] in
theorem IsPoissonPointProcess.isPPPLaw {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {N : Ω → Measure S} (hN : IsPoissonPointProcess N μ P) : IsPPPLaw μ (P.map N) := by
  have := hN.isProbabilityMeasure
  refine hN.of_map_eq (N' := fun ν : Measure S => ν) (P' := P.map N) measurable_id ?_
  simp

end ElboimSly
