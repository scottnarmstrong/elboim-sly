/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.PPP.Exploration.OneStepCount
import Mathlib

/-!
# The unexplored part after one step

The unexplored part after one step. For `N, N'' ~ PPP(μ)` independent, `M' = 𝖬(N, N'')` is a
`PPP(μ)` independent of `St(N)`. On `Measure S × Measure S` with `W ⊗ W`:
`Law(St(ν), 𝖬(ν, ν'')) = K ⊗ W`.
-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace ElboimSly

variable {S : Type*} [MeasurableSpace S] {μ : Measure S} [SigmaFinite μ] {R : S → ℝ≥0∞}
  {h : ℝ≥0} {W : Measure (Measure S)}

theorem oneStep_pos (hW : IsPPPLaw μ W) (hP : IsProbe μ R h) (hh : 0 < h) :
    (W.prod W).map (fun p => (probeStep μ R h p.1, probeRenew μ R h p.1 p.2)) =
      (W.map (probeStep μ R h)).prod W := by
  have := hW.isProbabilityMeasure
  have hR := hP.measurable
  have hstep := measurable_probeStep μ (h := h) hR
  have hren := measurable_probeRenew μ (h := h) hR
  have hmeas : Measurable fun p : Measure S × Measure S =>
      (probeStep μ R h p.1, probeRenew μ R h p.1 p.2) :=
    (hstep.comp measurable_fst).prodMk hren
  have hcountsp : IsCountablySpanning {G : Set (Outcome S) | MeasurableSet G} :=
    ⟨fun _ => Set.univ, fun _ => (MeasurableSet.univ : MeasurableSet (Set.univ : Set (Outcome S))),
      Set.iUnion_const _⟩
  have hcountsp2 : IsCountablySpanning (countEvents S) :=
    ⟨fun _ => Set.univ, fun _ => univ_mem_countEvents, Set.iUnion_const _⟩
  have hgen : (inferInstance : MeasurableSpace (Outcome S × Measure S)) =
      MeasurableSpace.generateFrom
        (Set.image2 (· ×ˢ ·) {G : Set (Outcome S) | MeasurableSet G} (countEvents S)) := by
    rw [← generateFrom_prod_eq hcountsp hcountsp2, MeasurableSpace.generateFrom_measurableSet,
      generateFrom_countEvents]
  have key : ∀ s ∈ Set.image2 (· ×ˢ ·) {G : Set (Outcome S) | MeasurableSet G} (countEvents S),
      ((W.prod W).map (fun p => (probeStep μ R h p.1, probeRenew μ R h p.1 p.2))) s =
        ((W.map (probeStep μ R h)).prod W) s := by
    rintro _ ⟨G, hG, F0, hF0, rfl⟩
    obtain ⟨l, B, C0, hB, hC0, rfl⟩ := hF0
    have hG' : MeasurableSet G := hG
    have hF : MeasurableSet {κ : Measure S | (fun j => κ (B j)) ∈ C0} :=
      countEvents_measurableSet ⟨l, B, C0, hB, hC0, rfl⟩
    rw [Measure.map_apply hmeas (hG'.prod hF), Measure.prod_prod]
    have h1 := lintegral_step_renew_count hW hP hh (g := G.indicator 1)
      (measurable_one.indicator hG') (fun o => by by_cases ho : o ∈ G <;> simp [Set.indicator, ho])
      hB hC0
    have e1 : ∀ p : Measure S × Measure S,
        (G.indicator (1 : Outcome S → ℝ≥0∞)) (probeStep μ R h p.1) *
          {κ : Measure S | (fun j => κ (B j)) ∈ C0}.indicator 1 (probeRenew μ R h p.1 p.2) =
        ((fun p : Measure S × Measure S => (probeStep μ R h p.1, probeRenew μ R h p.1 p.2)) ⁻¹'
          (G ×ˢ {κ : Measure S | (fun j => κ (B j)) ∈ C0})).indicator 1 p := by
      intro p
      by_cases h1 : probeStep μ R h p.1 ∈ G <;>
        by_cases h2 : probeRenew μ R h p.1 p.2 ∈ {κ : Measure S | (fun j => κ (B j)) ∈ C0} <;>
        simp [Set.indicator, h1, h2]
    simp_rw [e1] at h1
    rw [lintegral_indicator_one (hmeas (hG'.prod hF))] at h1
    rw [h1, ← lintegral_indicator_one hG', ← lintegral_map (measurable_one.indicator hG') hstep]
  exact ext_of_generate_finite _ hgen (IsPiSystem.prod MeasurableSpace.isPiSystem_measurableSet isPiSystem_countEvents) key
    (key _ ⟨Set.univ, (MeasurableSet.univ : MeasurableSet (Set.univ : Set (Outcome S))), Set.univ,
      univ_mem_countEvents, by simp⟩)

omit [SigmaFinite μ] in
theorem probeKernel_zero (hP : IsProbe μ R 0) :
    probeKernel μ R 0 = Measure.dirac (((0 : ℝ≥0) : ℝ≥0∞), (0 : Measure S)) := by
  have hm : μ (probeRegion R ((0 : ℝ≥0) : ℝ≥0∞)) = 0 := by
    have := probeMass_zero hP
    unfold probeMass at this
    simpa using this
  have hm' : probeMass μ R ((0 : ℝ≥0) : ℝ≥0∞) = 0 := hm
  unfold probeKernel
  rw [hm', Measure.restrict_eq_zero.2 hm]
  simp [expNeg]

theorem oneStep_zero (hW : IsPPPLaw μ W) (hP : IsProbe μ R 0) :
    (W.prod W).map (fun p => (probeStep μ R 0 p.1, probeRenew μ R 0 p.1 p.2)) =
      (Measure.dirac (((0 : ℝ≥0) : ℝ≥0∞), (0 : Measure S))).prod W := by
  have := hW.isProbabilityMeasure
  have hR := hP.measurable
  have hgood : ∀ᵐ p ∂(W.prod W), (probeStep μ R 0 p.1, probeRenew μ R 0 p.1 p.2) =
      ((((0 : ℝ≥0) : ℝ≥0∞), (0 : Measure S)), p.1) := by
    have h1 := (measurePreserving_fst (μ := W) (ν := W)).quasiMeasurePreserving.ae
      (hW.ae_mem_lfSet.and (ae_region_zero_eq_zero hW hP))
    have h2 := (measurePreserving_snd (μ := W) (ν := W)).quasiMeasurePreserving.ae
      (hW.ae_mem_lfSet.and (ae_region_zero_eq_zero hW hP))
    filter_upwards [h1, h2] with p hp1 hp2
    have h0 : p.1 (probeRegion R ((0 : ℝ≥0) : ℝ≥0∞)) = 0 := by simpa using hp1.2
    have h0' : p.2 (probeRegion R ((0 : ℝ≥0) : ℝ≥0∞)) = 0 := by simpa using hp2.2
    have hρ := probeRho_eq_h_of_measure_zero hp1.1 h0
    refine Prod.ext (Prod.ext hρ (probeV_eq_zero_of_measure_zero hp1.1 h0)) ?_
    show probeRenew μ R 0 p.1 p.2 = p.1
    unfold probeRenew
    rw [hρ, tau_of_mem μ hp1.1, tau_of_mem μ hp2.1, Measure.restrict_eq_zero.2 h0', add_zero]
    refine Measure.restrict_eq_self_of_ae_mem ?_
    exact measure_eq_zero_iff_ae_notMem.1 h0
  rw [Measure.map_congr hgood, Measure.dirac_prod]
  show Measure.map ((Prod.mk (((0 : ℝ≥0) : ℝ≥0∞), (0 : Measure S))) ∘ Prod.fst) (W.prod W) = _
  rw [← Measure.map_map (measurable_prodMk_left : Measurable (Prod.mk (((0 : ℝ≥0) : ℝ≥0∞),
    (0 : Measure S)))) measurable_fst]
  simp

/-- The unexplored part after one step: `Law(St(ν), 𝖬(ν, ν'')) = K ⊗ W` for independent PPPs. -/
theorem oneStep_law (hW : IsPPPLaw μ W) (hP : IsProbe μ R h) :
    (W.prod W).map (fun p => (probeStep μ R h p.1, probeRenew μ R h p.1 p.2)) =
      (probeKernel μ R h).prod W := by
  rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ h) with h0 | hh
  · subst h0
    rw [oneStep_zero hW hP, probeKernel_zero hP]
  · rw [oneStep_pos hW hP hh, map_probeStep_eq_kernel hW hP]

end ElboimSly
