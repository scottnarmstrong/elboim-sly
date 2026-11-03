/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.PPP.Exploration.OneStepLimit
import Mathlib

/-!
# One step: count events

The unexplored part after one step, Step 2: for a count event `F`,
`E[g(St ν) 1_F(𝖬(ν,ν''))] = E[g(St ν)] W(F)` for `g ≤ 1`.
-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace ElboimSly

variable {S : Type*} [MeasurableSpace S] {μ : Measure S} [SigmaFinite μ] {R : S → ℝ≥0∞}
  {h : ℝ≥0} {W : Measure (Measure S)}

omit [SigmaFinite μ] in
theorem ae_gridNat (hW : IsPPPLaw μ W) (hP : IsProbe μ R h) {B : Set S} (hB : MeasurableSet B) :
    ∀ᵐ ν ∂W, ∀ L i : ℕ, ∃ n : ℕ, ν (probeRegion R (gridTime h L (min i L)) ∩ B) = (n : ℝ≥0∞) := by
  have := hW.ae_forall_natCast_count (ι := ℕ × ℕ)
    (A := fun p => probeRegion R (gridTime h p.1 (min p.2 p.1)) ∩ B)
    (fun p => (measurableSet_probeRegion hP.measurable _).inter hB)
    (fun p => lt_of_le_of_lt (measure_mono (Set.inter_subset_left.trans (probeRegion_mono (by
      by_cases hp : p.1 = 0
      · have : min p.2 p.1 = 0 := by simp [hp]
        rw [this, gridTime_zero]; simp
      · exact_mod_cast gridTime_le (Nat.pos_of_ne_zero hp) (min_le_right _ _))))) hP.mass_lt_top)
  filter_upwards [this] with ν hν L i using hν (L, i)

omit [SigmaFinite μ] in
theorem ae_forall_gridNat (hW : IsPPPLaw μ W) (hP : IsProbe μ R h) {l : ℕ} {B : Fin l → Set S}
    (hB : ∀ j, MeasurableSet (B j)) :
    ∀ᵐ ν ∂W, ∀ j, ∀ L i : ℕ, ∃ n : ℕ, ν (probeRegion R (gridTime h L (min i L)) ∩ B j) = (n : ℝ≥0∞) :=
  ae_all_iff.2 fun j => ae_gridNat hW hP (hB j)

/-- The unexplored part after one step, Step 2, for a count event. -/
theorem lintegral_step_renew_count (hW : IsPPPLaw μ W) (hP : IsProbe μ R h) (hh : 0 < h)
    {g : Outcome S → ℝ≥0∞} (hgm : Measurable g) (hg1 : ∀ o, g o ≤ 1) {l : ℕ} {B : Fin l → Set S}
    (hB : ∀ j, MeasurableSet (B j)) {C0 : Set (Fin l → ℝ≥0∞)} (hC0 : MeasurableSet C0) :
    ∫⁻ p, g (probeStep μ R h p.1) *
        {κ : Measure S | (fun j => κ (B j)) ∈ C0}.indicator 1 (probeRenew μ R h p.1 p.2)
        ∂(W.prod W) =
      (∫⁻ ν, g (probeStep μ R h ν) ∂W) * W {κ : Measure S | (fun j => κ (B j)) ∈ C0} := by
  have := hW.isProbabilityMeasure
  have hR := hP.measurable
  set F : Set (Measure S) := {κ : Measure S | (fun j => κ (B j)) ∈ C0} with hFdef
  have hF : MeasurableSet F := countEvents_measurableSet ⟨l, B, C0, hB, hC0, rfl⟩
  have hgood : ∀ᵐ p ∂(W.prod W), (p.1 ∈ lfSet μ ∧ p.2 ∈ lfSet μ) ∧
      (∀ j, ∀ L i : ℕ, ∃ n : ℕ, p.1 (probeRegion R (gridTime h L (min i L)) ∩ B j) = (n : ℝ≥0∞)) ∧
      (∀ j, ∀ L i : ℕ, ∃ n : ℕ, p.2 (probeRegion R (gridTime h L (min i L)) ∩ B j) = (n : ℝ≥0∞)) := by
    have h1 := (measurePreserving_fst (μ := W) (ν := W)).quasiMeasurePreserving.ae
      (hW.ae_mem_lfSet.and (ae_forall_gridNat hW hP hB))
    have h2 := (measurePreserving_snd (μ := W) (ν := W)).quasiMeasurePreserving.ae
      (hW.ae_mem_lfSet.and (ae_forall_gridNat hW hP hB))
    filter_upwards [h1, h2] with p hp1 hp2
    exact ⟨⟨hp1.1, hp2.1⟩, hp1.2, hp2.2⟩
  let fn : ℕ → Measure S × Measure S → ℝ≥0∞ := fun n p => g (probeStep μ R h p.1) *
    F.indicator 1 (renewAt (probeRegion R (gridCeil h (2 ^ n) (probeRho μ R h p.1))) p)
  have hstep1 : ∀ n, ∫⁻ p, fn n p ∂(W.prod W) =
      (∫⁻ ν, g (probeStep μ R h ν) ∂W) * W F := fun n =>
    lintegral_step_renewGrid hW hP hh (L := 2 ^ n) (by positivity) hgm hF
  have hlim : ∀ᵐ p ∂(W.prod W), Tendsto (fun n => fn n p) atTop
      (𝓝 (g (probeStep μ R h p.1) * F.indicator 1 (probeRenew μ R h p.1 p.2))) := by
    filter_upwards [hgood] with p ⟨⟨hp1, hp2⟩, hn1, hn2⟩
    have hN : ∀ j, ∃ N : ℕ, ∀ n ≥ N,
        renewAt (probeRegion R (gridCeil h (2 ^ n) (probeRho μ R h p.1))) p (B j) =
          probeRenew μ R h p.1 p.2 (B j) := fun j =>
      eventually_renew_eq (hB j) hR hp1 hp2 (hn1 j) (hn2 j)
    choose N hN using hN
    refine tendsto_const_nhds.congr' (eventually_atTop.2 ⟨Finset.univ.sup N, fun n hn => ?_⟩)
    have : ∀ j, renewAt (probeRegion R (gridCeil h (2 ^ n) (probeRho μ R h p.1))) p (B j) =
        probeRenew μ R h p.1 p.2 (B j) := fun j =>
      hN j n (le_trans (Finset.le_sup (Finset.mem_univ j)) hn)
    have hmem : renewAt (probeRegion R (gridCeil h (2 ^ n) (probeRho μ R h p.1))) p ∈ F ↔
        probeRenew μ R h p.1 p.2 ∈ F := by
      show (fun j => _) ∈ C0 ↔ (fun j => _) ∈ C0
      simp only [this]
    simp only [fn]
    congr 1
    by_cases hm : probeRenew μ R h p.1 p.2 ∈ F
    · simp [Set.indicator, hm, hmem.2 hm]
    · have hm' : renewAt (probeRegion R (gridCeil h (2 ^ n) (probeRho μ R h p.1))) p ∉ F :=
        fun h' => hm (hmem.1 h')
      simp [Set.indicator, hm, hm']
  have hdom := tendsto_lintegral_of_dominated_convergence' (μ := W.prod W) (fun _ => (1 : ℝ≥0∞))
    (fun n => (aemeasurable_integrand hW hP hh (L := 2 ^ n) (by positivity) hgm hF :
      AEMeasurable (fn n) (W.prod W)))
    (fun n => Eventually.of_forall fun p => by
      have h1 : F.indicator (1 : Measure S → ℝ≥0∞)
          (renewAt (probeRegion R (gridCeil h (2 ^ n) (probeRho μ R h p.1))) p) ≤ 1 := by
        by_cases hm : renewAt (probeRegion R (gridCeil h (2 ^ n) (probeRho μ R h p.1))) p ∈ F
        · simp [Set.indicator, hm]
        · simp [Set.indicator, hm]
      exact mul_le_one' (hg1 _) h1)
    (by simp) hlim
  have hconst : Tendsto (fun n => ∫⁻ p, fn n p ∂(W.prod W)) atTop
      (𝓝 ((∫⁻ ν, g (probeStep μ R h ν) ∂W) * W F)) := by
    simp_rw [hstep1]; exact tendsto_const_nhds
  exact tendsto_nhds_unique hdom hconst

end ElboimSly
