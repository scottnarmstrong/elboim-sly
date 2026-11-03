/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.PPP.Exploration.ThmInfLaw2
import Mathlib

/-!
# Sequential first-point exploration: resampling at infinity

Sequential first-point exploration (c), `k = ∞` (Step 5): `Ñ_∞` is a `PPP(μ)` independent of `𝒢_∞`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace ElboimSly

variable {S : Type*} [MeasurableSpace S] {U : Type*} [MeasurableSpace U] {μ : Measure S}
  [SigmaFinite μ] {sch : ExplScheme μ U} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  (run : ExplRun sch P)

namespace ExplRun

include run

theorem ae_eventually_mem {l : ℕ} {B : Fin l → Set S} (hB : ∀ i, MeasurableSet (B i))
    (hfin : ∀ i, μ (B i) < ∞) {C0 : Set (Fin l → ℝ≥0∞)} :
    ∀ᵐ ω ∂P, ∀ᶠ k in atTop, (run.Ntil k ω ∈ {ν : Measure S | (fun i => ν (B i)) ∈ C0} ↔
      run.NtilInf ω ∈ {ν : Measure S | (fun i => ν (B i)) ∈ C0}) := by
  have := ae_all_iff.2 fun i => run.ae_eventually_Ntil_apply (hB i) (hfin i)
  filter_upwards [this] with ω hω
  have h2 : ∀ᶠ k in atTop, ∀ i, run.Ntil k ω (B i) = run.NtilInf ω (B i) :=
    Filter.eventually_all.2 hω
  filter_upwards [h2] with k hk
  have : (fun i => run.Ntil k ω (B i)) = fun i => run.NtilInf ω (B i) := funext hk
  show (fun i => run.Ntil k ω (B i)) ∈ C0 ↔ (fun i => run.NtilInf ω (B i)) ∈ C0
  rw [this]

theorem lintegral_inf_rect {k0 : ℕ} {A0 : Set (Hist U S k0)} (hA0 : MeasurableSet A0)
    {F : Set (Measure S)} (hF : F ∈ countEventsFin μ) :
    ∫⁻ ω, (truncHist k0 ⁻¹' A0).indicator 1 (run.Hinf ω) * F.indicator 1 (run.NtilInf ω) ∂P =
      (∫⁻ ω, (truncHist k0 ⁻¹' A0).indicator 1 (run.Hinf ω) ∂P) * (P.map run.N) F := by
  have := run.prob
  obtain ⟨l, B, C0, hB, hfin, hC0, rfl⟩ := hF
  set F := {ν : Measure S | (fun i => ν (B i)) ∈ C0} with hFdef
  have hFm : MeasurableSet F := countEvents_measurableSet ⟨l, B, C0, hB, hC0, rfl⟩
  set g : Ω → ℝ≥0∞ := fun ω => (truncHist k0 ⁻¹' A0).indicator 1 (run.Hinf ω) with hg
  have hgm : Measurable g := (measurable_one.indicator ((measurable_truncHist k0) hA0)).comp
    run.measurable_Hinf
  have hconst : ∀ k ≥ k0, ∫⁻ ω, g ω * F.indicator 1 (run.Ntil k ω) ∂P =
      (∫⁻ ω, g ω ∂P) * (P.map run.N) F := by
    intro k hk
    set A' : Set (Hist U S k) := shortenHist hk ⁻¹' A0 with hA'
    have hA'm : MeasurableSet A' := (measurable_shortenHist hk) hA0
    have e : ∀ ω, g ω = A'.indicator 1 (run.H k ω) := by
      intro ω
      have : truncHist k0 (run.Hinf ω) = shortenHist hk (run.H k ω) := by
        rw [truncHist_eq_shorten hk]
        congr 1
        exact sch.truncHist_Hinf k (run.X ω)
      classical
      simp only [hg, Set.indicator]
      refine if_congr ?_ rfl rfl
      show truncHist k0 (run.Hinf ω) ∈ A0 ↔ shortenHist hk (run.H k ω) ∈ A0
      rw [this]
    have h := run.resample (k := k)
      (F := fun q => A'.indicator (1 : Hist U S k → ℝ≥0∞) q.1 * F.indicator (1 : Measure S → ℝ≥0∞) q.2)
      (((measurable_one.indicator hA'm).comp measurable_fst).mul
        ((measurable_one.indicator hFm).comp measurable_snd))
    simp only [e]
    have hmA : Measurable fun ω => A'.indicator (1 : Hist U S k → ℝ≥0∞) (run.H k ω) :=
      (measurable_one.indicator hA'm).comp (run.measurable_H k)
    refine h.trans ?_
    have e2 : ∀ ω, ∫⁻ ν, A'.indicator (1 : Hist U S k → ℝ≥0∞) (run.H k ω) *
        F.indicator (1 : Measure S → ℝ≥0∞) ν ∂(P.map run.N) =
        A'.indicator (1 : Hist U S k → ℝ≥0∞) (run.H k ω) * (P.map run.N) F := by
      intro ω
      rw [lintegral_const_mul _ (measurable_one.indicator hFm), lintegral_indicator_one hFm]
    simp_rw [e2]
    exact lintegral_mul_const _ hmA
  have hind : ∀ k, Measurable fun ω => g ω * F.indicator (1 : Measure S → ℝ≥0∞) (run.Ntil k ω) :=
    fun k => hgm.mul ((measurable_one.indicator hFm).comp (run.measurable_Ntil k))
  have hlim : Tendsto (fun k => ∫⁻ ω, g ω * F.indicator (1 : Measure S → ℝ≥0∞) (run.Ntil k ω) ∂P)
      atTop (𝓝 (∫⁻ ω, g ω * F.indicator (1 : Measure S → ℝ≥0∞) (run.NtilInf ω) ∂P)) := by
    refine tendsto_lintegral_of_dominated_convergence (fun _ => (1 : ℝ≥0∞)) hind
      (fun k => Eventually.of_forall fun ω => ?_) (by simp) ?_
    · have h1 : g ω ≤ 1 := by
        by_cases hm : run.Hinf ω ∈ truncHist k0 ⁻¹' A0 <;> simp [hg, Set.indicator, hm]
      have h2 : F.indicator (1 : Measure S → ℝ≥0∞) (run.Ntil k ω) ≤ 1 := by
        by_cases hm : run.Ntil k ω ∈ F <;> simp [Set.indicator, hm]
      exact mul_le_one' h1 h2
    · filter_upwards [run.ae_eventually_mem hB hfin (C0 := C0)] with ω hω
      refine tendsto_const_nhds.congr' (hω.mono fun k hk => ?_)
      congr 1
      by_cases hm : run.NtilInf ω ∈ F
      · have hm' : run.Ntil k ω ∈ F := hk.2 hm
        simp [Set.indicator, hm, hm']
      · have hm' : run.Ntil k ω ∉ F := fun h' => hm (hk.1 h')
        simp [Set.indicator, hm, hm']
  have hconstlim : Tendsto (fun k => ∫⁻ ω, g ω * F.indicator (1 : Measure S → ℝ≥0∞)
      (run.Ntil k ω) ∂P) atTop (𝓝 ((∫⁻ ω, g ω ∂P) * (P.map run.N) F)) :=
    tendsto_const_nhds.congr' ((eventually_ge_atTop k0).mono fun k hk => (hconst k hk).symm)
  exact tendsto_nhds_unique hlim hconstlim

/-- Sequential first-point exploration (c), `k = ∞`: `Ñ_∞` is independent of `𝒢_∞` and has law `W`. -/
theorem resample_inf :
    P.map (fun ω => (run.Hinf ω, run.NtilInf ω)) = (P.map run.Hinf).prod (P.map run.N) := by
  have := run.prob
  have hmeas : Measurable fun ω => (run.Hinf ω, run.NtilInf ω) :=
    run.measurable_Hinf.prodMk run.measurable_NtilInf
  have hc1 : IsCountablySpanning (cylSets U S) :=
    ⟨fun _ => Set.univ, fun _ => ⟨0, Set.univ, MeasurableSet.univ, by simp⟩, Set.iUnion_const _⟩
  have hc2 : IsCountablySpanning (countEventsFin μ) :=
    ⟨fun _ => Set.univ, fun _ => univ_mem_countEventsFin, Set.iUnion_const _⟩
  have hgen : (inferInstance : MeasurableSpace ((U × (ℕ → Outcome S)) × Measure S)) =
      MeasurableSpace.generateFrom (Set.image2 (· ×ˢ ·) (cylSets U S) (countEventsFin μ)) := by
    rw [← generateFrom_prod_eq hc1 hc2, generateFrom_cylSets, generateFrom_countEventsFin]
  have key : ∀ s ∈ Set.image2 (· ×ˢ ·) (cylSets U S) (countEventsFin μ),
      (P.map fun ω => (run.Hinf ω, run.NtilInf ω)) s = ((P.map run.Hinf).prod (P.map run.N)) s := by
    rintro _ ⟨C, ⟨k0, A0, hA0, rfl⟩, F, hF, rfl⟩
    have hFm : MeasurableSet F := countEvents_measurableSet (countEventsFin_subset hF)
    have hCm : MeasurableSet (truncHist k0 ⁻¹' A0) := (measurable_truncHist k0) hA0
    rw [Measure.map_apply hmeas (hCm.prod hFm), Measure.prod_prod,
      Measure.map_apply run.measurable_Hinf hCm, ← lintegral_indicator_one (hmeas (hCm.prod hFm)),
      ← lintegral_indicator_one (run.measurable_Hinf hCm)]
    have e3 : ∫⁻ a, (run.Hinf ⁻¹' truncHist k0 ⁻¹' A0).indicator (1 : Ω → ℝ≥0∞) a ∂P =
        ∫⁻ ω, (truncHist k0 ⁻¹' A0).indicator (1 : U × (ℕ → Outcome S) → ℝ≥0∞) (run.Hinf ω) ∂P :=
      lintegral_congr fun a => by
        classical
        simp only [Set.indicator]
        exact if_congr Iff.rfl rfl rfl
    rw [e3, ← run.lintegral_inf_rect hA0 hF]
    refine lintegral_congr fun ω => ?_
    classical
    by_cases h1 : run.Hinf ω ∈ truncHist k0 ⁻¹' A0 <;>
      by_cases h2 : run.NtilInf ω ∈ F <;> simp [Set.indicator, h1, h2]
  exact ext_of_generate_finite _ hgen (IsPiSystem.prod isPiSystem_cylSets isPiSystem_countEventsFin)
    key (key _ ⟨Set.univ, ⟨0, Set.univ, MeasurableSet.univ, by simp⟩, Set.univ,
      univ_mem_countEventsFin, by simp⟩)

end ExplRun

end ElboimSly
