/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.PPP.Exploration.ThmInfLaw
import Mathlib

/-!
# Sequential first-point exploration: the resampled configurations

Sequential first-point exploration (c). `Ñ_k = N|_{S∖Z_k} + N'|_{Z_k}`, for `k ∈ ℕ ∪ {∞}`.
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

/-- `Ñ_k = N|_{S∖Z_k} + N'|_{Z_k}`. -/
noncomputable def Ntil (k : ℕ) (ω : Ω) : Measure S :=
  (run.N ω).restrict (sch.Z k (run.H k ω))ᶜ + (run.N' ω).restrict (sch.Z k (run.H k ω))

/-- `Ñ_∞ = N|_{S∖Z_∞} + N'|_{Z_∞}`. -/
noncomputable def NtilInf (ω : Ω) : Measure S :=
  (run.N ω).restrict (sch.Zinf (run.Hinf ω))ᶜ + (run.N' ω).restrict (sch.Zinf (run.Hinf ω))

theorem measurable_Ntil (k : ℕ) : Measurable (run.Ntil k) := by
  have : run.Ntil k = fun ω => (tau μ (run.N ω)).restrict (sch.Z k (run.H k ω))ᶜ +
      (tau μ (run.N' ω)).restrict (sch.Z k (run.H k ω)) := by
    funext ω; simp only [Ntil, tau_of_mem μ (run.lf ω), tau_of_mem μ (run.lf' ω)]
  rw [this]
  exact measurable_add_measure.comp
    (((sch.measurable_restrict_Zc k).comp ((run.measurable_H k).prodMk run.isPPP.measurable)).prodMk
      ((sch.measurable_restrict_Z k).comp ((run.measurable_H k).prodMk run.isPPP'.measurable)))

theorem measurable_NtilInf : Measurable run.NtilInf := by
  have : run.NtilInf = fun ω => (tau μ (run.N ω)).restrict (sch.Zinf (run.Hinf ω))ᶜ +
      (tau μ (run.N' ω)).restrict (sch.Zinf (run.Hinf ω)) := by
    funext ω; simp only [NtilInf, tau_of_mem μ (run.lf ω), tau_of_mem μ (run.lf' ω)]
  rw [this]
  have h1 := measurable_tau_restrict_section μ sch.measurableSet_Zinf.compl
  have h2 := measurable_tau_restrict_section μ sch.measurableSet_Zinf
  exact measurable_add_measure.comp
    ((h1.comp (run.measurable_Hinf.prodMk run.isPPP.measurable)).prodMk
      (h2.comp (run.measurable_Hinf.prodMk run.isPPP'.measurable)))

theorem law_Ntil (k : ℕ) : P.map (run.Ntil k) = P.map run.N := by
  have := run.prob
  refine Measure.ext fun G hG => ?_
  rw [Measure.map_apply (run.measurable_Ntil k) hG, Measure.map_apply run.isPPP.measurable hG,
    ← lintegral_indicator_one ((run.measurable_Ntil k) hG)]
  have h := run.resample (k := k) (F := fun q => G.indicator (1 : Measure S → ℝ≥0∞) q.2)
    ((measurable_one.indicator hG).comp measurable_snd)
  have e : ∀ ω, (run.Ntil k ⁻¹' G).indicator (1 : Ω → ℝ≥0∞) ω =
      G.indicator (1 : Measure S → ℝ≥0∞) (run.Ntil k ω) := by
    intro ω
    classical
    simp only [Set.indicator]
    exact if_congr Iff.rfl rfl rfl
  simp_rw [e]
  refine h.trans ?_
  simp only [lintegral_const, lintegral_indicator_one hG, measure_univ, mul_one]
  rw [Measure.map_apply run.isPPP.measurable hG]

theorem isPPP_Ntil (k : ℕ) : IsPoissonPointProcess (run.Ntil k) μ P :=
  run.isPPP.of_map_eq (run.measurable_Ntil k) (run.law_Ntil k)

theorem ae_eventually_Ntil_apply {B : Set S} (hB : MeasurableSet B) (hfin : μ B < ∞) :
    ∀ᵐ ω ∂P, ∀ᶠ k in atTop, run.Ntil k ω B = run.NtilInf ω B := by
  have hN := run.isPPP.ae_natCast_count hB hfin
  have hN' := run.isPPP'.ae_natCast_count hB hfin
  have hall := ae_all_iff.2 fun k => (run.isPPP_Ntil k).ae_natCast_count hB hfin
  filter_upwards [hN, hN', hall] with ω ⟨n, hn⟩ ⟨n', hn'⟩ hk
  have hNB : run.N ω B ≠ ∞ := by rw [hn]; exact ENNReal.natCast_ne_top n
  have hN'B : run.N' ω B ≠ ∞ := by rw [hn']; exact ENNReal.natCast_ne_top n'
  set Zs : ℕ → Set S := fun k => sch.Z k (run.H k ω) with hZs
  have hZm : ∀ k, MeasurableSet (Zs k) := fun k => sch.measurableSet_Zη k _
  have hmono : Monotone Zs := fun j k hjk => sch.Z_antitone_le hjk (run.X ω)
  have hU : sch.Zinf (run.Hinf ω) = ⋃ k, Zs k := sch.Zinf_Hinf (run.X ω)
  have eN : ∀ k, run.Ntil k ω B = run.N ω (B ∩ (Zs k)ᶜ) + run.N' ω (B ∩ Zs k) := by
    intro k
    simp only [Ntil, Measure.add_apply, Measure.restrict_apply hB]
    rfl
  have eInf : run.NtilInf ω B = run.N ω (B ∩ (⋃ k, Zs k)ᶜ) + run.N' ω (B ∩ ⋃ k, Zs k) := by
    simp only [NtilInf, Measure.add_apply, Measure.restrict_apply hB, hU]
  have t1 : Tendsto (fun k => run.N ω (B ∩ (Zs k)ᶜ)) atTop
      (𝓝 (run.N ω (B ∩ (⋃ k, Zs k)ᶜ))) := by
    have := tendsto_measure_iInter_atTop (μ := run.N ω) (s := fun k => B ∩ (Zs k)ᶜ)
      (fun k => (hB.inter (hZm k).compl).nullMeasurableSet)
      (fun j k hjk => Set.inter_subset_inter_right _ (Set.compl_subset_compl.2 (hmono hjk)))
      ⟨0, ne_top_of_le_ne_top hNB (measure_mono Set.inter_subset_left)⟩
    rw [← Set.inter_iInter, ← Set.compl_iUnion] at this
    exact this
  have t2 : Tendsto (fun k => run.N' ω (B ∩ Zs k)) atTop
      (𝓝 (run.N' ω (B ∩ ⋃ k, Zs k))) := by
    have := tendsto_measure_iUnion_atTop (μ := run.N' ω) (s := fun k => B ∩ Zs k)
      (fun j k hjk => Set.inter_subset_inter_right _ (hmono hjk))
    rw [← Set.inter_iUnion] at this
    exact this
  have hlim : Tendsto (fun k => run.Ntil k ω B) atTop (𝓝 (run.NtilInf ω B)) := by
    rw [eInf]
    exact (t1.add t2).congr fun k => (eN k).symm
  have hfinL : run.NtilInf ω B ≠ ∞ := by
    rw [eInf]
    refine ENNReal.add_ne_top.2 ⟨?_, ?_⟩
    · exact ne_top_of_le_ne_top hNB (measure_mono Set.inter_subset_left)
    · exact ne_top_of_le_ne_top hN'B (measure_mono Set.inter_subset_left)
  exact eventually_eq_of_nat_tendsto _ hk hfinL hlim

end ExplRun

end ElboimSly
