/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.PPP.Exploration.ThmRun
import Mathlib

/-!
# Sequential first-point exploration: resampling

Sequential first-point exploration (c), `k ∈ ℕ`. With `Ñ_k = N|_{S∖Z_k} + N'|_{Z_k}`,
`Law(H_k, Ñ_k) = Law(H_k) ⊗ W`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace ElboimSly

variable {S : Type*} [MeasurableSpace S] {U : Type*} [MeasurableSpace U] {μ : Measure S}
  [SigmaFinite μ] {sch : ExplScheme μ U} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {W : Measure (Measure S)}

theorem map_tau_prod (hW : IsPPPLaw μ W) :
    (W.prod W).map (Prod.map (tau μ) (tau μ)) = W.prod W := by
  have := hW.isProbabilityMeasure
  have h1 : W.map (tau μ) = W := by
    conv_rhs => rw [← Measure.map_id (μ := W)]
    exact Measure.map_congr (by
      filter_upwards [hW.ae_mem_lfSet] with ν hν using tau_of_mem μ hν)
  rw [← Measure.map_prod_map _ _ (measurable_tau μ) (measurable_tau μ), h1]

theorem lintegral_renewAt_tau (hW : IsPPPLaw μ W) {D : Set S} (hD : MeasurableSet D)
    {F : Measure S → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ ν, ∫⁻ y, F (renewAt D (tau μ ν, tau μ y)) ∂W ∂W = ∫⁻ m, F m ∂W := by
  have := hW.isProbabilityMeasure
  have hm : Measurable fun p : Measure S × Measure S => F (renewAt D (tau μ p.1, tau μ p.2)) :=
    hF.comp ((measurable_renewAt hD).comp
      (((measurable_tau μ).comp measurable_fst).prodMk ((measurable_tau μ).comp measurable_snd)))
  rw [← lintegral_prod _ hm.aemeasurable]
  have hg : Measurable fun p : Measure S × Measure S => F (renewAt D p) :=
    hF.comp (measurable_renewAt hD)
  have h1 := lintegral_map hg ((measurable_tau μ).prodMap (measurable_tau μ))
    (μ := W.prod W)
  rw [map_tau_prod hW] at h1
  have h2 := lintegral_map hF (measurable_renewAt hD) (μ := W.prod W)
  rw [map_renewAt hW hD] at h2
  exact (show _ = _ from h1.symm).trans h2.symm

namespace ExplRun

variable (run : ExplRun sch P)

include run

/-- Sequential first-point exploration (c), `k ∈ ℕ`: resampling. -/
theorem resample {k : ℕ} {F : Hist U S k × Measure S → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ ω, F (run.H k ω, (run.N ω).restrict (sch.Z k (run.H k ω))ᶜ +
        (run.N' ω).restrict (sch.Z k (run.H k ω))) ∂P =
      ∫⁻ ω, ∫⁻ ν, F (run.H k ω, ν) ∂(P.map run.N) ∂P := by
  have := run.prob
  have hW := run.isPPPLaw
  have hWN' : P.map run.N' = P.map run.N := run.isPPP.map_eq_map run.isPPP'
  let A : Ω → Hist U S k × Measure S := fun ω =>
    (run.H k ω, sch.unexpl k (run.H k ω) (run.N ω))
  have hAm : Measurable A := (run.measurable_H k).prodMk ((sch.measurable_unexpl k).comp
    ((run.measurable_H k).prodMk run.isPPP.measurable))
  let F' : (Hist U S k × Measure S) × Measure S → ℝ≥0∞ := fun q =>
    F (q.1.1, q.1.2 + (tau μ q.2).restrict (sch.Z k q.1.1))
  have hF' : Measurable F' := by
    refine hF.comp (measurable_fst.comp measurable_fst |>.prodMk
      (measurable_add_measure.comp ((measurable_snd.comp measurable_fst).prodMk ?_)))
    exact (sch.measurable_restrict_Z k).comp
      ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
  have hind : IndepFun A run.N' P := by
    have := (run.indep'.symm).comp (φ := fun x : U × Measure S =>
      (sch.Hfun k x, sch.unexpl k (sch.Hfun k x) x.2)) (ψ := id)
      (((sch.measurable_Hfun k).prodMk ((sch.measurable_unexpl k).comp
        ((sch.measurable_Hfun k).prodMk measurable_snd)))) measurable_id
    exact this
  have h1 := lintegral_freeze hAm run.isPPP'.measurable hind hF'
  have e1 : ∀ ω, F (run.H k ω, (run.N ω).restrict (sch.Z k (run.H k ω))ᶜ +
      (run.N' ω).restrict (sch.Z k (run.H k ω))) = F' (A ω, run.N' ω) := by
    intro ω
    simp only [F', A]
    rw [run.unexpl_N, tau_of_mem μ (run.lf' ω)]
  simp_rw [e1]
  rw [h1, hWN']
  set Θ : Hist U S k × Measure S → ℝ≥0∞ := fun x =>
    ∫⁻ y, F' (x, y) ∂(P.map run.N) with hΘ
  have hΘm : Measurable Θ := Measurable.lintegral_prod_right' hF'
  rw [lintegral_map hΘm hAm]
  have h2 := run.fresh hΘm
  have e2 : ∀ ω, Θ (A ω) = Θ (run.H k ω, (run.N ω).restrict (sch.Z k (run.H k ω))ᶜ) := by
    intro ω; simp only [A, run.unexpl_N]
  simp_rw [e2]
  rw [h2]
  refine lintegral_congr fun ω => ?_
  simp only [Θ, F', ExplScheme.unexpl]
  exact lintegral_renewAt_tau hW (sch.measurableSet_Zη k (run.H k ω))
    (hF.comp (measurable_const.prodMk measurable_id))

end ExplRun

end ElboimSly
