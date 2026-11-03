/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.PPP.Exploration.Probe
import Mathlib

/-!
# Measurability for parametrized probes

Measurability for parametrized probes.

A parametrized probe on `Θ` is a jointly measurable `R : Θ → S → ℝ≥0∞` and a measurable
`h : Θ → ℝ≥0`. Measurability of the step, renewal and kernel does not use (Pr1)-(Pr2).
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal NNReal

namespace ElboimSly

variable {S Θ : Type*} [MeasurableSpace S] [MeasurableSpace Θ] (μ : Measure S)

section PartA

variable {R : Θ → S → ℝ≥0∞} (hR : Measurable fun p : Θ × S => R p.1 p.2)

/-- Measurability for parametrized probes (a), the set `{(θ, r, x) : R θ x ≤ r}` (associated as
`(Θ × [0,∞]) × S`). -/
theorem measurableSet_probeRegion_param (hR : Measurable fun p : Θ × S => R p.1 p.2) :
    MeasurableSet {q : (Θ × ℝ≥0∞) × S | R q.1.1 q.2 ≤ q.1.2} :=
  measurableSet_le (hR.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd))
    (measurable_snd.comp measurable_fst)

/-- Measurability for parametrized probes (a), measurability of `(θ, r) ↦ m_θ(r)`. -/
theorem measurable_probeMass_param [SFinite μ] (hR : Measurable fun p : Θ × S => R p.1 p.2) :
    Measurable fun q : Θ × ℝ≥0∞ => probeMass μ (R q.1) q.2 :=
  measurable_measure_prodMk_left (measurableSet_probeRegion_param hR)

end PartA

variable [SigmaFinite μ] {R : Θ → S → ℝ≥0∞} {h : Θ → ℝ≥0}

theorem measurable_probeRho_param (hR : Measurable fun p : Θ × S => R p.1 p.2)
    (hh : Measurable h) :
    Measurable fun p : Θ × Measure S => probeRho μ (R p.1) (h p.1) p.2 := by
  classical
  unfold probeRho
  refine Measurable.min (measurable_coe_nnreal_ennreal.comp (hh.comp measurable_fst))
    (Measurable.iInf fun q => ?_)
  simp_rw [iInf_eq_if]
  refine Measurable.ite ?_ measurable_const measurable_const
  have hZ : MeasurableSet {p : Θ × S | R p.1 p.2 ≤ ratTime q} :=
    measurableSet_le hR measurable_const
  have h1 := measurable_tau_section μ hZ
  refine MeasurableSet.inter (MeasurableSet.const _) (MeasurableSet.inter ?_ ?_)
  · exact measurableSet_lt measurable_const
      (measurable_coe_nnreal_ennreal.comp (hh.comp measurable_fst))
  · exact measurableSet_le measurable_const h1

/-- Measurability for parametrized probes (b), the step map. -/
theorem measurable_probeStep_param (hR : Measurable fun p : Θ × S => R p.1 p.2)
    (hh : Measurable h) :
    Measurable fun p : Θ × Measure S => probeStep μ (R p.1) (h p.1) p.2 := by
  have hρ := measurable_probeRho_param μ hR hh
  refine hρ.prodMk ?_
  let Z : Set ((Θ × Measure S) × S) := {q | R q.1.1 q.2 ≤ probeRho μ (R q.1.1) (h q.1.1) q.1.2}
  have hZ : MeasurableSet Z :=
    measurableSet_le (hR.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd))
      (hρ.comp measurable_fst)
  have := (measurable_tau_restrict_section μ hZ).comp
    (measurable_id.prodMk (measurable_snd : Measurable fun p : Θ × Measure S => p.2))
  exact this

section Kernel

variable (R' : S → ℝ≥0∞) (h' : ℝ≥0)

omit [SigmaFinite μ] in
theorem monotone_probeMass : Monotone (probeMass μ R') :=
  fun _ _ hab => measure_mono fun _ hx => le_trans hx hab

omit [SigmaFinite μ] in
theorem measurable_expNeg_mass_comp (hR' : Measurable R') :
    Measurable fun x => expNeg (probeMass μ R' (R' x)) :=
  measurable_expNeg.comp ((monotone_probeMass μ R').measurable.comp hR')

omit [SigmaFinite μ] in
/-- Measurability for parametrized probes (c), the formula for the integral against `K`. -/
theorem lintegral_probeKernel (hR' : Measurable R') {g : Outcome S → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ o, g o ∂(probeKernel μ R' h') =
      expNeg (probeMass μ R' h') * g ((h' : ℝ≥0∞), 0) +
        ∫⁻ x in probeRegion R' h', expNeg (probeMass μ R' (R' x)) * g (R' x, Measure.dirac x) ∂μ := by
  unfold probeKernel
  have hΨ : Measurable fun a => (R' a, Measure.dirac a) :=
    hR'.prodMk Measure.measurable_dirac
  rw [lintegral_add_measure, lintegral_smul_measure, lintegral_dirac' _ hg,
    lintegral_map hg hΨ,
    lintegral_withDensity_eq_lintegral_mul _ (measurable_expNeg_mass_comp μ R' hR')
      (g := fun a => g (R' a, Measure.dirac a)) (hg.comp hΨ), smul_eq_mul]
  rfl

end Kernel

/-- Measurability for parametrized probes (c): the integral against `K_θ` is measurable in `θ`. -/
theorem measurable_lintegral_probeKernel (hR : Measurable fun p : Θ × S => R p.1 p.2)
    (hh : Measurable h) {g : Θ × Outcome S → ℝ≥0∞} (hg : Measurable g) :
    Measurable fun θ => ∫⁻ o, g (θ, o) ∂(probeKernel μ (R θ) (h θ)) := by
  have hRθ : ∀ θ, Measurable (R θ) := fun θ => hR.comp measurable_prodMk_left
  have hΨ : Measurable fun p : Θ × S => (p.1, (R p.1 p.2, Measure.dirac p.2)) :=
    measurable_fst.prodMk (hR.prodMk (Measure.measurable_dirac.comp measurable_snd))
  have hm := measurable_probeMass_param μ hR
  have hh' : Measurable fun θ => ((h θ : ℝ≥0) : ℝ≥0∞) := measurable_coe_nnreal_ennreal.comp hh
  have e : (fun θ => ∫⁻ o, g (θ, o) ∂(probeKernel μ (R θ) (h θ))) = fun θ =>
      expNeg (probeMass μ (R θ) (h θ)) * g (θ, ((h θ : ℝ≥0∞), 0)) +
        ∫⁻ x in probeRegion (R θ) (h θ),
          expNeg (probeMass μ (R θ) (R θ x)) * g (θ, (R θ x, Measure.dirac x)) ∂μ := by
    funext θ
    exact lintegral_probeKernel μ (R θ) (h θ) (hRθ θ)
      (hg.comp (measurable_const.prodMk measurable_id))
  rw [e]
  refine Measurable.add ?_ ?_
  · refine (measurable_expNeg.comp (hm.comp (measurable_id.prodMk hh'))).mul ?_
    exact hg.comp (measurable_id.prodMk (hh'.prodMk measurable_const))
  · have hset : MeasurableSet {p : Θ × S | R p.1 p.2 ≤ (h p.1 : ℝ≥0∞)} :=
      measurableSet_le hR (hh'.comp measurable_fst)
    have hF : Measurable fun p : Θ × S =>
        expNeg (probeMass μ (R p.1) (R p.1 p.2)) * g (p.1, (R p.1 p.2, Measure.dirac p.2)) :=
      (measurable_expNeg.comp (hm.comp (measurable_fst.prodMk hR))).mul (hg.comp hΨ)
    have := (hF.indicator hset).lintegral_prod_right' (ν := μ)
    convert this using 2 with θ
    have hs : MeasurableSet (probeRegion (R θ) (h θ)) := measurable_prodMk_left hset
    exact (lintegral_indicator hs _).symm

end ElboimSly
