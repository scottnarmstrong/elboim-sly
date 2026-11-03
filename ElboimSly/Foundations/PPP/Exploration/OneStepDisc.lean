/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.PPP.Exploration.FirstPointLaw
public import ElboimSly.Foundations.PPP.Restriction
public import ElboimSly.Foundations.PPP.Superposition
import Mathlib

/-!
# One step: a deterministic stopping region

The unexplored part after one step, Step 1.

For a fixed measurable `D ⊆ S`, on `(Measure S)², W ⊗ W`, the configuration
`ν|_{Dᶜ} + ν''|_D` is a PPP of law `W`, and for `ψ` measurable,
`E[ψ(ν|_D) 1_F(ν|_{Dᶜ} + ν''|_D)] = E[ψ(ν|_D)] W(F)`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace ElboimSly

variable {S : Type*} [MeasurableSpace S] {μ : Measure S} [SigmaFinite μ] {W : Measure (Measure S)}

/-- The renewal of `ν` by `ν''` on the region `D`. -/
noncomputable def renewAt (D : Set S) (p : Measure S × Measure S) : Measure S :=
  p.1.restrict Dᶜ + p.2.restrict D

theorem measurable_renewAt {D : Set S} (hD : MeasurableSet D) : Measurable (renewAt D) :=
  measurable_add_measure.comp
    (((measurable_restrict_measure hD.compl).comp measurable_fst).prodMk
      ((measurable_restrict_measure hD).comp measurable_snd))

section Prod

variable (hW : IsPPPLaw μ W)

include hW in
omit [SigmaFinite μ] in
theorem isPPPLaw_fst : IsPoissonPointProcess (fun p : Measure S × Measure S => p.1) μ (W.prod W) := by
  have := hW.isProbabilityMeasure
  refine hW.of_map_eq (N' := fun p : Measure S × Measure S => p.1) (P' := W.prod W)
    measurable_fst ?_
  simp

include hW in
omit [SigmaFinite μ] in
theorem isPPPLaw_snd : IsPoissonPointProcess (fun p : Measure S × Measure S => p.2) μ (W.prod W) := by
  have := hW.isProbabilityMeasure
  refine hW.of_map_eq (N' := fun p : Measure S × Measure S => p.2) (P' := W.prod W)
    measurable_snd ?_
  simp

include hW in
omit [SigmaFinite μ] in
theorem indepFun_fst_snd_prod :
    IndepFun (fun p : Measure S × Measure S => p.1) (fun p : Measure S × Measure S => p.2)
      (W.prod W) := by
  have := hW.isProbabilityMeasure
  exact indepFun_prod (X := fun ν : Measure S => ν) (Y := fun ν : Measure S => ν)
    measurable_id measurable_id

include hW in
omit [SigmaFinite μ] in
theorem isPPPLaw_renewAt {D : Set S} (hD : MeasurableSet D) :
    IsPoissonPointProcess (renewAt D) μ (W.prod W) := by
  have h1 := isPPPLaw_fst hW
  have h2 := isPPPLaw_snd hW
  have := IsPoissonPointProcess.restrict_add_restrict_compl h1 h2 (indepFun_fst_snd_prod hW)
    hD.compl
  rw [compl_compl] at this
  exact this

include hW in
omit [SigmaFinite μ] in
theorem map_renewAt {D : Set S} (hD : MeasurableSet D) : (W.prod W).map (renewAt D) = W := by
  have := hW.isProbabilityMeasure
  have := hW.map_eq_map (isPPPLaw_renewAt hW hD)
  simpa using this

include hW in
omit [SigmaFinite μ] in
/-- The unexplored part after one step, Step 1 for a fixed region `D`. -/
theorem lintegral_restrict_renewAt {D : Set S} (hD : MeasurableSet D) {ψ : Measure S → ℝ≥0∞}
    (hψ : Measurable ψ) {F : Set (Measure S)} (hF : MeasurableSet F) :
    ∫⁻ p, ψ (p.1.restrict D) * F.indicator 1 (renewAt D p) ∂(W.prod W) =
      (∫⁻ ν, ψ (ν.restrict D) ∂W) * W F := by
  have := hW.isProbabilityMeasure
  let G : Measure S → ℝ≥0∞ := fun κ => ∫⁻ ν'', F.indicator 1 (κ + ν''.restrict D) ∂W
  have hFm : Measurable fun q : Measure S × Measure S => F.indicator (1 : Measure S → ℝ≥0∞)
      (q.1 + q.2.restrict D) :=
    (measurable_one.indicator hF).comp
      (measurable_add_measure.comp
        (measurable_fst.prodMk ((measurable_restrict_measure hD).comp measurable_snd)))
  have hG : Measurable G := hFm.lintegral_prod_right'
  have hrD : Measurable fun ν : Measure S => ν.restrict D := measurable_restrict_measure hD
  have hrDc : Measurable fun ν : Measure S => ν.restrict Dᶜ := measurable_restrict_measure hD.compl
  have hfm : Measurable fun p : Measure S × Measure S =>
      ψ (p.1.restrict D) * F.indicator 1 (renewAt D p) :=
    (hψ.comp (hrD.comp measurable_fst)).mul
      ((measurable_one.indicator hF).comp (measurable_renewAt hD))
  rw [lintegral_prod _ hfm.aemeasurable]
  have e1 : ∀ ν : Measure S, ∫⁻ ν'', ψ (ν.restrict D) * F.indicator 1 (renewAt D (ν, ν'')) ∂W =
      ψ (ν.restrict D) * G (ν.restrict Dᶜ) := by
    intro ν
    have hm : Measurable fun ν'' : Measure S => F.indicator (1 : Measure S → ℝ≥0∞)
        (renewAt D (ν, ν'')) :=
      (measurable_one.indicator hF).comp
        ((measurable_renewAt hD).comp (measurable_const.prodMk measurable_id))
    rw [lintegral_const_mul _ hm]
    rfl
  simp_rw [e1]
  have hind := (hW.indepFun_restrict hD hD.compl disjoint_compl_right).comp hψ hG
  rw [show (fun ν : Measure S => ψ (ν.restrict D) * G (ν.restrict Dᶜ)) =
      (ψ ∘ fun ν : Measure S => ν.restrict D) * (G ∘ fun ν : Measure S => ν.restrict Dᶜ) from rfl,
    lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun (hψ.comp hrD) (hG.comp hrDc) hind]
  congr 1
  have hFm' : Measurable fun p : Measure S × Measure S => F.indicator (1 : Measure S → ℝ≥0∞)
      (renewAt D p) := (measurable_one.indicator hF).comp (measurable_renewAt hD)
  have := lintegral_prod _ hFm'.aemeasurable (μ := W) (ν := W)
  have e2 : ∫⁻ p, F.indicator (1 : Measure S → ℝ≥0∞) (renewAt D p) ∂(W.prod W) = W F := by
    rw [← lintegral_map (measurable_one.indicator hF) (measurable_renewAt hD), map_renewAt hW hD,
      lintegral_indicator_one hF]
  rw [← e2, this]
  rfl

end Prod

end ElboimSly
