/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.SRW.Coords
public import ElboimSly.Foundations.SRW.FixedBound
public import Mathlib

/-!
# Transfer to the canonical walk; coordinates of an SRW

Coordinates (for an arbitrary SRW), and the reduction "the statement depends only
on the law" used throughout fixed-time estimates.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ElboimSly
namespace SRW

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {Z : Ω → PathSpace d}

/-- An SRW has, on every measurable set of paths, the probability of the canonical walk of some
Poisson point process. -/
theorem IsSRW.exists_canonical (hZ : IsSRW P Z) :
    ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (P' : Measure Ω') (N' : Ω' → Measure (Dir d × ℝ)),
      IsPoissonPointProcess N' (clockIntensity (Dir d)) P' ∧
        ∀ E : Set (PathSpace d), MeasurableSet E → P (Z ⁻¹' E) = P' (canonical d N' ⁻¹' E) := by
  obtain ⟨hm, _, Ω', _, P', N', hN', hlaw⟩ := hZ
  refine ⟨Ω', inferInstance, P', N', hN', fun E hE => ?_⟩
  rw [← Measure.map_apply hm hE, hlaw, Measure.map_apply (measurable_canonical hN'.measurable) hE]

/-- Each coordinate of an SRW is a one-dimensional SRW (Coordinates). -/
theorem IsSRW.coord (hZ : IsSRW P Z) (i : Fin d) :
    IsSRW P (fun ω s => fun _ : Fin 1 => Z ω s i) := by
  obtain ⟨hm, hreg, Ω', _, P', N', hN', hlaw⟩ := hZ
  have hπ : Measurable fun γ : PathSpace d => fun (s : ℝ≥0) (_ : Fin 1) => γ s i :=
    measurable_pi_iff.2 fun s => measurable_pi_iff.2 fun _ =>
      (measurable_pi_apply i).comp (measurable_pi_apply s)
  refine ⟨hπ.comp hm, fun ω t => ?_, Ω', inferInstance, P', fun ω => axisProcess i (N' ω),
    axisProcess_ppp hN' i, ?_⟩
  · obtain ⟨δ, hδ, h⟩ := hreg ω t
    exact ⟨δ, hδ, fun s hs1 hs2 => by
      funext j
      exact congrFun (h s hs1 hs2) i⟩
  · have e1 : P.map (fun ω s => fun _ : Fin 1 => Z ω s i) =
        (P.map Z).map (fun γ : PathSpace d => fun (s : ℝ≥0) (_ : Fin 1) => γ s i) :=
      (Measure.map_map hπ hm).symm
    rw [e1, hlaw, Measure.map_map hπ (measurable_canonical hN'.measurable)]
    refine Measure.map_congr ?_
    filter_upwards [walk_axisProcess_ae hN' i] with ω hω
    funext s
    exact hω s

/-- Integrals of measurable functionals of an SRW agree with those of a canonical walk. -/
theorem IsSRW.exists_canonical_integral (hZ : IsSRW P Z) :
    ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (P' : Measure Ω') (N' : Ω' → Measure (Dir d × ℝ)),
      IsPoissonPointProcess N' (clockIntensity (Dir d)) P' ∧
        ∀ f : PathSpace d → ℝ, Measurable f →
          ∫ ω, f (Z ω) ∂P = ∫ ω, f (canonical d N' ω) ∂P' := by
  obtain ⟨hm, _, Ω', _, P', N', hN', hlaw⟩ := hZ
  refine ⟨Ω', inferInstance, P', N', hN', fun f hf => ?_⟩
  rw [← integral_map hm.aemeasurable hf.aestronglyMeasurable, hlaw,
    integral_map (measurable_canonical hN'.measurable).aemeasurable hf.aestronglyMeasurable]


end SRW
end ElboimSly
