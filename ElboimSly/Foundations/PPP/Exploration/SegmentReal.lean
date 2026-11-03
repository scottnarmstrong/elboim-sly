/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.PPP.Exploration.Segment
import Mathlib

/-!
# Segment probes on `E × ℝ`

Segment probes on E×mathbbT_β and E×mathbbR, case (ii): `X = ℝ`, `λ = Leb|_I`, segments
`x_e(s) = t_e + σ_e s` with `σ_e ∈ {+1, -1}`, left inverse `s_e(y) = σ_e (y - t_e)` and weight
`w_e(s) = 1_I(x_e(s))`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal NNReal

namespace ElboimSly

variable {E : Type*} [MeasurableSpace E]

/-- The affine map `s ↦ t + σ s` with `σ = ±1` preserves Lebesgue measure. -/
theorem measurePreserving_affine_pm (t σ : ℝ) (hσ : σ = 1 ∨ σ = -1) :
    MeasurePreserving (fun s : ℝ => t + σ * s) volume volume := by
  rcases hσ with rfl | rfl
  · simpa using measurePreserving_add_left volume t
  · have h1 : MeasurePreserving (fun s : ℝ => -s) volume volume := Measure.measurePreserving_neg _
    have h2 := (measurePreserving_add_left (volume : Measure ℝ) t).comp h1
    simpa [Function.comp_def, sub_eq_add_neg] using h2

omit [MeasurableSpace E] in
/-- The segment setup on `ℝ` with `λ = Leb|_I`. -/
theorem segSetup_real (A : Finset E) (t σ : E → ℝ) (hσ : ∀ e, σ e = 1 ∨ σ e = -1) (h : ℝ≥0)
    {I : Set ℝ} (hI : MeasurableSet I) :
    SegSetup (volume.restrict I) A (fun e s => t e + σ e * s) (fun e y => σ e * (y - t e)) h
      (fun e s => I.indicator (fun _ => (1 : ℝ≥0∞)) (t e + σ e * s)) := by
  have hσσ : ∀ e, σ e * σ e = 1 := fun e => by rcases hσ e with h | h <;> simp [h]
  have hleft : ∀ e s, σ e * ((t e + σ e * s) - t e) = s := fun e s => by
    have := hσσ e
    calc σ e * ((t e + σ e * s) - t e) = (σ e * σ e) * s := by ring
      _ = s := by rw [this, one_mul]
  have hright : ∀ e y, t e + σ e * (σ e * (y - t e)) = y := fun e y => by
    have := hσσ e
    calc t e + σ e * (σ e * (y - t e)) = t e + (σ e * σ e) * (y - t e) := by ring
      _ = y := by rw [this]; ring
  refine ⟨fun e => by fun_prop, fun e => by fun_prop, fun e => ?_, fun e s => ?_,
    fun e _ s _ => hleft e s, fun e => ?_, fun e _ ψ hψ => ?_⟩
  · exact (measurable_const.indicator hI).comp (by fun_prop)
  · exact Set.indicator_le_self' (fun _ _ => zero_le) _ |>.trans (by
      by_cases hm : (t e + σ e * s) ∈ I <;> simp)
  · simp only [hright]
    exact MeasurableSet.univ
  · -- change of variables
    have hmp := measurePreserving_affine_pm (t e) (σ e) (hσ e)
    let hφ : ℝ ≃ₜ ℝ :=
      { toFun := fun s => t e + σ e * s
        invFun := fun y => σ e * (y - t e)
        left_inv := fun s => hleft e s
        right_inv := fun y => hright e y
        continuous_toFun := by fun_prop
        continuous_invFun := by fun_prop }
    have hemb : MeasurableEmbedding (fun s : ℝ => t e + σ e * s) := hφ.measurableEmbedding
    have hseg : segImg (fun e s => t e + σ e * s) (fun e y => σ e * (y - t e)) h e =
        {y | σ e * (y - t e) ∈ Set.Ioc (0 : ℝ) h} := by
      ext y; simp [segImg, hright, Set.mem_Ioc]
    have hsegm : MeasurableSet
        (segImg (fun e s => t e + σ e * s) (fun e y => σ e * (y - t e)) h e) := by
      rw [hseg]; exact measurableSet_Ioc.preimage (by fun_prop)
    have hJ : MeasurableSet ((fun s : ℝ => t e + σ e * s) ⁻¹' I) := hI.preimage (by fun_prop)
    have hpre : (fun s : ℝ => t e + σ e * s) ⁻¹'
        (segImg (fun e s => t e + σ e * s) (fun e y => σ e * (y - t e)) h e ∩ I) =
        (fun s : ℝ => t e + σ e * s) ⁻¹' I ∩ Set.Ioc (0 : ℝ) h := by
      ext s
      simp only [Set.mem_preimage, Set.mem_inter_iff, hseg, Set.mem_ofPred_eq, hleft]
      tauto
    calc ∫⁻ y in segImg (fun e s => t e + σ e * s) (fun e y => σ e * (y - t e)) h e, ψ y
          ∂(volume.restrict I)
        = ∫⁻ y in segImg (fun e s => t e + σ e * s) (fun e y => σ e * (y - t e)) h e ∩ I, ψ y
          ∂volume := by rw [Measure.restrict_restrict hsegm]
      _ = ∫⁻ s in (fun s : ℝ => t e + σ e * s) ⁻¹'
            (segImg (fun e s => t e + σ e * s) (fun e y => σ e * (y - t e)) h e ∩ I),
            ψ (t e + σ e * s) ∂volume := (hmp.setLIntegral_comp_preimage_emb hemb ψ _).symm
      _ = ∫⁻ s in (fun s : ℝ => t e + σ e * s) ⁻¹' I ∩ Set.Ioc (0 : ℝ) h,
            ψ (t e + σ e * s) ∂volume := by rw [hpre]
      _ = ∫⁻ s in Set.Ioc (0 : ℝ) h, ((fun s : ℝ => t e + σ e * s) ⁻¹' I).indicator
            (fun s => ψ (t e + σ e * s)) s ∂volume := (setLIntegral_indicator hJ _).symm
      _ = _ := by
          refine lintegral_congr fun s => ?_
          by_cases hm : t e + σ e * s ∈ I <;> simp [Set.indicator, hm]

end ElboimSly
