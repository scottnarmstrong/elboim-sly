/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.SRW.Admissible
public import Mathlib

/-!
# Markov property for every SRW

Markov property for every SRW; admissible filtrations (a), (b), (c); independent stationary increments; Markov property at fixed times (b).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ElboimSly
namespace SRW

variable {d : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {Z : Ω → PathSpace d}

theorem IsSRW.isProbabilityMeasure (hZ : IsSRW P Z) : IsProbabilityMeasure P := by
  obtain ⟨hm, _, Ω', _, P', N', hN', hlaw⟩ := hZ
  have := hN'.isProbabilityMeasure
  refine ⟨?_⟩
  have := congrArg (fun μ => μ univ) hlaw
  simp only [Measure.map_apply hm MeasurableSet.univ,
    Measure.map_apply (measurable_canonical hN'.measurable) MeasurableSet.univ,
    preimage_univ, measure_univ] at this
  exact this

/-- Markov property for every SRW; admissible filtrations (a): `θ_t Z` has the law of `Z`. -/
theorem IsSRW.map_theta (hZ : IsSRW P Z) (t : ℝ≥0) :
    P.map (fun ω => theta t (Z ω)) = P.map Z := by
  obtain ⟨hm, _, Ω', _, P', N', hN', hlaw⟩ := hZ
  have h1 : P.map (fun ω => theta t (Z ω)) = (P.map Z).map (theta t) :=
    (Measure.map_map (measurable_theta t) hm).symm
  rw [h1, hlaw, Measure.map_map (measurable_theta t) (measurable_canonical hN'.measurable)]
  exact map_theta_canonical hN' t

/-- Markov property for every SRW; admissible filtrations (b): the stopped path and the shifted path are independent. -/
theorem IsSRW.indep_stop_theta (hZ : IsSRW P Z) (t : ℝ≥0) :
    IndepFun (fun ω => stopPath t (Z ω)) (fun ω => theta t (Z ω)) P := by
  have hprob : IsProbabilityMeasure P := IsSRW.isProbabilityMeasure (mΩ := mΩ) hZ
  obtain ⟨hm, _, Ω', _, P', N', hN', hlaw⟩ := hZ
  have := hN'.isProbabilityMeasure
  have hX := measurable_canonical hN'.measurable
  have hs := measurable_stopPath (d := d) t
  have ht := measurable_theta (d := d) t
  have hΦ : Measurable fun γ : PathSpace d => (stopPath t γ, theta t γ) := hs.prodMk ht
  have hind := (indepFun_iff_map_prod_eq_prod_map_map (f := fun ω => stopPath t (canonical d N' ω)) (g := fun ω => theta t (canonical d N' ω)) (hs.comp hX).aemeasurable
    (ht.comp hX).aemeasurable).1 (SRW.indepFun_stop_theta hN' t)
  rw [indepFun_iff_map_prod_eq_prod_map_map (f := fun ω => stopPath t (Z ω)) (g := fun ω => theta t (Z ω)) (hs.comp hm).aemeasurable (ht.comp hm).aemeasurable]
  have e1 : P.map (fun ω => (stopPath t (Z ω), theta t (Z ω))) = (P.map Z).map _ :=
    (Measure.map_map hΦ hm).symm
  have e2 : P.map (fun ω => stopPath t (Z ω)) = (P.map Z).map (stopPath t) :=
    (Measure.map_map hs hm).symm
  have e3 : P.map (fun ω => theta t (Z ω)) = (P.map Z).map (theta t) :=
    (Measure.map_map ht hm).symm
  have f1 : P'.map (fun ω => (stopPath t (canonical d N' ω), theta t (canonical d N' ω))) =
      (P'.map (canonical d N')).map _ := (Measure.map_map hΦ hX).symm
  have f2 : P'.map (fun ω => stopPath t (canonical d N' ω)) =
      (P'.map (canonical d N')).map (stopPath t) := (Measure.map_map hs hX).symm
  have f3 : P'.map (fun ω => theta t (canonical d N' ω)) =
      (P'.map (canonical d N')).map (theta t) := (Measure.map_map ht hX).symm
  rw [e1, e2, e3, hlaw, ← f1, ← f2, ← f3]
  exact hind

/-- Markov property for every SRW; admissible filtrations (b)/(c) with trivial `𝒢₀`: the natural filtration of an SRW
is admissible. -/
theorem IsSRW.isAdmissible_natFil (hZ : IsSRW P Z) : IsAdmissible P Z (natFil Z) := by
  refine ⟨natFil_mono Z, natFil_le hZ.1, fun s t h => measurable_natFil Z h, fun t => ?_⟩
  have hle : natFil Z t ≤ MeasurableSpace.comap (fun ω => stopPath t (Z ω)) inferInstance := by
    refine iSup₂_le fun s hs => ?_
    have : Measurable[MeasurableSpace.comap (fun ω => stopPath t (Z ω)) inferInstance]
        (fun ω => Z ω s) := by
      have h1 := (measurable_pi_apply (X := fun _ : ℝ≥0 => Fin d → ℤ) s).comp
        (comap_measurable (fun ω => stopPath t (Z ω)))
      convert h1 using 1
      funext ω
      simp [stopPath, min_eq_left hs]
    exact this.comap_le
  have h := hZ.indep_stop_theta t
  exact (indep_of_indep_of_le_left h hle).symm


/-- Markov property for every SRW; admissible filtrations (c): the natural filtration enlarged by the `σ`-algebra of a
random element independent of `Z` is admissible. -/
theorem IsSRW.isAdmissible_sup {β : Type*} [MeasurableSpace β] {W : Ω → β} (hZ : IsSRW P Z)
    (hW : Measurable W) (hind : IndepFun W Z P) :
    IsAdmissible P Z (fun t => MeasurableSpace.comap W inferInstance ⊔ natFil Z t) := by
  have := hZ.isProbabilityMeasure
  have hadm := hZ.isAdmissible_natFil
  have hA : MeasurableSpace.comap Z inferInstance ≤ mΩ := hZ.1.comap_le
  have hBA : ∀ t, natFil Z t ≤ MeasurableSpace.comap Z inferInstance := fun t =>
    iSup₂_le fun s _ =>
      ((measurable_pi_apply s).comp (comap_measurable Z)).comap_le
  have hCA : ∀ t, MeasurableSpace.comap (fun ω => theta t (Z ω)) inferInstance ≤
      MeasurableSpace.comap Z inferInstance := fun t =>
    ((measurable_theta t).comp (comap_measurable Z)).comap_le
  refine ⟨fun s t h => sup_le_sup_left (hadm.mono h) _, fun t => sup_le hW.comap_le (hadm.le t),
    fun s t h => (hadm.adapted s t h).mono le_sup_right le_rfl, fun t => ?_⟩
  exact (indep_sup_of_indep hW.comap_le (hadm.le t) ((measurable_theta t).comp hZ.1).comap_le
    (hBA t) (hCA t) hA hind (hadm.indep t).symm).symm

end SRW
end ElboimSly
