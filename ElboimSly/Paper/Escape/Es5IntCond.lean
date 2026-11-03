/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Escape.ResampleTower
public import Mathlib

/-!
# `Φ_B(ρ_T)` is a version of the conditional expectation `E[1_{N ∈ B} | ℱ_T]`

Resampling formula (b), "the mathlib `condExp` statement": `resPhi` is `ℱ_T`-measurable
and `P(A ∩ {N ∈ B}) = ∫_A Φ_B dP` for `A ∈ ℱ_T`, hence `Φ_B(ρ_T) = P(N ∈ B | ℱ_T)` a.s.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Escape

open ElboimSly.Cyclic ElboimSly.Paper

variable {Ω : Type*} {I : Type*} [MeasurableSpace I] [Countable I] [MeasurableSingletonClass I]
  {d : ℕ} {β : ℝ} [Fact (0 < β)] (P : CycPlan I d β) (𝒢₀ : MeasurableSpace Ω)
  [mΩ : MeasurableSpace Ω] {Pr : Measure Ω} {N N' : Ω → Measure (CycS I d β)}
  (hN : IsPoissonPointProcess N (cycIntensity I d β) Pr)
  (hN' : IsPoissonPointProcess N' (cycIntensity I d β) Pr)
  (hI1 : Indep 𝒢₀ (MeasurableSpace.comap N inferInstance) Pr)
  (hI2 : Indep (MeasurableSpace.comap N' inferInstance)
    (𝒢₀ ⊔ MeasurableSpace.comap N inferInstance) Pr)

include hN hN' hI1 hI2 in
/-- **resampling formula (b)**, `condExp` form. -/
theorem resPhi_toReal_ae_eq_condExp (hK : 0 < P.K) (h𝒢 : 𝒢₀ ≤ mΩ) {T : Ω → WithTop ℝ≥0}
    (hT : IsStoppingTime (cycMultiFilt P 𝒢₀ hN.measurable h𝒢 Pr) T)
    (hfin : Pr {ω | T ω ≠ ⊤} = 1) {B : Set (Measure (CycS I d β))} (hB : MeasurableSet B) :
    (fun ω => (resPhi P Pr N T B ω).toReal) =ᵐ[Pr]
      Pr[(N ⁻¹' B).indicator (fun _ => (1 : ℝ)) | hT.measurableSpace] := by
  have hPr := hN.isProbabilityMeasure
  obtain ⟨hmeas, hint⟩ := es4_resample_b P 𝒢₀ hN hN' hI1 hI2 hK h𝒢 hT hfin hB
  have hm := hT.measurableSpace_le
  have : IsFiniteMeasure (Pr.trim hm) := isFiniteMeasure_trim hm
  have hNB : MeasurableSet (N ⁻¹' B) := hN.measurable hB
  have hle1 : ∀ ω, resPhi P Pr N T B ω ≤ 1 := fun ω => by
    unfold resPhi resampleProb
    have : IsProbabilityMeasure (Pr.map N) := (Measure.isProbabilityMeasure_map_iff hN.measurable.aemeasurable).2 hPr
    exact prob_le_one
  have hmeasR : Measurable[hT.measurableSpace] (fun ω => (resPhi P Pr N T B ω).toReal) :=
    hmeas.ennreal_toReal
  refine ae_eq_condExp_of_forall_setIntegral_eq hm
    ((integrable_const (1 : ℝ)).indicator hNB) (fun s hs _ => ?_) (fun s hs _ => ?_)
    hmeasR.stronglyMeasurable.aestronglyMeasurable
  · refine Integrable.integrableOn ?_
    refine Integrable.mono' (integrable_const (1 : ℝ))
      ((hmeasR.mono hm le_rfl).aestronglyMeasurable) (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_of_nonneg ENNReal.toReal_nonneg]
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using hle1 ω)
  · have hsm : MeasurableSet s := hm _ hs
    have h1 : ∫ ω in s, (resPhi P Pr N T B ω).toReal ∂Pr =
        (∫⁻ ω in s, resPhi P Pr N T B ω ∂Pr).toReal := by
      refine integral_toReal ((hmeas.mono hm le_rfl).aemeasurable) ?_
      exact Filter.Eventually.of_forall fun ω => lt_of_le_of_lt (hle1 ω) ENNReal.one_lt_top
    have h2 : ∫⁻ ω in s, resPhi P Pr N T B ω ∂Pr = Pr (s ∩ {ω | N ω ∈ B}) := (hint hs).symm
    rw [h1, h2, setIntegral_indicator hNB, setIntegral_const]
    simp [Measure.real]
    rfl

end ElboimSly.Paper.Escape
