/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Escape.ResampleTower
public import ElboimSly.Paper.Escape.LamStopping
public import Mathlib

/-!
# Lower bounds for `Φ_C(ρ_T)` from lower bounds on `ℱ_T`-measurable sets

ES22 Lemma 5.5, Step 1 (conditioning on `ℱ_{S₃}`).

`resPhi_ge_of_forall`: if `a · P(A ∩ {N ∈ H}) ≤ P(A ∩ {N ∈ C})` for every `A ∈ ℱ_T`, and
`{N ∈ H} ∈ ℱ_T`, then `Φ_C(ρ_T) ≥ a` almost surely on `{N ∈ H}`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Escape

open ElboimSly.Cyclic ElboimSly.Paper

variable {Ω : Type*}

section lower

variable {I : Type*} [MeasurableSpace I] [Countable I] [MeasurableSingletonClass I] {d : ℕ}
  {β : ℝ} [Fact (0 < β)] (P : CycPlan I d β) (𝒢₀ : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω]
  {Pr : Measure Ω} {N N' : Ω → Measure (CycS I d β)}
  (hN : IsPoissonPointProcess N (cycIntensity I d β) Pr)
  (hN' : IsPoissonPointProcess N' (cycIntensity I d β) Pr)
  (hI1 : Indep 𝒢₀ (MeasurableSpace.comap N inferInstance) Pr)
  (hI2 : Indep (MeasurableSpace.comap N' inferInstance)
    (𝒢₀ ⊔ MeasurableSpace.comap N inferInstance) Pr)

include hN hN' hI1 hI2 in
/-- If `a P(A ∩ {N ∈ H}) ≤ P(A ∩ {N ∈ C})` for all `A ∈ ℱ_T` and `{N ∈ H} ∈ ℱ_T`, then
`Φ_C(ρ_T) ≥ a` a.s. on `{N ∈ H}`. -/
theorem resPhi_ge_of_forall (hK0 : 0 < P.K) (h𝒢 : 𝒢₀ ≤ mΩ) {T : Ω → WithTop ℝ≥0}
    (hT : IsStoppingTime (cycMultiFilt P 𝒢₀ hN.measurable h𝒢 Pr) T)
    (hfin : Pr {ω | T ω ≠ ⊤} = 1) {H C : Set (Measure (CycS I d β))}
    (hC : MeasurableSet C) (hHT : MeasurableSet[hT.measurableSpace] (N ⁻¹' H)) {a : ℝ≥0∞}
    (h : ∀ A : Set Ω, MeasurableSet[hT.measurableSpace] A →
      a * Pr (A ∩ N ⁻¹' H) ≤ Pr (A ∩ {ω | N ω ∈ C})) :
    ∀ᵐ ω ∂Pr, N ω ∈ H → a ≤ resPhi P Pr N T C ω := by
  have hPr := hN.isProbabilityMeasure
  obtain ⟨hmC, hCint⟩ := es4_resample_b P 𝒢₀ hN hN' hI1 hI2 hK0 h𝒢 hT hfin hC
  have hle := hT.measurableSpace_le
  have hHm : MeasurableSet (N ⁻¹' H) := hle _ hHT
  have h1 : Measurable[hT.measurableSpace] ((N ⁻¹' H).indicator (fun _ => a)) :=
    measurable_const.indicator hHT
  have key : (N ⁻¹' H).indicator (fun _ => a) ≤ᵐ[Pr] resPhi P Pr N T C := by
    refine ae_le_of_setLIntegral_le_sub hle Pr h1 hmC fun A hA => ?_
    have hAm : MeasurableSet A := hle _ hA
    calc ∫⁻ ω in A, (N ⁻¹' H).indicator (fun _ => a) ω ∂Pr
        = a * Pr (A ∩ N ⁻¹' H) := by
          rw [lintegral_indicator_const hHm, Measure.restrict_apply hHm, inter_comm, mul_comm]
      _ ≤ Pr (A ∩ {ω | N ω ∈ C}) := h A hA
      _ = ∫⁻ ω in A, resPhi P Pr N T C ω ∂Pr := hCint hA
  filter_upwards [key] with ω hω hmem
  simpa [Set.indicator, hmem] using hω

end lower

end ElboimSly.Paper.Escape
