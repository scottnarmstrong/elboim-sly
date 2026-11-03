/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Escape.Es4Transfer
public import Mathlib

/-!
# Adjoining an independent Poisson process to an `Es4Space`

The plan coupling, form used in S5 (c).

`prodExt`: an `Es4Space` on `Ω` and an independent Poisson process `N''` on `Ω''` give, on
`Ω × Ω''` with the product measure, an `Es4Space` for `(N ∘ fst, N' ∘ fst)` and the process
`N'' ∘ snd`, independent of `𝒢₀ ∨ σ(N) ∨ σ(N') ∨ 𝒩`.  `prodExt_ae`: an almost sure statement
about `ω ∘ fst` on the product holds on `Ω`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Escape

open ElboimSly ElboimSly.Cyclic

variable {k : ℕ} {β : ℝ} [Fact (0 < β)]

theorem prodExt {Ω Ω2 : Type} {𝒢₀ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    [m2 : MeasurableSpace Ω2] {Pr : Measure Ω} {P2 : Measure Ω2} [IsProbabilityMeasure P2]
    {N N' : Ω → Measure (CycS ℕ (k + 2) β)} {N2 : Ω2 → Measure (CycS ℕ (k + 2) β)}
    (hsp : Es4Space (k + 2) β 𝒢₀ Pr N N')
    (hN2 : IsPoissonPointProcess N2
      ((Measure.count : Measure ℕ).prod (ringIntensity (k + 2) β)) P2) :
    Es4Space (k + 2) β (𝒢₀.comap (Prod.fst : Ω × Ω2 → Ω)) (Pr.prod P2) (N ∘ Prod.fst)
      (N' ∘ Prod.fst) ∧
    IsPoissonPointProcess (N2 ∘ Prod.snd)
      ((Measure.count : Measure ℕ).prod (ringIntensity (k + 2) β)) (Pr.prod P2) ∧
    Indep (MeasurableSpace.comap (N2 ∘ Prod.snd) inferInstance)
      (𝒢₀.comap (Prod.fst : Ω × Ω2 → Ω) ⊔ MeasurableSpace.comap (N ∘ Prod.fst) inferInstance ⊔
        MeasurableSpace.comap (N' ∘ Prod.fst) inferInstance ⊔ cycNull (Pr.prod P2))
      (Pr.prod P2) := by
  have hPr : IsProbabilityMeasure Pr := hsp.ppp.isProbabilityMeasure
  have hmN : (Pr.prod P2).map (N ∘ Prod.fst) = Pr.map N := by
    rw [← Measure.map_map hsp.ppp.measurable measurable_fst, Measure.map_fst_prod]; simp
  have hmN' : (Pr.prod P2).map (N' ∘ Prod.fst) = Pr.map N' := by
    rw [← Measure.map_map hsp.ppp'.measurable measurable_fst, Measure.map_fst_prod]; simp
  have hmN2 : (Pr.prod P2).map (N2 ∘ Prod.snd) = P2.map N2 := by
    rw [← Measure.map_map hN2.measurable measurable_snd, Measure.map_snd_prod]; simp
  have h1 := hsp.ppp.of_map_eq (hsp.ppp.measurable.comp measurable_fst) hmN
  have h1' := hsp.ppp'.of_map_eq (hsp.ppp'.measurable.comp measurable_fst) hmN'
  have h2 := hN2.of_map_eq (hN2.measurable.comp measurable_snd) hmN2
  have hle1 : MeasurableSpace.comap N inferInstance ≤ mΩ := hsp.ppp.measurable.comap_le
  have hle2 : MeasurableSpace.comap N' inferInstance ≤ mΩ := hsp.ppp'.measurable.comap_le
  have hle0 := hsp.le
  have cN : MeasurableSpace.comap (N ∘ Prod.fst) inferInstance =
      (MeasurableSpace.comap N inferInstance).comap (Prod.fst : Ω × Ω2 → Ω) :=
    MeasurableSpace.comap_comp.symm
  have cN' : MeasurableSpace.comap (N' ∘ Prod.fst) inferInstance =
      (MeasurableSpace.comap N' inferInstance).comap (Prod.fst : Ω × Ω2 → Ω) :=
    MeasurableSpace.comap_comp.symm
  have cN2 : MeasurableSpace.comap (N2 ∘ Prod.snd) inferInstance =
      (MeasurableSpace.comap N2 inferInstance).comap (Prod.snd : Ω × Ω2 → Ω2) :=
    MeasurableSpace.comap_comp.symm
  have I1 : Indep (𝒢₀.comap (Prod.fst : Ω × Ω2 → Ω))
      (MeasurableSpace.comap (N ∘ Prod.fst) inferInstance) (Pr.prod P2) := by
    rw [cN]; exact indep_comap_fst Pr P2 hle0 hle1 hsp.indep
  have I2 : Indep (MeasurableSpace.comap (N' ∘ Prod.fst) inferInstance)
      (𝒢₀.comap (Prod.fst : Ω × Ω2 → Ω) ⊔ MeasurableSpace.comap (N ∘ Prod.fst) inferInstance)
      (Pr.prod P2) := by
    rw [cN, cN', ← MeasurableSpace.comap_sup]
    exact indep_comap_fst Pr P2 hle2 (sup_le hle0 hle1) hsp.indep'
  have I3 : Indep (MeasurableSpace.comap (N2 ∘ Prod.snd) inferInstance)
      (𝒢₀.comap (Prod.fst : Ω × Ω2 → Ω) ⊔ MeasurableSpace.comap (N ∘ Prod.fst) inferInstance ⊔
        MeasurableSpace.comap (N' ∘ Prod.fst) inferInstance ⊔ cycNull (Pr.prod P2))
      (Pr.prod P2) := by
    refine indep_sup_cycNull ?_
    have hI := indep_comap_snd_fst Pr P2
    refine indep_of_indep_of_le_right (indep_of_indep_of_le_left hI ?_) ?_
    · rw [cN2]; exact MeasurableSpace.comap_mono hN2.measurable.comap_le
    · rw [cN, cN']
      exact sup_le (sup_le (MeasurableSpace.comap_mono hle0) (MeasurableSpace.comap_mono hle1))
        (MeasurableSpace.comap_mono hle2)
  have hle : 𝒢₀.comap (Prod.fst : Ω × Ω2 → Ω) ≤ (inferInstance : MeasurableSpace (Ω × Ω2)) :=
    (MeasurableSpace.comap_mono hle0).trans measurable_fst.comap_le
  exact ⟨⟨h1, h1', hle, I1, I2⟩, h2, I3⟩

theorem prodExt_ae {Ω Ω2 : Type} [MeasurableSpace Ω] [MeasurableSpace Ω2] {Pr : Measure Ω}
    {P2 : Measure Ω2} [IsProbabilityMeasure P2] [SFinite Pr] {Q : Ω → Prop}
    (h : ∀ᵐ p ∂(Pr.prod P2), Q p.1) : ∀ᵐ ω ∂Pr, Q ω := by
  filter_upwards [Measure.ae_ae_of_ae_prod h] with ω hω
  obtain ⟨y, hy⟩ := hω.exists
  exact hy

end ElboimSly.Paper.Escape
