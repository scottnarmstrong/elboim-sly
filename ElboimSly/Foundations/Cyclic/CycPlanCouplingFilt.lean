/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycPlanCoupling
public import ElboimSly.Foundations.SRW.Admissible
public import Mathlib

/-!
# Plan-level coupling after a stopping time (d): enlarging `𝒢₀` by an independent environment

Plan-level coupling after a stopping time (d), proof ("`N''` is independent of
`σ(𝒢₀,N,N') ∨ 𝒩`, which contains `ℱ^𝒫_T`"). Enlarging `𝒢₀` to `𝒢₀ ∨ σ(N'')` keeps the hypotheses of
Several walks explored one after another (`cycNg_indep1`, `cycNg_indep2`), enlarges the filtration
(`cycMultiFilt_mono_gen`) and the stopping `σ`-algebra (`measurableSet_stopping_mono`), and the
filtration stays inside `σ(𝒢₀,N) ∨ 𝒩` (`cycMultiFilt_le_X`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

set_option linter.unusedSectionVars false

variable {I : Type*} [MeasurableSpace I] [Countable I] [MeasurableSingletonClass I] {d : ℕ}
  {β : ℝ} [Fact (0 < β)] (P : CycPlan I d β)
  {Ω : Type*} (𝒢₀ 𝒢₁ : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] {Pr : Measure Ω}
  {N : Ω → Measure (CycS I d β)}

theorem cycMultiFilt_mono_gen (hN : Measurable N) (h0 : 𝒢₀ ≤ mΩ)
    (h1 : 𝒢₁ ≤ mΩ) (hle : 𝒢₀ ≤ 𝒢₁) (s : ℝ≥0) :
    cycMultiFilt P 𝒢₀ hN h0 Pr s ≤ cycMultiFilt P 𝒢₁ hN h1 Pr s := by
  show cycFiltration Pr 𝒢₀ _ s ≤ cycFiltration Pr 𝒢₁ _ s
  rw [cycFiltration_eq 𝒢₀ P.junk, cycFiltration_eq 𝒢₁ P.junk]
  exact sup_le_sup_right (sup_le_sup_right hle _) _

theorem le_cycMultiFilt_gen (hN : Measurable N) (h0 : 𝒢₀ ≤ mΩ) (s : ℝ≥0) :
    𝒢₀ ≤ cycMultiFilt P 𝒢₀ hN h0 Pr s := by
  show 𝒢₀ ≤ cycFiltration Pr 𝒢₀ _ s
  rw [cycFiltration_eq 𝒢₀ P.junk]
  exact le_sup_left.trans le_sup_left

theorem cycMultiFilt_le_X (hN : Measurable N) (h0 : 𝒢₀ ≤ mΩ) (s : ℝ≥0) :
    cycMultiFilt P 𝒢₀ hN h0 Pr s ≤ 𝒢₀ ⊔ MeasurableSpace.comap N inferInstance ⊔ cycNull Pr := by
  show cycFiltration Pr 𝒢₀ _ s ≤ _
  have : Nonempty (CycEntry I d) := ⟨P.junk⟩
  rw [cycFiltration_eq 𝒢₀ P.junk]
  refine sup_le_sup_right (sup_le_sup_left ?_ _) _
  have hg : Measurable fun ν : Measure (CycS I d β) =>
      CycRec.trunc s (P.envFinal (cycNgood (fun ν : Measure (CycS I d β) => ν) ν)) :=
    measurable_trunc.comp ((measurable_envFinal_cycNgood P measurable_id).prodMk measurable_const)
  have : (fun ω => CycRec.trunc s (P.envFinal (cycNgood N ω))) =
      (fun ν : Measure (CycS I d β) =>
        CycRec.trunc s (P.envFinal (cycNgood (fun ν : Measure (CycS I d β) => ν) ν))) ∘ N := rfl
  rw [this, ← MeasurableSpace.comap_comp]
  exact MeasurableSpace.comap_mono hg.comap_le

/-- The stopping `σ`-algebra grows with the filtration. -/
theorem measurableSet_stopping_mono {ι : Type*} [Preorder ι] {m : MeasurableSpace Ω}
    {f g : Filtration ι m} (hfg : ∀ i, f i ≤ g i) {τ : Ω → WithTop ι}
    (hf : IsStoppingTime f τ) (hg : IsStoppingTime g τ) {A : Set Ω}
    (hA : MeasurableSet[hf.measurableSpace] A) : MeasurableSet[hg.measurableSpace] A := by
  refine ⟨iSup_mono hfg A hA.1, fun i => hfg i _ (hA.2 i)⟩

/-- Sets of `𝒢₀` belong to the stopping `σ`-algebra. -/
theorem measurableSet_stopping_of_gen {ι : Type*} [Preorder ι] {m : MeasurableSpace Ω}
    {g : Filtration ι m} [Nonempty ι] {τ : Ω → WithTop ι} (hg : IsStoppingTime g τ)
    {G : MeasurableSpace Ω} (hG : ∀ i, G ≤ g i) {A : Set Ω} (hA : MeasurableSet[G] A) :
    MeasurableSet[hg.measurableSpace] A := by
  obtain ⟨i0⟩ := ‹Nonempty ι›
  exact ⟨le_iSup g i0 _ (hG i0 _ hA), fun i => (hG i _ hA).inter (hg i)⟩

section indep

variable {N' : Ω → Measure (CycS I d β)} {N'' : Ω → Measure (ℕ × RingSpace d β)}

/-- The `σ`-algebra `σ(𝒢₀,N,N') ∨ 𝒩` from which `N''` is independent. -/
theorem cycX_le (h𝒢 : 𝒢₀ ≤ mΩ) (hN : Measurable N) (hN' : Measurable N') :
    𝒢₀ ⊔ MeasurableSpace.comap N inferInstance ⊔ MeasurableSpace.comap N' inferInstance ⊔
      cycNull Pr ≤ mΩ :=
  sup_le (sup_le (sup_le h𝒢 hN.comap_le) hN'.comap_le) (cycNull_le Pr)

variable [IsProbabilityMeasure Pr]

theorem cycNg_indep1 (h𝒢 : 𝒢₀ ≤ mΩ) (hN : Measurable N) (hN' : Measurable N')
    (hN'' : Measurable N'')
    (hI1 : Indep 𝒢₀ (MeasurableSpace.comap N inferInstance) Pr)
    (hI3 : Indep (MeasurableSpace.comap N'' inferInstance)
      (𝒢₀ ⊔ MeasurableSpace.comap N inferInstance ⊔ MeasurableSpace.comap N' inferInstance ⊔
        cycNull Pr) Pr) :
    Indep (𝒢₀ ⊔ MeasurableSpace.comap N'' inferInstance)
      (MeasurableSpace.comap N inferInstance) Pr := by
  rw [sup_comm]
  exact ElboimSly.SRW.indep_sup_of_indep hN''.comap_le h𝒢 hN.comap_le
    (le_sup_left.trans (le_sup_left.trans le_sup_left))
    ((le_sup_right.trans le_sup_left).trans le_sup_left) (cycX_le 𝒢₀ h𝒢 hN hN') hI3 hI1

theorem cycNg_indep2 (h𝒢 : 𝒢₀ ≤ mΩ) (hN : Measurable N) (hN' : Measurable N')
    (hN'' : Measurable N'')
    (hI2 : Indep (MeasurableSpace.comap N' inferInstance)
      (𝒢₀ ⊔ MeasurableSpace.comap N inferInstance) Pr)
    (hI3 : Indep (MeasurableSpace.comap N'' inferInstance)
      (𝒢₀ ⊔ MeasurableSpace.comap N inferInstance ⊔ MeasurableSpace.comap N' inferInstance ⊔
        cycNull Pr) Pr) :
    Indep (MeasurableSpace.comap N' inferInstance)
      ((𝒢₀ ⊔ MeasurableSpace.comap N'' inferInstance) ⊔
        MeasurableSpace.comap N inferInstance) Pr := by
  refine Indep.symm ?_
  have : (𝒢₀ ⊔ MeasurableSpace.comap N'' inferInstance) ⊔ MeasurableSpace.comap N inferInstance =
      MeasurableSpace.comap N'' inferInstance ⊔ (𝒢₀ ⊔ MeasurableSpace.comap N inferInstance) := by
    rw [sup_comm 𝒢₀, sup_assoc]
  rw [this]
  exact ElboimSly.SRW.indep_sup_of_indep hN''.comap_le (sup_le h𝒢 hN.comap_le) hN'.comap_le
    (le_sup_left.trans le_sup_left)
    (le_sup_right.trans le_sup_left) (cycX_le 𝒢₀ h𝒢 hN hN') hI3 hI2.symm

end indep

end ElboimSly.Cyclic

end
