/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycMultiRegion
public import ElboimSly.Foundations.Cyclic.CycLines
public import ElboimSly.Foundations.Cyclic.CycTruncMeas
public import Mathlib

/-!
# Several walks explored one after another (a): the joint exploration filtration

World-lines of a plan; joint exploration filtration (c) and several walks explored one after another (a), Step 1.

* `multiFilt`: the joint exploration filtration `s ↦ 𝒢₀ ∨ σ(Rec(s') : s' ≤ s) ∨ 𝒩` as a Mathlib
  `Filtration`, when the final record `R` is measurable;
* `cycFiltration_eq`: `σ(Rec(s') : s' ≤ s) = σ(Trunc_s ∘ R)`;
-/

@[expose] public section

open MeasureTheory Set MeasurableSpace
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

variable {I : Type*} [MeasurableSpace I] {d : ℕ} {β : ℝ} [Fact (0 < β)]
  {Ω : Type*} (𝒢₀ : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω]

section filt

variable [Countable I] [MeasurableSingletonClass I]

theorem cycFiltration_eq (junk : CycEntry I d) (Pr : Measure Ω)
    (R : Ω → CycRec I d) (s : ℝ≥0) :
    cycFiltration Pr 𝒢₀ R s =
      𝒢₀ ⊔ MeasurableSpace.comap (fun ω => CycRec.trunc s (R ω)) inferInstance ⊔ @cycNull Ω mΩ Pr := by
  have : Nonempty (CycEntry I d) := ⟨junk⟩
  unfold cycFiltration
  congr 2
  refine le_antisymm (iSup₂_le fun s' hs' => ?_) (le_iSup₂_of_le s le_rfl le_rfl)
  have : (fun ω => CycRec.trunc s' (R ω)) =
      (CycRec.trunc s') ∘ (fun ω => CycRec.trunc s (R ω)) := by
    funext ω
    exact (CycRec.trunc_trunc junk hs' (R ω)).symm
  have hg : Measurable (CycRec.trunc (I := I) (d := d) s') :=
    measurable_trunc.comp (measurable_id.prodMk measurable_const)
  rw [this, ← MeasurableSpace.comap_comp]
  exact MeasurableSpace.comap_mono hg.comap_le

theorem cycNull_le (Pr : Measure Ω) : @cycNull Ω mΩ Pr ≤ mΩ :=
  MeasurableSpace.generateFrom_le fun _ hA => hA.1

omit [Countable I] [MeasurableSingletonClass I] in
theorem cycFiltration_mono (Pr : Measure Ω) (R : Ω → CycRec I d)
    {a b : ℝ≥0} (hab : a ≤ b) : cycFiltration Pr 𝒢₀ R a ≤ cycFiltration Pr 𝒢₀ R b := by
  have hX : (⨆ s' ≤ a, MeasurableSpace.comap (fun ω => CycRec.trunc s' (R ω))
        (inferInstance : MeasurableSpace (CycRec I d))) ≤
      ⨆ s' ≤ b, MeasurableSpace.comap (fun ω => CycRec.trunc s' (R ω))
        (inferInstance : MeasurableSpace (CycRec I d)) :=
    iSup₂_le fun s' hs' => le_iSup₂_of_le s' (hs'.trans hab) le_rfl
  exact sup_le_sup_right (sup_le_sup_left hX _) _

theorem cycFiltration_le (junk : CycEntry I d) (Pr : Measure Ω)
    (h𝒢 : 𝒢₀ ≤ mΩ) (R : Ω → CycRec I d) (hR : Measurable R) (s : ℝ≥0) :
    cycFiltration Pr 𝒢₀ R s ≤ mΩ := by
  have : Nonempty (CycEntry I d) := ⟨junk⟩
  rw [cycFiltration_eq 𝒢₀ junk]
  refine sup_le (sup_le h𝒢 ?_) (cycNull_le Pr)
  exact (measurable_trunc.comp (hR.prodMk measurable_const)).comap_le

/-- The joint exploration filtration of world-lines of a plan; joint exploration filtration (c) as a Mathlib `Filtration`, for a
measurable final record `R`. -/
@[instance_reducible] noncomputable def multiFilt (junk : CycEntry I d) (Pr : Measure Ω)
    (h𝒢 : 𝒢₀ ≤ mΩ) (R : Ω → CycRec I d) (hR : Measurable R) :
    Filtration ℝ≥0 mΩ where
  seq s := cycFiltration Pr 𝒢₀ R s
  mono' _ _ hab := cycFiltration_mono 𝒢₀ Pr R hab
  le' s := cycFiltration_le 𝒢₀ junk Pr h𝒢 R hR s

end filt

end ElboimSly.Cyclic

end
