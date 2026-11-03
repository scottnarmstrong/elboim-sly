/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycMultiFilt
public import Mathlib

/-!
# Several walks explored one after another (a), Step 1: the `π`-`λ` argument

Several walks explored one after another (a), Step 1. `indep_of_generators`: if `Ñ` is independent of
the sets `A ∩ B`, `A ∈ 𝒢₀`, `B ∈ σ(Y)`, with law `Π`, then `Ñ` is independent of
`𝒢₀ ∨ σ(Y) ∨ 𝒩`.
-/

@[expose] public section

open MeasureTheory Set MeasurableSpace
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

variable {I : Type*} [MeasurableSpace I] {d : ℕ}
  {Ω : Type*} (𝒢₀ : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω]
  {S : Type*} [MeasurableSpace S]

/-- The `λ`-system argument: a statement about `Ñ` that holds on a generating `π`-system and is
stable under complements and disjoint unions holds on the generated `σ`-algebra. -/
theorem dynkin_indep (hmle : 𝒢₀ ≤ mΩ)
    (Pr : Measure Ω) [IsProbabilityMeasure Pr] (C : Set (Set Ω)) (hGen : 𝒢₀ = generateFrom C)
    (hPi : IsPiSystem C) (Nt : Ω → Measure S) (hNt : Measurable Nt) (Pi : Measure (Measure S))
    (hbasic : ∀ t ∈ C, ∀ F : Set (Measure S), MeasurableSet F →
      Pr (t ∩ Nt ⁻¹' F) = Pr t * Pi F)
    (hPiF : ∀ F : Set (Measure S), MeasurableSet F → Pi F = Pr (Nt ⁻¹' F))
    {t : Set Ω} (ht : MeasurableSet[𝒢₀] t) {F : Set (Measure S)} (hF : MeasurableSet F) :
    Pr (t ∩ Nt ⁻¹' F) = Pr t * Pi F := by
  have key : ∀ t (ht : MeasurableSet[𝒢₀] t), ∀ F : Set (Measure S), MeasurableSet F →
      Pr (t ∩ Nt ⁻¹' F) = Pr t * Pi F := by
    refine @MeasurableSpace.induction_on_inter Ω 𝒢₀
      (fun t _ => ∀ F : Set (Measure S), MeasurableSet F → Pr (t ∩ Nt ⁻¹' F) = Pr t * Pi F)
      C hGen hPi ?_ ?_ ?_ ?_
    · intro F hF; simp
    · exact fun t htC F hF => hbasic t htC F hF
    · intro t htm ih F hF
      have htm' : MeasurableSet t := hmle _ htm
      have hPiFin : Pi F ≠ ⊤ := by rw [hPiF F hF]; exact measure_ne_top _ _
      have hE : MeasurableSet (Nt ⁻¹' F) := hNt hF
      have e1 : tᶜ ∩ Nt ⁻¹' F = Nt ⁻¹' F \ (t ∩ Nt ⁻¹' F) := by
        ext x; simp only [mem_inter_iff, mem_compl_iff, mem_sdiff]; tauto
      have hsub : t ∩ Nt ⁻¹' F ⊆ Nt ⁻¹' F := inter_subset_right
      rw [e1, measure_sdiff hsub (htm'.inter hE).nullMeasurableSet (measure_ne_top _ _),
        ih F hF, ← hPiF F hF, prob_compl_eq_one_sub htm', ENNReal.sub_mul (fun _ _ => hPiFin),
        one_mul]
    · intro f hdisj hfm ih F hF
      have hfm' : ∀ i, MeasurableSet (f i) := fun i => hmle _ (hfm i)
      rw [iUnion_inter, measure_iUnion, measure_iUnion hdisj hfm', ← ENNReal.tsum_mul_right]
      · exact tsum_congr fun i => ih i F hF
      · exact fun i j hij => (hdisj hij).mono inter_subset_left inter_subset_left
      · exact fun i => (hfm' i).inter (hNt hF)
  exact key t ht F hF

/-- The `π`-`λ` argument of Step 1. -/
theorem indep_of_generators (Pr : Measure Ω) [IsProbabilityMeasure Pr]
    (h𝒢 : 𝒢₀ ≤ mΩ) (Y : Ω → CycRec I d) (hY : Measurable Y)
    (Nt : Ω → Measure S) (Pi : Measure (Measure S))
    (hgen : ∀ A : Set Ω, MeasurableSet[𝒢₀] A → ∀ B : Set Ω,
      MeasurableSet[MeasurableSpace.comap Y inferInstance] B → ∀ F : Set (Measure S),
        MeasurableSet F → Pr (A ∩ B ∩ Nt ⁻¹' F) = Pr (A ∩ B) * Pi F)
    (hNt : Measurable Nt)
    {A : Set Ω} (hA : MeasurableSet[𝒢₀ ⊔ MeasurableSpace.comap Y inferInstance ⊔ @cycNull Ω mΩ Pr] A)
    {F : Set (Measure S)} (hF : MeasurableSet F) :
    Pr (A ∩ Nt ⁻¹' F) = Pr A * Pi F := by
  classical
  have hYc : MeasurableSpace.comap Y inferInstance ≤ mΩ := hY.comap_le
  have hmle : 𝒢₀ ⊔ MeasurableSpace.comap Y inferInstance ⊔ @cycNull Ω mΩ Pr ≤ mΩ :=
    sup_le (sup_le h𝒢 hYc) (cycNull_le Pr)
  have h1 : 𝒢₀ ≤ 𝒢₀ ⊔ MeasurableSpace.comap Y inferInstance ⊔ @cycNull Ω mΩ Pr :=
    le_sup_left.trans le_sup_left
  have h2 : MeasurableSpace.comap Y inferInstance ≤
      𝒢₀ ⊔ MeasurableSpace.comap Y inferInstance ⊔ @cycNull Ω mΩ Pr :=
    le_sup_right.trans le_sup_left
  have h3 : @cycNull Ω mΩ Pr ≤ 𝒢₀ ⊔ MeasurableSpace.comap Y inferInstance ⊔ @cycNull Ω mΩ Pr :=
    le_sup_right
  let C : Set (Set Ω) := {t | ∃ a b c : Set Ω, MeasurableSet[𝒢₀] a ∧
    MeasurableSet[MeasurableSpace.comap Y inferInstance] b ∧
    (c = univ ∨ (MeasurableSet c ∧ Pr c = 0)) ∧ t = a ∩ b ∩ c}
  have hGen : 𝒢₀ ⊔ MeasurableSpace.comap Y inferInstance ⊔ @cycNull Ω mΩ Pr =
      MeasurableSpace.generateFrom C := by
    refine le_antisymm (sup_le (sup_le ?_ ?_) ?_) ?_
    · intro a ha
      exact MeasurableSpace.measurableSet_generateFrom
        ⟨a, univ, univ, ha, MeasurableSet.univ, Or.inl rfl, by simp⟩
    · intro b hb
      exact MeasurableSpace.measurableSet_generateFrom
        ⟨univ, b, univ, MeasurableSet.univ, hb, Or.inl rfl, by simp⟩
    · refine MeasurableSpace.generateFrom_le fun c hc => ?_
      exact MeasurableSpace.measurableSet_generateFrom
        ⟨univ, univ, c, MeasurableSet.univ, MeasurableSet.univ, Or.inr hc, by simp⟩
    · refine MeasurableSpace.generateFrom_le ?_
      rintro _ ⟨a, b, c, ha, hb, hc, rfl⟩
      refine @MeasurableSet.inter Ω _ _ _ (@MeasurableSet.inter Ω _ _ _ (h1 _ ha) (h2 _ hb)) ?_
      rcases hc with rfl | hc
      · exact @MeasurableSet.univ Ω _
      · exact h3 _ (MeasurableSpace.measurableSet_generateFrom
          (show c ∈ {A | MeasurableSet A ∧ Pr A = 0} from hc))
  have hPi : IsPiSystem C := by
    rintro _ ⟨a, b, c, ha, hb, hc, rfl⟩ _ ⟨a', b', c', ha', hb', hc', rfl⟩ -
    refine ⟨a ∩ a', b ∩ b', c ∩ c', @MeasurableSet.inter Ω 𝒢₀ _ _ ha ha',
      @MeasurableSet.inter Ω (MeasurableSpace.comap Y inferInstance) _ _ hb hb', ?_, ?_⟩
    · rcases hc with rfl | hc
      · rcases hc' with rfl | hc'
        · exact Or.inl (by simp)
        · exact Or.inr (by simpa using hc')
      · rcases hc' with rfl | hc'
        · exact Or.inr (by simpa using hc)
        · exact Or.inr ⟨hc.1.inter hc'.1, measure_mono_null inter_subset_left hc.2⟩
    · ext x; simp only [mem_inter_iff]; tauto
  have hPiF : ∀ F : Set (Measure S), MeasurableSet F → Pi F = Pr (Nt ⁻¹' F) := fun F hF => by
    have := hgen univ MeasurableSet.univ univ MeasurableSet.univ F hF
    simpa using this.symm
  refine dynkin_indep _ hmle Pr C hGen hPi Nt hNt Pi ?_ hPiF hA hF
  rintro _ ⟨a, b, c, ha, hb, hc, rfl⟩ F hF
  rcases hc with rfl | hc
  · simpa using hgen a ha b hb F hF
  · have h0 : Pr (a ∩ b ∩ c) = 0 := measure_mono_null inter_subset_right hc.2
    have h0' : Pr (a ∩ b ∩ c ∩ Nt ⁻¹' F) = 0 := measure_mono_null inter_subset_left h0
    rw [h0, h0']; simp

end ElboimSly.Cyclic

end
