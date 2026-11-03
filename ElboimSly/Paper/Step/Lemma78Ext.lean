/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Escape.Es55Ext
public import ElboimSly.Foundations.Cyclic.CycDrivenLawBridge
public import ElboimSly.Foundations.PPP.ExistenceExamples
public import Mathlib

/-!
# The extension of the probability space

W_2 after zeta_i, given ℱ^+_zeta_i ("on an extension of the probability space"). A Poisson point process
`N` of intensity `ringIntensity d β` on `(Ω, P)` is carried, on the product `(Ω × Ω₂) × Ω₃` with an
independent process `N'` of intensity `cycIntensity Unit d β` and an independent process `N''` of
intensity `# ⊗ ringIntensity`, to the three processes of `step78_couple_zeta`, with trivial `𝒢₀ = ⊥`
(as in `prodExt` of `Es55Ext`). The first coordinate projection `f` pushes the product measure to `P`,
and `N = (Nr ∘ f)` mapped by `Prod.mk `.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Step

open ElboimSly ElboimSly.Cyclic ElboimSly.Paper.Escape

variable {d : ℕ} {β : ℝ} [Fact (0 < β)]

theorem step78_ppp_comp {Ω0 Ω' : Type} [MeasurableSpace Ω0] [MeasurableSpace Ω'] {S : Type*}
    [MeasurableSpace S] {μ : Measure S} {Q : Measure Ω0} {M : Ω0 → Measure S}
    (h : IsPoissonPointProcess M μ Q) {P' : Measure Ω'} {g : Ω' → Ω0} (hg : Measurable g)
    (hmap : P'.map g = Q) : IsPoissonPointProcess (M ∘ g) μ P' :=
  h.of_map_eq (h.measurable.comp hg) (by rw [← Measure.map_map h.measurable hg, hmap])

/-- A set `A` whose preimage under the first projection is a.e. contained in a measurable `B` has
outer measure at most that of `B` (Fubini for the sections of `B`). -/
theorem step78_measure_le_prod {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} [SFinite μ] [IsProbabilityMeasure ν] (A : Set X)
    {B : Set (X × Y)} (hB : MeasurableSet B) (h : Prod.fst ⁻¹' A ≤ᵐ[μ.prod ν] B) :
    μ A ≤ (μ.prod ν) B := by
  set E := toMeasurable (μ.prod ν) (Prod.fst ⁻¹' A \ B) with hE
  have hE0 : (μ.prod ν) E = 0 := by rw [measure_toMeasurable]; exact ae_le_set.1 h
  have hB' : MeasurableSet (B ∪ E) := hB.union (measurableSet_toMeasurable _ _)
  have hsub : ∀ y, A ⊆ (fun x => (x, y)) ⁻¹' (B ∪ E) := by
    intro y x hx
    by_cases hxB : (x, y) ∈ B
    · exact Or.inl hxB
    · exact Or.inr (subset_toMeasurable _ _ ⟨hx, hxB⟩)
  calc μ A = ∫⁻ _y, μ A ∂ν := by simp
    _ ≤ ∫⁻ y, μ ((fun x => (x, y)) ⁻¹' (B ∪ E)) ∂ν :=
        lintegral_mono fun y => measure_mono (hsub y)
    _ = (μ.prod ν) (B ∪ E) := (Measure.prod_apply_symm hB').symm
    _ ≤ (μ.prod ν) B + (μ.prod ν) E := measure_union_le _ _
    _ = (μ.prod ν) B := by rw [hE0, add_zero]

theorem step78_ext {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {Nr : Ω → Measure (RingSpace d β)}
    (hN : IsPoissonPointProcess Nr (ringIntensity d β) P) :
    ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (P' : Measure Ω') (f : Ω' → Ω)
      (N N' : Ω' → Measure (CycS Unit d β)) (N'' : Ω' → Measure (ℕ × RingSpace d β)),
      IsProbabilityMeasure P' ∧ Measurable f ∧ P'.map f = P ∧
      (∀ ω', N ω' = (Nr (f ω')).map (Prod.mk ())) ∧
      IsPoissonPointProcess N (cycIntensity Unit d β) P' ∧
      IsPoissonPointProcess N' (cycIntensity Unit d β) P' ∧
      IsPoissonPointProcess N'' ((Measure.count : Measure ℕ).prod (ringIntensity d β)) P' ∧
      Indep (⊥ : MeasurableSpace Ω') (MeasurableSpace.comap N inferInstance) P' ∧
      Indep (MeasurableSpace.comap N' inferInstance)
        ((⊥ : MeasurableSpace Ω') ⊔ MeasurableSpace.comap N inferInstance) P' ∧
      Indep (MeasurableSpace.comap N'' inferInstance)
        ((⊥ : MeasurableSpace Ω') ⊔ MeasurableSpace.comap N inferInstance ⊔
          MeasurableSpace.comap N' inferInstance ⊔ cycNull P') P' ∧
      (∀ (A : Set Ω) (B : Set Ω'), MeasurableSet B → f ⁻¹' A ≤ᵐ[P'] B → P A ≤ P' B) := by
  have := hN.isProbabilityMeasure
  have hNu := isPPP_envUnit hN
  obtain ⟨Ω2, m2, P2, N2, hP2, hN2, -⟩ := exists_isPoissonPointProcess (cycIntensity Unit d β)
  obtain ⟨Ω3, m3, P3, N3, hP3, hN3, -⟩ := exists_isPoissonPointProcess
    ((Measure.count : Measure ℕ).prod (ringIntensity d β))
  set Nu : Ω → Measure (CycS Unit d β) := fun ω => (Nr ω).map (Prod.mk ()) with hNu_def
  have hf1 : ((P.prod P2).prod P3).map (Prod.fst : (Ω × Ω2) × Ω3 → Ω × Ω2) = P.prod P2 := by
    rw [Measure.map_fst_prod]; simp
  have hf3 : ((P.prod P2).prod P3).map (Prod.snd : (Ω × Ω2) × Ω3 → Ω3) = P3 := by
    rw [Measure.map_snd_prod]; simp
  have hg1 : ((P.prod P2).prod P3).map (fun p : (Ω × Ω2) × Ω3 => p.1.1) = P := by
    have : (fun p : (Ω × Ω2) × Ω3 => p.1.1) = Prod.fst ∘ Prod.fst := rfl
    rw [this, ← Measure.map_map measurable_fst measurable_fst, hf1, Measure.map_fst_prod]; simp
  have hg2 : ((P.prod P2).prod P3).map (fun p : (Ω × Ω2) × Ω3 => p.1.2) = P2 := by
    have : (fun p : (Ω × Ω2) × Ω3 => p.1.2) = Prod.snd ∘ Prod.fst := rfl
    rw [this, ← Measure.map_map measurable_snd measurable_fst, hf1, Measure.map_snd_prod]; simp
  refine ⟨(Ω × Ω2) × Ω3, inferInstance, (P.prod P2).prod P3, fun p => p.1.1,
    fun p => Nu p.1.1, fun p => N2 p.1.2, fun p => N3 p.2, inferInstance,
    measurable_fst.comp measurable_fst, hg1, fun ω' => rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact step78_ppp_comp hNu (g := fun p : (Ω × Ω2) × Ω3 => p.1.1)
      (measurable_fst.comp measurable_fst) hg1
  · exact step78_ppp_comp hN2 (g := fun p : (Ω × Ω2) × Ω3 => p.1.2)
      (measurable_snd.comp measurable_fst) hg2
  · exact step78_ppp_comp hN3 (g := fun p : (Ω × Ω2) × Ω3 => p.2) measurable_snd hf3
  · exact indep_bot_left _
  · -- `N'` against `N`
    have I12 : Indep (MeasurableSpace.comap (fun p : Ω × Ω2 => N2 p.2) inferInstance)
        (MeasurableSpace.comap (fun p : Ω × Ω2 => Nu p.1) inferInstance) (P.prod P2) := by
      refine indep_of_indep_of_le_right (indep_of_indep_of_le_left (indep_comap_snd_fst P P2) ?_) ?_
      · rw [show (fun p : Ω × Ω2 => N2 p.2) = N2 ∘ Prod.snd from rfl, ← MeasurableSpace.comap_comp]
        exact MeasurableSpace.comap_mono hN2.measurable.comap_le
      · rw [show (fun p : Ω × Ω2 => Nu p.1) = Nu ∘ Prod.fst from rfl, ← MeasurableSpace.comap_comp]
        exact MeasurableSpace.comap_mono hNu.measurable.comap_le
    have h := indep_comap_fst (P.prod P2) P3
      (hN2.measurable.comp measurable_snd).comap_le (hNu.measurable.comp measurable_fst).comap_le
      I12
    have e1 : MeasurableSpace.comap (fun p : (Ω × Ω2) × Ω3 => N2 p.1.2) inferInstance =
        (MeasurableSpace.comap (fun p : Ω × Ω2 => N2 p.2) inferInstance).comap Prod.fst :=
      (MeasurableSpace.comap_comp (f := fun p : Ω × Ω2 => N2 p.2) (g := Prod.fst)).symm
    have e2 : MeasurableSpace.comap (fun p : (Ω × Ω2) × Ω3 => Nu p.1.1) inferInstance =
        (MeasurableSpace.comap (fun p : Ω × Ω2 => Nu p.1) inferInstance).comap Prod.fst :=
      (MeasurableSpace.comap_comp (f := fun p : Ω × Ω2 => Nu p.1) (g := Prod.fst)).symm
    rw [bot_sup_eq, e1, e2]
    exact h
  · -- `N''` against everything
    have e1 : MeasurableSpace.comap (fun p : (Ω × Ω2) × Ω3 => N2 p.1.2) inferInstance =
        (MeasurableSpace.comap (fun p : Ω × Ω2 => N2 p.2) inferInstance).comap Prod.fst :=
      (MeasurableSpace.comap_comp (f := fun p : Ω × Ω2 => N2 p.2) (g := Prod.fst)).symm
    have e2 : MeasurableSpace.comap (fun p : (Ω × Ω2) × Ω3 => Nu p.1.1) inferInstance =
        (MeasurableSpace.comap (fun p : Ω × Ω2 => Nu p.1) inferInstance).comap Prod.fst :=
      (MeasurableSpace.comap_comp (f := fun p : Ω × Ω2 => Nu p.1) (g := Prod.fst)).symm
    have e3 : MeasurableSpace.comap (fun p : (Ω × Ω2) × Ω3 => N3 p.2) inferInstance =
        (MeasurableSpace.comap N3 inferInstance).comap Prod.snd :=
      MeasurableSpace.comap_comp.symm
    refine indep_sup_cycNull ?_
    have hI := indep_comap_snd_fst (P.prod P2) P3
    refine indep_of_indep_of_le_right (indep_of_indep_of_le_left hI ?_) ?_
    · rw [e3]; exact MeasurableSpace.comap_mono hN3.measurable.comap_le
    · rw [e1, e2]
      refine sup_le (sup_le bot_le (MeasurableSpace.comap_mono ?_)) (MeasurableSpace.comap_mono ?_)
      · exact (hNu.measurable.comp measurable_fst).comap_le
      · exact (hN2.measurable.comp measurable_snd).comap_le
  · intro A B hB hAB
    have h1 : (Prod.fst : (Ω × Ω2) × Ω3 → Ω × Ω2) ⁻¹' (A ×ˢ (univ : Set Ω2)) =
        (fun p : (Ω × Ω2) × Ω3 => p.1.1) ⁻¹' A := by ext p; simp
    have h2 := step78_measure_le_prod (μ := P.prod P2) (ν := P3) (A ×ˢ (univ : Set Ω2)) hB
      (by rw [h1]; exact hAB)
    rwa [Measure.prod_prod, measure_univ, mul_one] at h2

end ElboimSly.Paper.Step

end
