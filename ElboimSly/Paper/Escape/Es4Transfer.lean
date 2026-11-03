/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Escape.C57Claim
public import ElboimSly.Foundations.PPP.Existence
public import Mathlib

/-!
# Product-space transfer for the `Es4Space` setting

ES22 Claim 5.7; The plan coupling, form used in S5 (c).

Independence facts for the product `Ω × Ω''` of a probability space with an independent
auxiliary space, used to adjoin an independent Poisson process `N''` to an `Es4Space`.
-/

@[expose] public section

set_option warn.classDefReducibility false

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Escape

open ElboimSly ElboimSly.Cyclic

section Indep


/-- The σ-algebra of sets that are `μ`-a.e. equal to a set of `𝒜`. -/
def aeSig {Ω : Type} (𝒜 : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] (μ : Measure Ω) :
    MeasurableSpace Ω where
  MeasurableSet' A := ∃ A', MeasurableSet[𝒜] A' ∧ A =ᵐ[μ] A'
  measurableSet_empty := ⟨∅, @MeasurableSet.empty _ 𝒜, Filter.EventuallyEq.refl _ _⟩
  measurableSet_compl := fun _ ⟨A', h1, h2⟩ => ⟨A'ᶜ, h1.compl, ae_eq_set_compl.2 (by simpa using h2)⟩
  measurableSet_iUnion := fun f h => by
    choose g hg1 hg2 using h
    exact ⟨⋃ i, g i, @MeasurableSet.iUnion _ _ 𝒜 _ _ hg1, Filter.EventuallyEqSet.countable_iUnion hg2⟩

theorem indep_sup_cycNull {Ω : Type} {ℬ 𝒜 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (h : Indep ℬ 𝒜 μ) : Indep ℬ (𝒜 ⊔ cycNull μ) μ := by
  have hle : 𝒜 ⊔ cycNull μ ≤ aeSig 𝒜 μ := by
    refine sup_le (fun A hA' => ⟨A, hA', Filter.EventuallyEq.refl _ _⟩) ?_
    refine MeasurableSpace.generateFrom_le fun A ⟨hAm, hA0⟩ => ?_
    exact ⟨∅, @MeasurableSet.empty _ 𝒜, ae_eq_empty.2 hA0⟩
  rw [Indep_iff] at h ⊢
  intro t1 t2 h1 h2
  obtain ⟨A', hA', hae⟩ := hle _ h2
  have e1 : μ t2 = μ A' := measure_congr hae
  have e2 : μ (t1 ∩ t2) = μ (t1 ∩ A') := measure_congr (Filter.EventuallyEqSet.inter
    (Filter.EventuallyEq.refl _ _) hae)
  rw [e2, e1, h t1 A' h1 hA']

theorem indep_comap_snd_fst {Ω Ω' : Type} [mΩ : MeasurableSpace Ω] [mΩ' : MeasurableSpace Ω']
    (μ : Measure Ω) (ν : Measure Ω') [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    Indep (mΩ'.comap Prod.snd) (mΩ.comap Prod.fst) (μ.prod ν) := by
  rw [Indep_iff]
  rintro _ _ ⟨B, hB, rfl⟩ ⟨A, hA, rfl⟩
  have : Prod.snd ⁻¹' B ∩ Prod.fst ⁻¹' A = A ×ˢ B := by ext; simp [and_comm]
  rw [this, Measure.prod_prod]
  have e1 : (μ.prod ν) (Prod.snd ⁻¹' B) = ν B := by
    rw [← Measure.map_apply measurable_snd hB, Measure.map_snd_prod]; simp
  have e2 : (μ.prod ν) (Prod.fst ⁻¹' A) = μ A := by
    rw [← Measure.map_apply measurable_fst hA, Measure.map_fst_prod]; simp
  rw [e1, e2, mul_comm]

theorem indep_comap_fst {Ω Ω' : Type} {m1 m2 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    [mΩ' : MeasurableSpace Ω'] (μ : Measure Ω) (ν : Measure Ω') [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (h1 : m1 ≤ mΩ) (h2 : m2 ≤ mΩ) (h : Indep m1 m2 μ) :
    Indep (m1.comap Prod.fst) (m2.comap Prod.fst) (μ.prod ν) := by
  rw [Indep_iff] at h ⊢
  rintro _ _ ⟨A, hA, rfl⟩ ⟨B, hB, rfl⟩
  have e : ∀ C : Set Ω, MeasurableSet C → (μ.prod ν) (Prod.fst ⁻¹' C) = μ C := fun C hC => by
    rw [← Measure.map_apply measurable_fst hC, Measure.map_fst_prod]; simp
  rw [← Set.preimage_inter, e _ ((h1 _ hA).inter (h2 _ hB)), e _ (h1 _ hA), e _ (h2 _ hB)]
  exact h A B hA hB

end Indep

variable {k : ℕ}

open ElboimSly.Brownian ElboimSly.Cyclic.CycSchemeEnv ElboimSly.Paper

/-- **ES22 Claim 5.7 on an `Es4Space`.**  The independent process `N''` of
The plan coupling, form used in S5 (c) is adjoined on a product space `Ω × Ω''`; the canonical version
`resPhi` of the conditional probability only depends on the law of `N`, so the bound transfers. -/
theorem es5_7_space (hd : 5 ≤ k + 2) :
    ∀ n₀ : ℕ, ∃ β₅₇ : ℝ, ∀ (β : ℝ) [Fact (0 < β)], β₅₇ ≤ β → ∀ (n : ℕ) (t₀ : ℝ),
      Es4Params (k + 2) β n₀ n t₀ → ∀ {Ω : Type} (𝒢₀ : MeasurableSpace Ω) [_mΩ : MeasurableSpace Ω]
        {Pr : Measure Ω} {N N' : Ω → Measure (CycS ℕ (k + 2) β)},
        Es4Space (k + 2) β 𝒢₀ Pr N N' → ∀ (tn : ℝ) (u : EscV k) (β' i : ℕ)
        (hlog : 1 < Real.log β), 1 ≤ i → i ≤ escIstar n (escJ n) →
        ∀ {S : ℝ≥0}, (S : ℝ) = ((2 : ℝ) ^ escJ n) ^ 2 / 4 →
        ∀ᵐ ω ∂Pr, ENNReal.ofReal (c57 (k + 2) / 2) ≤ resPhi (plan5 n β tn u β' i hlog) Pr N
          (lamT (plan5 n β tn u β' i hlog) N (escIstar n (escJ n) + 1))
          (exitSet (β := β) (escJ n) u S
            (((0 : ℕ), escPoint n (escJ n) u i, (β' : ℝ), false) : CycData ℕ (k + 2))) ω := by
  intro n₀
  obtain ⟨b, hb⟩ := es5_7 hd n₀
  refine ⟨b, fun β _ hβ n t₀ hp Ω 𝒢₀ mΩ Pr N N' hsp tn u β' i hlog hi1 hiI S hS => ?_⟩
  have hPr : IsProbabilityMeasure Pr := hsp.ppp.isProbabilityMeasure
  obtain ⟨Ω2, m2, P2, N2, hP2, hN2, -⟩ :=
    exists_isPoissonPointProcess ((Measure.count : Measure ℕ).prod (ringIntensity (k + 2) β))
  have := hP2
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
        MeasurableSpace.comap (N' ∘ Prod.fst) inferInstance ⊔ cycNull (Pr.prod P2)) (Pr.prod P2) := by
    refine indep_sup_cycNull ?_
    have hI := indep_comap_snd_fst Pr P2
    refine indep_of_indep_of_le_right (indep_of_indep_of_le_left hI ?_) ?_
    · rw [cN2]; exact MeasurableSpace.comap_mono hN2.measurable.comap_le
    · rw [cN, cN']
      exact sup_le (sup_le (MeasurableSpace.comap_mono hle0) (MeasurableSpace.comap_mono hle1))
        (MeasurableSpace.comap_mono hle2)
  have hle : 𝒢₀.comap (Prod.fst : Ω × Ω2 → Ω) ≤ (inferInstance : MeasurableSpace (Ω × Ω2)) :=
    (MeasurableSpace.comap_mono hle0).trans measurable_fst.comap_le
  have h := hb β hβ n t₀ hp (𝒢₀.comap (Prod.fst : Ω × Ω2 → Ω)) h1 h1' h2 I1 I2 I3 hle tn u β' i
    hlog hi1 hiI hS
  have key : ∀ p : Ω × Ω2, resPhi (plan5 n β tn u β' i hlog) (Pr.prod P2) (N ∘ Prod.fst)
      (lamT (plan5 n β tn u β' i hlog) (N ∘ Prod.fst) (escIstar n (escJ n) + 1))
      (exitSet (β := β) (escJ n) u S
        (((0 : ℕ), escPoint n (escJ n) u i, (β' : ℝ), false) : CycData ℕ (k + 2))) p =
      resPhi (plan5 n β tn u β' i hlog) Pr N
      (lamT (plan5 n β tn u β' i hlog) N (escIstar n (escJ n) + 1))
      (exitSet (β := β) (escJ n) u S
        (((0 : ℕ), escPoint n (escJ n) u i, (β' : ℝ), false) : CycData ℕ (k + 2))) p.1 := by
    intro p
    unfold resPhi
    rw [hmN]
    rfl
  filter_upwards [Measure.ae_ae_of_ae_prod h] with ω hω
  obtain ⟨y, hy⟩ := hω.exists
  rwa [key (ω, y)] at hy

end ElboimSly.Paper.Escape
