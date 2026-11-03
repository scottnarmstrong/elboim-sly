/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycMultiDef
public import ElboimSly.Foundations.Cyclic.CycSchemeEnvMain
public import ElboimSly.Foundations.PPP.Exploration.ExplRunOf
public import Mathlib

/-!
# Several walks explored one after another (a), Step 1: the exploration run

Several walks explored one after another (a), Step 1. Given `𝒢₀`, `N`, `N'` with `𝒢₀`, `σ(N)`, `σ(N')`
independent, `multiRun` is the run of the environment scheme of `P` with global horizon `s_∘` and
auxiliary variable `U` the identity `(Ω, 𝒜) → (Ω, 𝒢₀)`. Its `𝒢_κ`-measurable sets contain
`𝒢₀` (`inGkappa_u`) and are closed under intersection (`inGkappa_inter`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

variable {I : Type*} [MeasurableSpace I] [Countable I] [MeasurableSingletonClass I] {d : ℕ}
  {β : ℝ} [Fact (0 < β)]
  {Ω : Type*} (𝒢₀ : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] {Pr : Measure Ω}

omit [Countable I] [MeasurableSingletonClass I] [Fact (0 < β)] in
theorem indepFun_gspace {N : Ω → Measure (CycS I d β)}
    (hI1 : Indep 𝒢₀ (MeasurableSpace.comap N inferInstance) Pr) :
    IndepFun (GSpace.mk 𝒢₀) N Pr := by
  rw [IndepFun_iff_Indep]
  have : MeasurableSpace.comap (GSpace.mk 𝒢₀) (GSpace.instMeasurableSpace 𝒢₀) = 𝒢₀ :=
    MeasurableSpace.comap_id
  rw [this]; exact hI1

omit [Countable I] [MeasurableSingletonClass I] [Fact (0 < β)] in
theorem indepFun_gspace_pair {N N' : Ω → Measure (CycS I d β)}
    (hI2 : Indep (MeasurableSpace.comap N' inferInstance)
      (𝒢₀ ⊔ MeasurableSpace.comap N inferInstance) Pr) :
    IndepFun N' (fun ω => (GSpace.mk 𝒢₀ ω, N ω)) Pr := by
  rw [IndepFun_iff_Indep]
  have : MeasurableSpace.comap (fun ω => (GSpace.mk 𝒢₀ ω, N ω)) inferInstance =
      𝒢₀ ⊔ MeasurableSpace.comap N inferInstance := by
    have h := MeasurableSpace.comap_prodMk (mβ := GSpace.instMeasurableSpace 𝒢₀)
      (mγ := (inferInstance : MeasurableSpace (Measure (CycS I d β)))) (GSpace.mk 𝒢₀) N
    have h0 : MeasurableSpace.comap (GSpace.mk 𝒢₀) (GSpace.instMeasurableSpace 𝒢₀) = 𝒢₀ :=
      MeasurableSpace.comap_id
    rw [h0] at h
    exact h
  rw [this]; exact hI2

theorem measurable_gspace_mk (h𝒢 : 𝒢₀ ≤ mΩ) : Measurable (GSpace.mk 𝒢₀) :=
  fun _ hs => h𝒢 _ hs

/-- The run of the environment scheme of `P` with global horizon `sc`, for the auxiliary variable
`U = id : (Ω, 𝒜) → (Ω, 𝒢₀)`, driven by the Poisson point processes `N` and `N'`. -/
noncomputable def multiRun (P : CycPlan I d β) (sc : ℝ≥0∞) (h𝒢 : 𝒢₀ ≤ mΩ)
    {N N' : Ω → Measure (CycS I d β)} (hN : IsPoissonPointProcess N (cycIntensity I d β) Pr)
    (hN' : IsPoissonPointProcess N' (cycIntensity I d β) Pr)
    (hI1 : Indep 𝒢₀ (MeasurableSpace.comap N inferInstance) Pr)
    (hI2 : Indep (MeasurableSpace.comap N' inferInstance)
      (𝒢₀ ⊔ MeasurableSpace.comap N inferInstance) Pr) :
    ExplRun (cycScheme P sc (GSpace 𝒢₀)) Pr :=
  ExplRun.ofPPP (cycScheme P sc (GSpace 𝒢₀)) (measurable_gspace_mk 𝒢₀ h𝒢) hN
    (indepFun_gspace 𝒢₀ hI1) hN' (indepFun_gspace_pair 𝒢₀ hI2)

section gkappa

variable {S : Type*} [MeasurableSpace S] {U : Type*} [MeasurableSpace U] {μ : Measure S}
  [SigmaFinite μ] {sch : ExplScheme μ U} {Pr' : Measure Ω} (run : ExplRun sch Pr')

theorem inGkappa_inter {κ : Ω → ℕ∞} {G₁ G₂ : Set Ω} (h₁ : run.InGkappa κ G₁)
    (h₂ : run.InGkappa κ G₂) : run.InGkappa κ (G₁ ∩ G₂) := by
  obtain ⟨hk₁, A₁, hA₁, hA₁e⟩ := h₁
  obtain ⟨hk₂, A₂, hA₂, hA₂e⟩ := h₂
  refine ⟨fun k => ?_, A₁ ∩ A₂, hA₁.inter hA₂, ?_⟩
  · obtain ⟨B₁, hB₁, e₁⟩ := hk₁ k
    obtain ⟨B₂, hB₂, e₂⟩ := hk₂ k
    refine ⟨B₁ ∩ B₂, hB₁.inter hB₂, ?_⟩
    have : G₁ ∩ G₂ ∩ {ω | κ ω = k} = (G₁ ∩ {ω | κ ω = k}) ∩ (G₂ ∩ {ω | κ ω = k}) := by
      ext ω; simp only [mem_inter_iff, mem_ofPred_eq]; tauto
    rw [this, e₁, e₂]; rfl
  · have : G₁ ∩ G₂ ∩ {ω | κ ω = ⊤} = (G₁ ∩ {ω | κ ω = ⊤}) ∩ (G₂ ∩ {ω | κ ω = ⊤}) := by
      ext ω; simp only [mem_inter_iff, mem_ofPred_eq]; tauto
    rw [this, hA₁e, hA₂e]; rfl

theorem inGkappa_u {κ : Ω → ℕ∞} (hκ : run.IsStopping κ) {A : Set U} (hA : MeasurableSet A) :
    run.InGkappa κ (run.u ⁻¹' A) := by
  obtain ⟨Ainf, hAinf, hAeq⟩ := hκ.top
  refine ⟨fun k => ?_, Prod.fst ⁻¹' A ∩ Ainf, (measurable_fst hA).inter hAinf, ?_⟩
  · obtain ⟨B, hB, hBe⟩ := hκ k
    refine ⟨Prod.fst ⁻¹' A ∩ B, (measurable_fst hA).inter hB, ?_⟩
    have hfst : ∀ ω, (run.H k ω).1 = run.u ω := fun ω => sch.Hfun_fst k (run.X ω)
    ext ω
    simp only [mem_inter_iff, mem_preimage, mem_ofPred_eq]
    have : ω ∈ {ω | κ ω = k} ↔ run.H k ω ∈ B := by
      rw [hBe]; rfl
    rw [hfst ω]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, this.1 h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, this.2 h2⟩
  · ext ω
    simp only [mem_inter_iff, mem_preimage, mem_ofPred_eq]
    have : ω ∈ {ω | κ ω = ⊤} ↔ run.Hinf ω ∈ Ainf := by
      rw [hAeq]; rfl
    have hfst : (run.Hinf ω).1 = run.u ω := rfl
    rw [hfst]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, this.1 h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, this.2 h2⟩

end gkappa

end ElboimSly.Cyclic

end
