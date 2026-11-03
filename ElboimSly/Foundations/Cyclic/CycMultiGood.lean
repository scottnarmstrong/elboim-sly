/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycMultiDef
public import ElboimSly.Foundations.Cyclic.CycPlanSanity
public import ElboimSly.Foundations.Cyclic.CycEnvMeas
public import ElboimSly.Foundations.Cyclic.CycSchemeEnvAe
public import ElboimSly.Foundations.PPP.Law
public import Mathlib

/-!
# Several walks explored one after another (a): the good modification of `N`

Natural filtration ("`N` given fixed values off `{N ∈ Good}`") and the first line of
the proof of several walks explored one after another (replace `N` by a version equal to it almost surely).

`ν ↦ ρ^𝒫(ν)` is measurable only on the good environments (`CycPlan.measurable_envFinal`). So we
set `cycNgood N ω := N ω` if `N ω` is good and `0` otherwise. This is always good, equal to `N`
almost surely (`ae_cycNgood_eq`), a PPP of the same intensity (`isPoissonPointProcess_cycNgood`),
and `P.envFinal ∘ cycNgood N` is measurable (`measurable_envFinal_cycNgood`). The remaining
lemmas transfer the independence hypotheses from `N` to `cycNgood N`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology MeasurableSpace
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

variable {I : Type*} [MeasurableSpace I] [Countable I] [MeasurableSingletonClass I] {d : ℕ}
  {β : ℝ} [Fact (0 < β)]
  {Ω : Type*} [mΩ : MeasurableSpace Ω] {Pr : Measure Ω}

omit [Countable I] [MeasurableSingletonClass I] in
omit [Fact (0 < β)] in
theorem cycGood_zero' : CycGood (0 : Measure (I × RingSpace d β)) := fun ι => by
  have : cycSlice ι (0 : Measure (I × RingSpace d β)) = 0 := by
    unfold cycSlice; exact Measure.comap_zero (Prod.mk ι)
  rw [this]; exact good_zero

open scoped Classical in
/-- `N` where it is good, and `0` elsewhere ("given fixed values off `{N ∈ Good}`"). -/
noncomputable def cycNgood (N : Ω → Measure (CycS I d β)) (ω : Ω) : Measure (CycS I d β) :=
  if CycGood (N ω) then N ω else 0

omit mΩ in
omit [Countable I] [MeasurableSingletonClass I] in
omit [Fact (0 < β)] in
theorem cycGood_cycNgood (N : Ω → Measure (CycS I d β)) (ω : Ω) : CycGood (cycNgood N ω) := by
  unfold cycNgood
  split_ifs with h
  · exact h
  · exact cycGood_zero'

theorem measurable_cycNgood {N : Ω → Measure (CycS I d β)} (hN : Measurable N) :
    Measurable (cycNgood N) := by
  classical
  have hs : MeasurableSet {ω | CycGood (N ω)} := hN measurableSet_cycGood
  exact Measurable.ite hs hN measurable_const

theorem ae_cycNgood_eq {N : Ω → Measure (CycS I d β)}
    (hN : IsPoissonPointProcess N (cycIntensity I d β) Pr) : cycNgood N =ᵐ[Pr] N := by
  filter_upwards [CycSchemeEnv.ae_cycGood' hN] with ω h
  simp [cycNgood, h]

theorem isPoissonPointProcess_cycNgood {N : Ω → Measure (CycS I d β)}
    (hN : IsPoissonPointProcess N (cycIntensity I d β) Pr) :
    IsPoissonPointProcess (cycNgood N) (cycIntensity I d β) Pr :=
  hN.of_ae_eq (measurable_cycNgood hN.measurable) (ae_cycNgood_eq hN)

/-- `ω ↦ ρ^𝒫(N^good(ω))` is measurable. -/
theorem measurable_envFinal_cycNgood (P : CycPlan I d β) {N : Ω → Measure (CycS I d β)}
    (hN : Measurable N) : Measurable fun ω => P.envFinal (cycNgood N ω) := by
  have h : Measurable fun ω => (⟨cycNgood N ω, cycGood_cycNgood N ω⟩ : CycGoodSet I d β) :=
    Measurable.subtype_mk (measurable_cycNgood hN)
  have h2 := P.measurable_envFinal.comp h
  exact h2

section indep

/-- The sets almost equal to a set of `X`, as a `σ`-algebra. -/
@[instance_reducible] def aeSets (Pr : Measure Ω) (X : MeasurableSpace Ω) : MeasurableSpace Ω where
  MeasurableSet' A := ∃ A', MeasurableSet[X] A' ∧ A =ᵐ[Pr] A'
  measurableSet_empty := ⟨∅, @MeasurableSet.empty _ X, Filter.EventuallyEq.rfl⟩
  measurableSet_compl := fun A ⟨A', h1, h2⟩ => ⟨A'ᶜ, @MeasurableSet.compl _ _ X h1, h2.compl⟩
  measurableSet_iUnion := fun f hf => by
    choose g hg1 hg2 using hf
    exact ⟨⋃ n, g n, @MeasurableSet.iUnion _ _ X _ _ hg1, Filter.EventuallyEqSet.countable_iUnion hg2⟩

theorem indep_of_ae_sets {m₁ m₂ m₃ : MeasurableSpace Ω} (h : Indep m₁ m₂ Pr)
    (h3 : ∀ A, MeasurableSet[m₃] A → ∃ A', MeasurableSet[m₂] A' ∧ A =ᵐ[Pr] A') :
    Indep m₁ m₃ Pr := by
  rw [Indep_iff] at h ⊢
  intro t1 t3 h1 h3'
  obtain ⟨t2, ht2, he⟩ := h3 t3 h3'
  rw [measure_congr (Filter.EventuallyEqSet.inter Filter.EventuallyEq.rfl he), measure_congr he]
  exact h t1 t2 h1 ht2

omit [Countable I] [MeasurableSingletonClass I] [Fact (0 < β)] in
theorem exists_ae_set_comap {N N₂ : Ω → Measure (CycS I d β)} (hae : N₂ =ᵐ[Pr] N)
    (𝒢₀ : MeasurableSpace Ω) :
    ∀ A, MeasurableSet[𝒢₀ ⊔ MeasurableSpace.comap N₂ inferInstance] A →
      ∃ A', MeasurableSet[𝒢₀ ⊔ MeasurableSpace.comap N inferInstance] A' ∧ A =ᵐ[Pr] A' := by
  have hle : 𝒢₀ ⊔ MeasurableSpace.comap N₂ inferInstance ≤
      @aeSets Ω mΩ Pr (𝒢₀ ⊔ MeasurableSpace.comap N inferInstance) := by
    have hl : 𝒢₀ ≤ 𝒢₀ ⊔ MeasurableSpace.comap N inferInstance := le_sup_left
    have hr : MeasurableSpace.comap N inferInstance ≤ 𝒢₀ ⊔ MeasurableSpace.comap N inferInstance :=
      le_sup_right
    refine sup_le (fun A hA => ⟨A, hl A hA, Filter.EventuallyEq.rfl⟩) ?_
    rintro A ⟨B, hB, rfl⟩
    refine ⟨N ⁻¹' B, hr _ ⟨B, hB, rfl⟩, ?_⟩
    exact Filter.eventuallyEqSet_iff.2 (hae.mono fun ω h => by simp [h])
  exact fun A hA => hle _ hA

omit [Countable I] [MeasurableSingletonClass I] [Fact (0 < β)] in
theorem exists_ae_set_comap' {N N₂ : Ω → Measure (CycS I d β)} (hae : N₂ =ᵐ[Pr] N) :
    ∀ A, MeasurableSet[MeasurableSpace.comap N₂ inferInstance] A →
      ∃ A', MeasurableSet[MeasurableSpace.comap N inferInstance] A' ∧ A =ᵐ[Pr] A' := by
  rintro A ⟨B, hB, rfl⟩
  exact ⟨N ⁻¹' B, ⟨B, hB, rfl⟩, Filter.eventuallyEqSet_iff.2 (hae.mono fun ω h => by simp [h])⟩

end indep

end ElboimSly.Cyclic

end
