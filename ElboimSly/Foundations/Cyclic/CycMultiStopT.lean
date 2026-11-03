/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycMultiStop
public import Mathlib

/-!
# Several walks explored one after another (a), Step 5: arbitrary stopping times

Several walks explored one after another (a), Step 5 ("version on `{T < ∞}`"). For an arbitrary
`(ℱ^𝒫_s)`-stopping time `T` and `A ∈ ℱ^𝒫_T`,
`P(A ∩ {T < ∞} ∩ {Ñ_T ∈ F}) = P(A ∩ {T < ∞}) Π_μ(F)` (`multi_stopped`), where `Π_μ = Law(N)`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

variable {Ω : Type*} (𝒢₀ : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] {f : Filtration ℝ≥0 mΩ} {T : Ω → WithTop ℝ≥0}

omit 𝒢₀ in
/-- `{T < ∞} ∈ ℱ_T`. -/
theorem measurableSet_ne_top (hT : IsStoppingTime f T) :
    MeasurableSet[hT.measurableSpace] {ω | T ω ≠ ⊤} := by
  have h1 : {ω | T ω ≠ ⊤} = ⋃ n : ℕ, {ω | T ω ≤ ((n : ℝ≥0) : WithTop ℝ≥0)} := by
    ext ω
    simp only [mem_ofPred_eq, mem_iUnion]
    constructor
    · intro h
      obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.1 h
      obtain ⟨n, hn⟩ := exists_nat_ge a
      exact ⟨n, by rw [← ha]; exact_mod_cast hn⟩
    · rintro ⟨n, hn⟩
      exact ne_top_of_le_ne_top WithTop.coe_ne_top hn
  refine ⟨?_, fun i => ?_⟩
  · rw [h1]
    exact MeasurableSet.iUnion fun n => le_iSup f (n : ℝ≥0) _ (hT n)
  · have : {ω | T ω ≠ ⊤} ∩ {ω | T ω ≤ (i : WithTop ℝ≥0)} = {ω | T ω ≤ (i : WithTop ℝ≥0)} := by
      ext ω
      simp only [mem_inter_iff, mem_ofPred_eq, and_iff_right_iff_imp]
      exact fun h => ne_top_of_le_ne_top WithTop.coe_ne_top h
    rw [this]
    exact hT i

omit 𝒢₀ in
/-- `A ∩ {T ≤ n} ∈ ℱ_{T ∧ n}` for `A ∈ ℱ_T`. -/
theorem measurableSet_inter_le_min (hT : IsStoppingTime f T) {A : Set Ω}
    (hA : MeasurableSet[hT.measurableSpace] A) (n : ℝ≥0) :
    MeasurableSet[(hT.min_const n).measurableSpace] (A ∩ {ω | T ω ≤ (n : WithTop ℝ≥0)}) := by
  refine ⟨?_, fun i => ?_⟩
  · exact hA.1.inter (le_iSup f n _ (hT n))
  · by_cases hni : n ≤ i
    · have : (A ∩ {ω | T ω ≤ (n : WithTop ℝ≥0)}) ∩ {ω | min (T ω) (n : WithTop ℝ≥0) ≤ (i : WithTop ℝ≥0)} =
          A ∩ {ω | T ω ≤ (n : WithTop ℝ≥0)} := by
        ext ω
        simp only [mem_inter_iff, mem_ofPred_eq]
        constructor
        · rintro ⟨h, -⟩; exact h
        · rintro ⟨ha, hn⟩
          exact ⟨⟨ha, hn⟩, (min_le_right _ _).trans (by exact_mod_cast hni)⟩
      rw [this]
      exact f.mono hni _ (hA.2 n)
    · push Not at hni
      have : (A ∩ {ω | T ω ≤ (n : WithTop ℝ≥0)}) ∩ {ω | min (T ω) (n : WithTop ℝ≥0) ≤ (i : WithTop ℝ≥0)} =
          A ∩ {ω | T ω ≤ (i : WithTop ℝ≥0)} := by
        ext ω
        simp only [mem_inter_iff, mem_ofPred_eq]
        constructor
        · rintro ⟨⟨ha, hn⟩, hm⟩
          refine ⟨ha, ?_⟩
          rcases min_le_iff.1 hm with h | h
          · exact h
          · exact absurd (by exact_mod_cast h : n ≤ i) (not_le.2 hni)
        · rintro ⟨ha, hi⟩
          exact ⟨⟨ha, hi.trans (by exact_mod_cast hni.le)⟩, (min_le_left _ _).trans hi⟩
      rw [this]
      exact hA.2 i

variable {I : Type*} [MeasurableSpace I] [Countable I] [MeasurableSingletonClass I] {d : ℕ}
  {β : ℝ} [Fact (0 < β)] (P : CycPlan I d β)
  {Pr : Measure Ω}
  {N N' : Ω → Measure (CycS I d β)}
  (hN : IsPoissonPointProcess N (cycIntensity I d β) Pr)
  (hN' : IsPoissonPointProcess N' (cycIntensity I d β) Pr)
  (hI1 : Indep 𝒢₀ (MeasurableSpace.comap N inferInstance) Pr)
  (hI2 : Indep (MeasurableSpace.comap N' inferInstance)
    (𝒢₀ ⊔ MeasurableSpace.comap N inferInstance) Pr)

include hN hN' hI1 hI2 in
/-- Several walks explored one after another (a), Step 5 (version on `{T < ∞}`): for every
`(ℱ^𝒫_s)`-stopping time `T` and `A ∈ ℱ^𝒫_T`,
`P(A ∩ {T < ∞} ∩ {Ñ_T ∈ F}) = P(A ∩ {T < ∞}) Π_μ(F)`, where `Π_μ = Law(N)`. -/
theorem multi_stopped (hK : 0 < P.K) (h𝒢 : 𝒢₀ ≤ mΩ)
    (hR : Measurable fun ω => P.envFinal (N ω))
    (hT : IsStoppingTime (multiFilt 𝒢₀ P.junk Pr h𝒢 (fun ω => P.envFinal (N ω)) hR) T)
    {A : Set Ω} (hA : MeasurableSet[hT.measurableSpace] A)
    {F : Set (Measure (CycS I d β))} (hF : MeasurableSet F) :
    Pr (A ∩ {ω | T ω ≠ ⊤} ∩ {ω | tildeMeasure N N' (cycRegionStop P N T) ω ∈ F}) =
      Pr (A ∩ {ω | T ω ≠ ⊤}) * (Pr.map N) F := by
  set E : Set Ω := {ω | tildeMeasure N N' (cycRegionStop P N T) ω ∈ F} with hE
  have hn : ∀ n : ℕ, Pr (A ∩ {ω | T ω ≤ ((n : ℝ≥0) : WithTop ℝ≥0)} ∩ E) =
      Pr (A ∩ {ω | T ω ≤ ((n : ℝ≥0) : WithTop ℝ≥0)}) * (Pr.map N) F := by
    intro n
    have hfin : ∀ ω, (fun ω => min (T ω) ((n : ℝ≥0) : WithTop ℝ≥0)) ω ≠ ⊤ := fun ω =>
      ne_top_of_le_ne_top WithTop.coe_ne_top (min_le_right _ _)
    have := multi_stopped_fin P 𝒢₀ hN hN' hI1 hI2 hK h𝒢 hR (hT.min_const (n : ℝ≥0)) hfin
      (measurableSet_inter_le_min hT hA (n : ℝ≥0)) hF
    rw [← this]
    congr 1
    ext ω
    simp only [hE, mem_inter_iff, mem_ofPred_eq]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      have : cycRegionStop P N (fun ω => min (T ω) ((n : ℝ≥0) : WithTop ℝ≥0)) ω =
          cycRegionStop P N T ω := by
        unfold cycRegionStop
        beta_reduce
        rw [min_eq_left h1.2]
      unfold tildeMeasure at h2 ⊢
      rwa [← this] at h2
    · rintro ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      have : cycRegionStop P N (fun ω => min (T ω) ((n : ℝ≥0) : WithTop ℝ≥0)) ω =
          cycRegionStop P N T ω := by
        unfold cycRegionStop
        beta_reduce
        rw [min_eq_left h1.2]
      unfold tildeMeasure at h2 ⊢
      rwa [this] at h2
  have hmono : Monotone fun n : ℕ => A ∩ {ω | T ω ≤ ((n : ℝ≥0) : WithTop ℝ≥0)} :=
    fun a b hab ω ⟨h1, h2⟩ => ⟨h1, le_trans (show T ω ≤ _ from h2) (WithTop.coe_le_coe.2 (Nat.cast_le.2 hab))⟩
  have hU : (⋃ n : ℕ, A ∩ {ω | T ω ≤ ((n : ℝ≥0) : WithTop ℝ≥0)}) = A ∩ {ω | T ω ≠ ⊤} := by
    ext ω
    simp only [mem_iUnion, mem_inter_iff, mem_ofPred_eq]
    constructor
    · rintro ⟨n, h1, h2⟩; exact ⟨h1, ne_top_of_le_ne_top WithTop.coe_ne_top h2⟩
    · rintro ⟨h1, h2⟩
      obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.1 h2
      obtain ⟨n, hn⟩ := exists_nat_ge a
      exact ⟨n, h1, by rw [← ha]; exact_mod_cast hn⟩
  have hmono' : Monotone fun n : ℕ => A ∩ {ω | T ω ≤ ((n : ℝ≥0) : WithTop ℝ≥0)} ∩ E :=
    fun a b hab => inter_subset_inter_left _ (hmono hab)
  have hU' : (⋃ n : ℕ, A ∩ {ω | T ω ≤ ((n : ℝ≥0) : WithTop ℝ≥0)} ∩ E) =
      A ∩ {ω | T ω ≠ ⊤} ∩ E := by
    rw [← iUnion_inter, hU]
  rw [← hU', ← hU, hmono'.measure_iUnion, hmono.measure_iUnion]
  simp_rw [hn]
  rw [ENNReal.iSup_mul]

end ElboimSly.Cyclic

end
