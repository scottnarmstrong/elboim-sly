/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CPathStop
public import ElboimSly.Foundations.Cyclic.CPathJump
public import ElboimSly.Foundations.SRW.Stopping
public import Mathlib

/-!
# Several walks explored one after another (a), Step 3: the dyadic approximation (abstract form)

Several walks explored one after another (a), Step 3. Let `M t` be a family of random measures such
that, for each fixed `t`, `M t` has the law `Π` and is independent of `ℱ_t`. Let `T` be an
everywhere finite `(ℱ_t)`-stopping time, `τ` its real value and `T_m = ⌈2^m τ⌉ 2^{-m}`.

* `dyadic_discrete`: `M (T_m)` has the law `Π` and is independent of `ℱ_T`;
* `dyadic_indep`: if for a `π`-system `𝒞` generating the `σ`-algebra of the target, almost surely
  `M (T_m) ∈ F ↔ M (τ) ∈ F` eventually for all `F ∈ 𝒞`, then `M τ` has the law `Π` and is
  independent of `ℱ_T`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {S : Type*} [MeasurableSpace S]
  {f : Filtration ℝ≥0 mΩ} {T : Ω → WithTop ℝ≥0}

theorem stopReal_measurable (hT : IsStoppingTime f T) :
    Measurable (ElboimSly.SRW.stopReal T) :=
  (measurable_stopReal_stop hT).mono hT.measurableSpace_le le_rfl

theorem measurableSet_inter_stopReal_le (hT : IsStoppingTime f T) (hfin : ∀ ω, T ω ≠ ⊤)
    {A : Set Ω} (hA : MeasurableSet[hT.measurableSpace] A) (c : ℝ≥0) :
    MeasurableSet[f c] (A ∩ {ω | ElboimSly.SRW.stopReal T ω ≤ c}) := by
  have h := hA.2 c
  convert h using 2
  ext ω
  simp only [mem_ofPred_eq]
  obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.1 (hfin ω)
  simp only [ElboimSly.SRW.stopReal, ← ha]
  rw [WithTop.untopD_coe]
  exact WithTop.coe_le_coe.symm

/-- `M (T_m)` is independent of `ℱ_T` with law `Π`. -/
theorem dyadic_discrete (Pr : Measure Ω) [IsProbabilityMeasure Pr]
    (M : ℝ≥0 → Ω → Measure S) (Pi : Measure (Measure S))
    (hMmeas : ∀ g : Ω → ℝ≥0, Measurable g → Measurable fun ω => M (g ω) ω)
    (hstep : ∀ t, ∀ A, MeasurableSet[f t] A → ∀ F : Set (Measure S), MeasurableSet F →
      Pr (A ∩ {ω | M t ω ∈ F}) = Pr A * Pi F)
    (hT : IsStoppingTime f T) (hfin : ∀ ω, T ω ≠ ⊤)
    {A : Set Ω} (hA : MeasurableSet[hT.measurableSpace] A) (m : ℕ)
    {F : Set (Measure S)} (hF : MeasurableSet F) :
    Pr (A ∩ {ω | M (dyUp m (ElboimSly.SRW.stopReal T ω)) ω ∈ F}) = Pr A * Pi F := by
  set τ := ElboimSly.SRW.stopReal T with hτ
  have hτm : Measurable τ := stopReal_measurable hT
  have hAm : MeasurableSet A := hT.measurableSpace_le _ hA
  -- the level sets of the ceiling
  let E : ℕ → Set Ω := fun k => {ω | ⌈τ ω * 2 ^ m⌉₊ = k}
  have hEm : ∀ k, MeasurableSet (E k) := fun k =>
    (Nat.measurable_ceil.comp (hτm.mul_const _)) (measurableSet_singleton k)
  have hEd : Pairwise (Function.onFun Disjoint E) := fun i j hij =>
    Set.disjoint_left.2 fun ω hi hj => hij (hi.symm.trans hj)
  have hEu : (⋃ k, E k) = univ := by
    ext ω; simp [E]
  -- `A ∩ E k ∈ ℱ_{k / 2^m}`
  have hG : ∀ j : ℕ, MeasurableSet[f ((j : ℝ≥0) / 2 ^ m)]
      (A ∩ {ω | ⌈τ ω * 2 ^ m⌉₊ ≤ j}) := by
    intro j
    convert measurableSet_inter_stopReal_le hT hfin hA ((j : ℝ≥0) / 2 ^ m) using 2
    ext ω
    simp only [mem_ofPred_eq, hτ]
    rw [Nat.ceil_le, le_div_iff₀ (by positivity)]
  have hAE : ∀ k : ℕ, MeasurableSet[f ((k : ℝ≥0) / 2 ^ m)] (A ∩ E k) := by
    intro k
    rcases k with _ | k
    · convert hG 0 using 2
      ext ω; simp [E]
    · have h1 := hG (k + 1)
      have h2 : MeasurableSet[f (((k + 1 : ℕ) : ℝ≥0) / 2 ^ m)]
          (A ∩ {ω | ⌈τ ω * 2 ^ m⌉₊ ≤ k}) :=
        f.mono (div_le_div_of_nonneg_right (by exact_mod_cast Nat.le_succ k) (by positivity)) _ (hG k)
      convert h1.diff h2 using 1
      ext ω
      simp only [E, mem_inter_iff, mem_ofPred_eq, Set.mem_sdiff, not_and, not_le]
      constructor
      · rintro ⟨ha, hk⟩; exact ⟨⟨ha, hk.le⟩, fun _ => by omega⟩
      · rintro ⟨⟨ha, hk⟩, h⟩; exact ⟨ha, le_antisymm hk (by have := h ha; omega)⟩
  have hset : A ∩ {ω | M (dyUp m (τ ω)) ω ∈ F} =
      ⋃ k : ℕ, (A ∩ E k) ∩ {ω | M ((k : ℝ≥0) / 2 ^ m) ω ∈ F} := by
    ext ω
    simp only [mem_inter_iff, mem_ofPred_eq, mem_iUnion, E]
    constructor
    · rintro ⟨ha, hM⟩
      exact ⟨_, ⟨ha, rfl⟩, hM⟩
    · rintro ⟨k, ⟨ha, hk⟩, hM⟩
      refine ⟨ha, ?_⟩
      unfold dyUp
      rw [hk]; exact hM
  have hMm : ∀ t : ℝ≥0, MeasurableSet {ω | M t ω ∈ F} := fun t =>
    (hMmeas (fun _ => t) measurable_const) hF
  rw [hset, measure_iUnion]
  · calc ∑' k, Pr ((A ∩ E k) ∩ {ω | M ((k : ℝ≥0) / 2 ^ m) ω ∈ F})
        = ∑' k, Pr (A ∩ E k) * Pi F := tsum_congr fun k => hstep _ _ (hAE k) F hF
      _ = Pr A * Pi F := by
        rw [ENNReal.tsum_mul_right, ← measure_iUnion]
        · rw [← inter_iUnion, hEu, inter_univ]
        · exact fun i j hij => (hEd hij).mono inter_subset_right inter_subset_right
        · exact fun k => hAm.inter (hEm k)
  · exact fun i j hij => Set.disjoint_left.2 fun ω hi hj =>
      (Set.disjoint_left.1 (hEd hij)) hi.1.2 hj.1.2
  · exact fun k => (hAm.inter (hEm k)).inter (hMm _)

theorem measurable_dyUp (m : ℕ) : Measurable (dyUp m) := by
  unfold dyUp
  exact (measurable_from_top.comp (Nat.measurable_ceil.comp (measurable_id.mul_const _))).div_const _

/-- Step 3 of the proof: `M τ` has the law `Π` and is independent of `ℱ_T`, if it is the limit of
the `M (T_m)` on a `π`-system generating the target `σ`-algebra. -/
theorem dyadic_indep (Pr : Measure Ω) [IsProbabilityMeasure Pr]
    (M : ℝ≥0 → Ω → Measure S) (Pi : Measure (Measure S)) (hPi : Pi univ = 1)
    (hMmeas : ∀ g : Ω → ℝ≥0, Measurable g → Measurable fun ω => M (g ω) ω)
    (hstep : ∀ t, ∀ A, MeasurableSet[f t] A → ∀ F : Set (Measure S), MeasurableSet F →
      Pr (A ∩ {ω | M t ω ∈ F}) = Pr A * Pi F)
    (𝒞 : Set (Set (Measure S)))
    (h𝒞 : (Measure.instMeasurableSpace : MeasurableSpace (Measure S)) = MeasurableSpace.generateFrom 𝒞)
    (hpi : IsPiSystem 𝒞)
    (hT : IsStoppingTime f T) (hfin : ∀ ω, T ω ≠ ⊤)
    (hlim : ∀ F ∈ 𝒞, ∀ᵐ ω ∂Pr, ∀ᶠ m in atTop,
      (M (dyUp m (ElboimSly.SRW.stopReal T ω)) ω ∈ F ↔
        M (ElboimSly.SRW.stopReal T ω) ω ∈ F))
    {A : Set Ω} (hA : MeasurableSet[hT.measurableSpace] A)
    {F : Set (Measure S)} (hF : MeasurableSet F) :
    Pr (A ∩ {ω | M (ElboimSly.SRW.stopReal T ω) ω ∈ F}) = Pr A * Pi F := by
  set τ := ElboimSly.SRW.stopReal T with hτ
  have hτm : Measurable τ := stopReal_measurable hT
  have hAm : MeasurableSet A := hT.measurableSpace_le _ hA
  have hMτ : Measurable fun ω => M (τ ω) ω := hMmeas τ hτm
  have hMm : ∀ m : ℕ, Measurable fun ω => M (dyUp m (τ ω)) ω := fun m =>
    hMmeas _ ((measurable_dyUp m).comp hτm)
  have key : ∀ F0 ∈ 𝒞, Pr (A ∩ {ω | M (τ ω) ω ∈ F0}) = Pr A * Pi F0 := by
    intro F0 hF0
    have hF0m : MeasurableSet F0 := by
      have := MeasurableSpace.measurableSet_generateFrom hF0
      rwa [← h𝒞] at this
    have : IsFiniteMeasure (Pr.restrict A) := inferInstance
    have ht := tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure (μ := Pr.restrict A)
      atTop (hMτ hF0m) (fun m => hMm m hF0m)
      (ae_restrict_of_ae (hlim F0 hF0))
    have hc : ∀ m, (Pr.restrict A) ((fun ω => M (dyUp m (τ ω)) ω) ⁻¹' F0) = Pr A * Pi F0 := fun m => by
      rw [Measure.restrict_apply (hMm m hF0m), inter_comm]
      exact dyadic_discrete Pr M Pi hMmeas hstep hT hfin hA m hF0m
    simp only [hc] at ht
    have := tendsto_nhds_unique ht tendsto_const_nhds
    rw [Measure.restrict_apply (hMτ hF0m), inter_comm] at this
    exact this
  have hext : (Pr.restrict A).map (fun ω => M (τ ω) ω) = Pr A • Pi := by
    refine ext_of_generate_finite 𝒞 h𝒞 hpi (fun F0 hF0 => ?_) ?_
    · rw [Measure.map_apply hMτ ((h𝒞 ▸ MeasurableSpace.measurableSet_generateFrom hF0)),
        Measure.restrict_apply (hMτ ((h𝒞 ▸ MeasurableSpace.measurableSet_generateFrom hF0))),
        inter_comm]
      exact key F0 hF0
    · rw [Measure.map_apply hMτ MeasurableSet.univ]
      simp [hPi]
  have := congrArg (fun ν => ν F) hext
  simp only [Measure.map_apply hMτ hF, Measure.restrict_apply (hMτ hF), Measure.smul_apply,
    smul_eq_mul] at this
  rw [inter_comm]
  exact this

end ElboimSly.Cyclic

end
