/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycRegenEnvGlue
public import ElboimSly.Foundations.PPP.Restriction
public import ElboimSly.Foundations.PPP.Operations
public import ElboimSly.Foundations.Interchange.GoodAs
public import Mathlib

/-!
# The constructions of the regenerated walk (i): Poisson environments on `ℕ × S_β`

The constructions of the regenerated walk (i). Let `N` be a `PPP(# ⊗ μ_β)` on `ℕ × S_β`. Its copies
`N^k = cycSlice k N` are `PPP(μ_β)` (restriction (a), images), independent
(restriction (b)), and almost surely good (configurations are a.s. good). Hence almost surely
the regenerated walk built from the copies `N^k` is `W_reg` of the environment final record of
`𝒫_reg`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

variable {d : ℕ} {β : ℝ} [Fact (0 < β)]

omit [Fact (0 < β)] in
/-- The slice `ν^k` is the restriction to `{k} × S_β` projected to `S_β`. -/
theorem cycSlice_eq_map_restrict (k : ℕ) (ν : Measure (ℕ × RingSpace d β)) :
    cycSlice k ν = (ν.restrict ({k} ×ˢ univ)).map Prod.snd := by
  ext A hA
  unfold cycSlice
  rw [(measurableEmbedding_prodMk_left k).comap_apply, Measure.map_apply measurable_snd hA,
    Measure.restrict_apply (measurable_snd hA)]
  congr 1
  ext ⟨a, x⟩
  simp only [mem_image, mem_inter_iff, mem_preimage, mem_prod, mem_singleton_iff, mem_univ,
    and_true, Prod.mk.injEq]
  constructor
  · rintro ⟨y, hy, rfl, rfl⟩
    exact ⟨hy, rfl⟩
  · rintro ⟨hx, rfl⟩
    exact ⟨x, hx, rfl, rfl⟩

theorem slice_intensity (k : ℕ) :
    (((Measure.count : Measure ℕ).prod (ringIntensity d β)).restrict ({k} ×ˢ univ)).map
      Prod.snd = ringIntensity d β := by
  have : SFinite (ringIntensity d β) := by unfold ringIntensity; infer_instance
  ext A hA
  rw [Measure.map_apply measurable_snd hA, Measure.restrict_apply (measurable_snd hA)]
  have : Prod.snd ⁻¹' A ∩ ({k} ×ˢ univ : Set (ℕ × RingSpace d β)) = {k} ×ˢ A := by
    ext ⟨a, x⟩
    simp only [mem_inter_iff, mem_preimage, mem_prod, mem_singleton_iff, mem_univ, and_true]
    tauto
  rw [this, Measure.prod_prod, Measure.count_singleton, one_mul]

/-- The copies `N^k` of a `PPP(# ⊗ μ_β)` are `PPP(μ_β)`. Restriction (a),
Images. -/
theorem isPoissonPointProcess_slice {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {N : Ω → Measure (ℕ × RingSpace d β)}
    (hN : IsPoissonPointProcess N ((Measure.count : Measure ℕ).prod (ringIntensity d β)) P)
    (k : ℕ) : IsPoissonPointProcess (fun ω => cycSlice k (N ω)) (ringIntensity d β) P := by
  have h := (hN.restrict (A := {k} ×ˢ univ)
    ((measurableSet_singleton k).prod MeasurableSet.univ)).map_measure
    (measurable_snd : Measurable (Prod.snd : ℕ × RingSpace d β → RingSpace d β))
  rw [slice_intensity] at h
  simpa only [cycSlice_eq_map_restrict] using h

/-- The copies `N^k` are independent. Restriction (b). -/
theorem iIndepFun_slice {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {N : Ω → Measure (ℕ × RingSpace d β)}
    (hN : IsPoissonPointProcess N ((Measure.count : Measure ℕ).prod (ringIntensity d β)) P) :
    iIndepFun (fun k ω => cycSlice k (N ω)) P := by
  have h := hN.iIndepFun_restrict (A := fun k : ℕ => ({k} ×ˢ univ : Set (ℕ × RingSpace d β)))
    (fun k => (measurableSet_singleton k).prod MeasurableSet.univ)
    (fun i j hij => by
      simp only [Function.onFun]
      rw [Set.disjoint_left]
      rintro ⟨a, x⟩ ha hb
      simp only [mem_prod, mem_singleton_iff] at ha hb
      exact hij (ha.1.symm.trans hb.1))
  have := h.comp (fun _ ν => ν.map Prod.snd) (fun _ => measurable_map_measure measurable_snd)
  simpa only [Function.comp_def, cycSlice_eq_map_restrict] using this

/-- A `PPP(# ⊗ μ_β)` is almost surely good in every copy. Configurations are a.s. good. -/
theorem ae_cycGood {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {N : Ω → Measure (ℕ × RingSpace d β)}
    (hN : IsPoissonPointProcess N ((Measure.count : Measure ℕ).prod (ringIntensity d β)) P) :
    ∀ᵐ ω ∂P, CycGood (N ω) :=
  ae_all_iff.2 fun k => Interchange.ae_good (isPoissonPointProcess_slice hN k)

/-- **the constructions of the regenerated walk (i)**, almost surely: the regenerated walk built from the copies
`N^k` of a `PPP(# ⊗ μ_β)` on `ℕ × S_β` is `W_reg` of the environment final record of `𝒫_reg`. -/
theorem ae_regRecWalk_envFinal {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {N : Ω → Measure (ℕ × RingSpace d β)}
    (hN : IsPoissonPointProcess N ((Measure.count : Measure ℕ).prod (ringIntensity d β)) P) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, regRecWalk ((regPlan d β).envFinal (N ω)) t =
      ElboimSly.regenWalk (fun k => cycSlice k (N ω)) (t : ℝ) := by
  filter_upwards [ae_cycGood hN] with ω hω t
  exact regRecWalk_envFinal_eq_regenWalk hω t

end ElboimSly.Cyclic

end
