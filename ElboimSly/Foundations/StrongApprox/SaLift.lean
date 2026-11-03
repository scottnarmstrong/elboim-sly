/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import Mathlib

/-!
# Lifting a coupling through a countably-valued map

Lifting a coupling through a countably-valued map.

Let `Ξ : E' → S` be measurable with values in a countable set `C`, and let `Γ` be a probability
measure on `S × F` whose first marginal is `Ξ_* ν'`.  Then there is a probability measure `Γh` on
`E' × F` with first marginal `ν'` whose image under `(e, f) ↦ (Ξ e, f)` is `Γ`.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace ElboimSly
namespace StrongApprox

variable {E' S F : Type*} [MeasurableSpace E'] [MeasurableSpace S] [MeasurableSingletonClass S]
  [MeasurableSpace F]

/-- The measure `Γh = ∑_{x ∈ C} κ_x ⊗ Γ_x` of the proof of lifting a coupling through a countably-valued map. -/
noncomputable def liftMeasure (ν' : Measure E') (C : Set S) (Ξ : E' → S) (Γ : Measure (S × F)) :
    Measure (E' × F) :=
  Measure.sum fun x : C =>
    (ν' (Ξ ⁻¹' {(x : S)}))⁻¹ •
      (ν'.restrict (Ξ ⁻¹' {(x : S)})).prod ((Γ.restrict (({(x : S)} : Set S) ×ˢ univ)).map Prod.snd)

section

variable {ν' : Measure E'} [IsProbabilityMeasure ν'] {C : Set S} {Ξ : E' → S}
  {Γ : Measure (S × F)} [IsFiniteMeasure Γ]

omit [IsProbabilityMeasure ν'] [IsFiniteMeasure Γ] in
theorem liftMeasure_fiber_mass (hΞ : Measurable Ξ) (hfst : Γ.map Prod.fst = ν'.map Ξ) (x : S) :
    Γ (({x} : Set S) ×ˢ univ) = ν' (Ξ ⁻¹' {x}) := by
  have h := congrArg (fun m => m {x}) hfst
  rw [Measure.map_apply measurable_fst (measurableSet_singleton x),
    Measure.map_apply hΞ (measurableSet_singleton x)] at h
  rw [← h]; congr 1; ext p; simp

omit [MeasurableSingletonClass S] [IsFiniteMeasure Γ] in
theorem liftPx_apply (x : S) {V : Set F} (hV : MeasurableSet V) :
    (Γ.restrict (({x} : Set S) ×ˢ univ)).map Prod.snd V = Γ (({x} : Set S) ×ˢ V) := by
  rw [Measure.map_apply measurable_snd hV,
    Measure.restrict_apply (measurable_snd hV)]
  congr 1; ext p; simp [and_comm]

omit [MeasurableSingletonClass S] [IsFiniteMeasure Γ] in
theorem liftPx_univ (x : S) :
    (Γ.restrict (({x} : Set S) ×ˢ univ)).map Prod.snd univ = Γ (({x} : Set S) ×ˢ univ) := by
  rw [liftPx_apply x MeasurableSet.univ]

theorem inv_mul_cancel_aux {a b : ℝ≥0∞} (h : a = 0 → b = 0) (_hb : b ≤ a) (ha : a ≠ ⊤) :
    a⁻¹ * b * a = b := by
  by_cases h0 : a = 0
  · rw [h h0]; simp
  · rw [mul_comm, ← mul_assoc, ENNReal.mul_inv_cancel h0 ha, one_mul]

/-- (a): the first marginal of `Γh` is `ν'`. -/
theorem liftMeasure_map_fst (hC : C.Countable) (hΞ : Measurable Ξ) (hrange : ∀ e, Ξ e ∈ C)
    (hfst : Γ.map Prod.fst = ν'.map Ξ) : (liftMeasure ν' C Ξ Γ).map Prod.fst = ν' := by
  have : Countable C := hC.to_subtype
  refine Measure.ext fun A hA => ?_
  rw [Measure.map_apply measurable_fst hA, liftMeasure,
    Measure.sum_apply _ (measurable_fst hA)]
  have hterm : ∀ x : C, ((ν' (Ξ ⁻¹' {(x : S)}))⁻¹ •
      (ν'.restrict (Ξ ⁻¹' {(x : S)})).prod ((Γ.restrict (({(x : S)} : Set S) ×ˢ univ)).map
        Prod.snd)) (Prod.fst ⁻¹' A) = (ν'.restrict A) (Ξ ⁻¹' {(x : S)}) := by
    intro x
    have hAx : MeasurableSet (Ξ ⁻¹' {(x : S)}) := hΞ (measurableSet_singleton _)
    have hpre : (Prod.fst ⁻¹' A : Set (E' × F)) = A ×ˢ univ := by ext; simp
    rw [Measure.smul_apply, hpre, Measure.prod_prod, liftPx_univ,
      liftMeasure_fiber_mass hΞ hfst, Measure.restrict_apply hA, Measure.restrict_apply hAx,
      smul_eq_mul]
    have key := inv_mul_cancel_aux (a := ν' (Ξ ⁻¹' {(x : S)})) (b := ν' (Ξ ⁻¹' {(x : S)} ∩ A))
      (fun h0 => measure_mono_null Set.inter_subset_left h0) (measure_mono Set.inter_subset_left)
      (measure_ne_top _ _)
    rw [Set.inter_comm A]
    refine Eq.trans ?_ key; ring
  simp_rw [hterm]
  rw [tsum_measure_preimage_singleton hC (fun y _ => hΞ (measurableSet_singleton y))]
  have : Ξ ⁻¹' C = univ := eq_univ_of_forall hrange
  rw [this, Measure.restrict_apply_univ]

/-- (b): the image of `Γh` under `(e, f) ↦ (Ξ e, f)` is `Γ`. -/
theorem liftMeasure_map_Ξ (hC : C.Countable) (hΞ : Measurable Ξ) (hrange : ∀ e, Ξ e ∈ C)
    (hfst : Γ.map Prod.fst = ν'.map Ξ) [IsProbabilityMeasure Γ] :
    (liftMeasure ν' C Ξ Γ).map (fun p : E' × F => (Ξ p.1, p.2)) = Γ := by
  have : Countable C := hC.to_subtype
  have hΦ : Measurable fun p : E' × F => (Ξ p.1, p.2) := (hΞ.comp measurable_fst).prodMk measurable_snd
  refine Measure.ext fun U hU => ?_
  rw [Measure.map_apply hΦ hU, liftMeasure, Measure.sum_apply _ (hΦ hU)]
  have hterm : ∀ x : C, ((ν' (Ξ ⁻¹' {(x : S)}))⁻¹ •
      (ν'.restrict (Ξ ⁻¹' {(x : S)})).prod ((Γ.restrict (({(x : S)} : Set S) ×ˢ univ)).map
        Prod.snd)) ((fun p : E' × F => (Ξ p.1, p.2)) ⁻¹' U) =
      (Γ.restrict U) (Prod.fst ⁻¹' {(x : S)}) := by
    intro x
    have hAx : MeasurableSet (Ξ ⁻¹' {(x : S)}) := hΞ (measurableSet_singleton _)
    have hUx : MeasurableSet (Prod.mk (x : S) ⁻¹' U) := measurable_prodMk_left hU
    rw [Measure.smul_apply, Measure.prod_apply (hΦ hU)]
    have hint : ∀ e ∈ Ξ ⁻¹' {(x : S)},
        (Γ.restrict (({(x : S)} : Set S) ×ˢ univ)).map Prod.snd
          (Prod.mk e ⁻¹' ((fun p : E' × F => (Ξ p.1, p.2)) ⁻¹' U)) =
        (Γ.restrict (({(x : S)} : Set S) ×ˢ univ)).map Prod.snd (Prod.mk (x : S) ⁻¹' U) := by
      intro e he
      have : Ξ e = x := he
      simp [Set.preimage, this]
    rw [setLIntegral_congr_fun hAx hint, lintegral_const, Measure.restrict_apply_univ,
      liftPx_apply _ hUx, smul_eq_mul,
      Measure.restrict_apply (measurable_fst (measurableSet_singleton _))]
    have hset : (({(x : S)} : Set S) ×ˢ (Prod.mk (x : S) ⁻¹' U)) =
        Prod.fst ⁻¹' {(x : S)} ∩ U := by
      ext p; obtain ⟨y, f⟩ := p
      simp only [mem_prod, mem_singleton_iff, mem_preimage, mem_inter_iff]
      constructor
      · rintro ⟨rfl, h⟩; exact ⟨rfl, h⟩
      · rintro ⟨rfl, h⟩; exact ⟨rfl, h⟩
    have hle : Γ (({(x : S)} : Set S) ×ˢ (Prod.mk (x : S) ⁻¹' U)) ≤ ν' (Ξ ⁻¹' {(x : S)}) := by
      rw [← liftMeasure_fiber_mass hΞ hfst]
      exact measure_mono (prod_mono subset_rfl (subset_univ _))
    have key := inv_mul_cancel_aux (a := ν' (Ξ ⁻¹' {(x : S)}))
      (b := Γ (({(x : S)} : Set S) ×ˢ (Prod.mk (x : S) ⁻¹' U)))
      (fun h0 => nonpos_iff_eq_zero.1 (h0 ▸ hle)) hle (measure_ne_top _ _)
    rw [← hset]
    refine Eq.trans ?_ key; ring
  simp_rw [hterm]
  rw [tsum_measure_preimage_singleton hC (fun y _ => measurable_fst (measurableSet_singleton y))]
  rw [Measure.restrict_apply (measurable_fst hC.measurableSet)]
  have hnull : Γ (Prod.fst ⁻¹' Cᶜ) = 0 := by
    rw [← Measure.map_apply measurable_fst hC.measurableSet.compl, hfst,
      Measure.map_apply hΞ hC.measurableSet.compl]
    have : Ξ ⁻¹' Cᶜ = ∅ := by
      ext e; simp [hrange e]
    rw [this, measure_empty]
  have : U ∩ Prod.fst ⁻¹' C = U \ Prod.fst ⁻¹' Cᶜ := by
    ext p; simp
  rw [inter_comm, this]
  exact measure_sdiff_null hnull

end

end StrongApprox
end ElboimSly
