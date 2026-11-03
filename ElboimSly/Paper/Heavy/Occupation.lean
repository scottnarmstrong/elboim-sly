/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Base.StepAux
public import ElboimSly.Paper.Heavy.CyclicPath
public import Mathlib

/-!
# Occupation before closing

Occupation before closing (ES22 §6).

For a cyclic path `w` with the no-return property and `t ≤ T(w)`, the time spent at any vertex
before `t` is at most `β`: `Leb {s ∈ [0,t) : w s = v} ≤ β`, hence
`Leb {s ∈ [0,t) : w s ∈ A} ≤ β |A|` for finite `A`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Paper

variable {d : ℕ}

/-- The level sets of a cyclic path, restricted to `[0, ∞)`, are measurable. -/
theorem IsCyclicPath.measurableSet_level {w : ℝ → Fin d → ℤ} (hw : IsCyclicPath w)
    (v : Fin d → ℤ) : MeasurableSet {s : ℝ | 0 ≤ s ∧ w s = v} := by
  have hrc : ∀ s : ℝ≥0, ∀ᶠ u in 𝓝[≥] s, (fun r : ℝ≥0 => w r) u = (fun r : ℝ≥0 => w r) s := by
    intro s
    have h := hw.rc (s : ℝ) s.2
    have ht : Tendsto (fun u : ℝ≥0 => (u : ℝ)) (𝓝[≥] s) (𝓝[≥] (s : ℝ)) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · exact (NNReal.continuous_coe.tendsto s).mono_left nhdsWithin_le_nhds
      · exact eventually_nhdsWithin_of_forall fun u hu => by exact_mod_cast hu
    exact ht.eventually h
  have hm : Measurable (fun r : ℝ≥0 => w r) := Base.measurable_of_rc hrc
  have : {s : ℝ | 0 ≤ s ∧ w s = v} =
      Ici (0 : ℝ) ∩ (fun s : ℝ => s.toNNReal) ⁻¹' ((fun r : ℝ≥0 => w r) ⁻¹' {v}) := by
    ext s
    simp only [mem_ofPred_eq, mem_inter_iff, mem_Ici, mem_preimage, mem_singleton_iff]
    constructor
    · rintro ⟨h0, h⟩
      exact ⟨h0, by simpa [Real.coe_toNNReal _ h0] using h⟩
    · rintro ⟨h0, h⟩
      exact ⟨h0, by simpa [Real.coe_toNNReal _ h0] using h⟩
  rw [this]
  exact measurableSet_Ici.inter (measurable_real_toNNReal (hm (measurableSet_singleton v)))

/-- Occupation before closing. For `t ≤ T(w)` and `v ∈ ℤ^d`,
`Leb {s ∈ [0,t) : w s = v} ≤ β`. -/
theorem volume_level_le {β : ℝ} (hβ : 0 < β) {w : ℝ → Fin d → ℤ} (hw : IsCyclicPath w)
    (hnr : HasNoReturn β w) {t : ℝ} (ht : ENNReal.ofReal t ≤ cycClosingTime β w)
    (v : Fin d → ℤ) : volume {s : ℝ | s ∈ Ico 0 t ∧ w s = v} ≤ ENNReal.ofReal β := by
  set O : Set ℝ := {s : ℝ | s ∈ Ico 0 t ∧ w s = v} with hO
  have hOm : MeasurableSet O := by
    have : O = {s : ℝ | 0 ≤ s ∧ w s = v} ∩ Iio t := by
      ext s; simp only [hO, mem_ofPred_eq, mem_Ico, mem_inter_iff, mem_Iio]; tauto
    rw [this]; exact (hw.measurableSet_level v).inter measurableSet_Iio
  -- pieces
  let P : ℕ → Set ℝ := fun ℓ => (fun u : ℝ => (ℓ : ℝ) * β + u) ⁻¹' O ∩ Ico 0 β
  have hPm : ∀ ℓ, MeasurableSet (P ℓ) := fun ℓ =>
    ((measurable_const_add _) hOm).inter measurableSet_Ico
  have hcover : O ⊆ ⋃ ℓ : ℕ, (O ∩ Ico ((ℓ : ℝ) * β) (((ℓ : ℝ) + 1) * β)) := by
    intro s hs
    have h0 : 0 ≤ s := hs.1.1
    refine mem_iUnion.2 ⟨⌊s / β⌋₊, hs, ?_, ?_⟩
    · have := Nat.floor_le (div_nonneg h0 hβ.le)
      calc (⌊s / β⌋₊ : ℝ) * β ≤ s / β * β := by gcongr
        _ = s := by field_simp
    · have := Nat.lt_floor_add_one (s / β)
      calc s = s / β * β := by field_simp
        _ < ((⌊s / β⌋₊ : ℝ) + 1) * β := by gcongr
  have hpiece : ∀ ℓ : ℕ, volume (O ∩ Ico ((ℓ : ℝ) * β) (((ℓ : ℝ) + 1) * β)) = volume (P ℓ) := by
    intro ℓ
    have : P ℓ = (fun u : ℝ => (ℓ : ℝ) * β + u) ⁻¹' (O ∩ Ico ((ℓ : ℝ) * β) (((ℓ : ℝ) + 1) * β)) := by
      ext u
      simp only [P, mem_inter_iff, mem_preimage, mem_Ico]
      constructor
      · rintro ⟨h1, h2, h3⟩
        refine ⟨h1, ?_, ?_⟩ <;> nlinarith
      · rintro ⟨h1, h2, h3⟩
        refine ⟨h1, ?_, ?_⟩ <;> nlinarith
    rw [this]
    exact (measure_preimage_add volume ((ℓ : ℝ) * β) _).symm
  have hdisj : Pairwise (Function.onFun Disjoint P) := by
    intro ℓ ℓ' hne
    wlog hlt : ℓ < ℓ' generalizing ℓ ℓ'
    · exact (this hne.symm (lt_of_le_of_ne (not_lt.1 hlt) hne.symm)).symm
    rw [Function.onFun, Set.disjoint_left]
    rintro u ⟨hu1, hu3⟩ ⟨hv1, hv3⟩
    have hu1 : (ℓ : ℝ) * β + u ∈ Ico 0 t ∧ w ((ℓ : ℝ) * β + u) = v := hu1
    have hv1 : (ℓ' : ℝ) * β + u ∈ Ico 0 t ∧ w ((ℓ' : ℝ) * β + u) = v := hv1
    have hs : (ℓ : ℝ) * β + u < t := hu1.1.2
    have hs' : (ℓ' : ℝ) * β + u < t := hv1.1.2
    have hlt' : (ℓ : ℝ) < ℓ' := by exact_mod_cast hlt
    have hlt2 : (ℓ : ℝ) * β + u < (ℓ' : ℝ) * β + u := by nlinarith
    refine hnr ((ℓ' : ℝ) * β + u) ((ℓ : ℝ) * β + u) (by have := hu3.1; positivity) hlt2 ?_
      ⟨(ℓ' : ℤ) - ℓ, by push_cast; ring⟩ (hv1.2.trans hu1.2.symm)
    have ht0 : 0 < t := by have := hu3.1; nlinarith [hu1.1.1]
    exact lt_of_lt_of_le ((ENNReal.ofReal_lt_ofReal_iff ht0).2 hs') ht
  calc volume O ≤ ∑' ℓ : ℕ, volume (O ∩ Ico ((ℓ : ℝ) * β) (((ℓ : ℝ) + 1) * β)) :=
        (measure_mono hcover).trans (measure_iUnion_le _)
    _ = ∑' ℓ : ℕ, volume (P ℓ) := by simp_rw [hpiece]
    _ = volume (⋃ ℓ, P ℓ) := (measure_iUnion hdisj hPm).symm
    _ ≤ volume (Ico (0 : ℝ) β) :=
        measure_mono (iUnion_subset fun ℓ => inter_subset_right)
    _ = ENNReal.ofReal β := by simp

/-- Occupation before closing, second sentence: for finite `A ⊆ ℤ^d`,
`Leb {s ∈ [0,t) : w s ∈ A} ≤ β |A|`. -/
theorem volume_mem_finite_le {β : ℝ} (hβ : 0 < β) {w : ℝ → Fin d → ℤ} (hw : IsCyclicPath w)
    (hnr : HasNoReturn β w) {t : ℝ} (ht : ENNReal.ofReal t ≤ cycClosingTime β w)
    {A : Set (Fin d → ℤ)} (hA : A.Finite) :
    volume {s : ℝ | s ∈ Ico 0 t ∧ w s ∈ A} ≤ (A.ncard : ℝ≥0∞) * ENNReal.ofReal β := by
  have hsub : {s : ℝ | s ∈ Ico 0 t ∧ w s ∈ A} ⊆
      ⋃ v ∈ hA.toFinset, {s : ℝ | s ∈ Ico 0 t ∧ w s = v} := by
    intro s hs
    simp only [mem_iUnion, Finite.mem_toFinset, mem_ofPred_eq]
    exact ⟨w s, hs.2, hs.1, rfl⟩
  calc volume {s : ℝ | s ∈ Ico 0 t ∧ w s ∈ A}
      ≤ volume (⋃ v ∈ hA.toFinset, {s : ℝ | s ∈ Ico 0 t ∧ w s = v}) := measure_mono hsub
    _ ≤ ∑ v ∈ hA.toFinset, volume {s : ℝ | s ∈ Ico 0 t ∧ w s = v} := measure_biUnion_finset_le _ _
    _ ≤ ∑ _v ∈ hA.toFinset, ENNReal.ofReal β :=
        Finset.sum_le_sum fun v _ => volume_level_le hβ hw hnr ht v
    _ = (A.ncard : ℝ≥0∞) * ENNReal.ofReal β := by
        rw [Finset.sum_const, nsmul_eq_mul, Set.ncard_eq_toFinset_card A hA]

end ElboimSly.Paper
