/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycRegenShiftEnv
public import Mathlib

/-!
# ES22 Lemma 2.1 (b): `Sh_z` preserves `PPP(# ⊗ μ_β)`, and its slices

ES22 Lemma 2.1 (b), "Re-indexing": for fixed `z` the map `cycShiftMap z`
is a bijection of the copies `≥ k` onto `ℕ × S_β` which carries `# ⊗ μ_β` restricted to its
domain onto `# ⊗ μ_β` (`map_cycIntensity_shift`), so `Sh_z N` is a `PPP(# ⊗ μ_β)` for a
`PPP(# ⊗ μ_β)` `N` (`isPoissonPointProcess_cycShift`, `law_cycShift`).
The slices of `Sh_z ν` are the recentred slice `k` of `ν` and the slices `k + 1 + j`
(`cycSlice_zero_cycShift`, `cycSlice_succ_cycShift`).
-/

@[expose] public section

open MeasureTheory Set ElboimSly.Interchange
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

set_option linter.unusedSectionVars false

variable {d : ℕ} {β : ℝ} [Fact (0 < β)]

theorem cycIntensity_apply {B : Set (ℕ × RingSpace d β)} (hB : MeasurableSet B) :
    cycIntensity ℕ d β B = ∑' a : ℕ, ringIntensity d β (Prod.mk a ⁻¹' B) := by
  unfold cycIntensity
  rw [Measure.prod_apply hB, lintegral_count]

theorem map_cycIntensity_shift (z : ShiftPar d) :
    ((cycIntensity ℕ d β).restrict (shiftDom z)).map (cycShiftMap z) = cycIntensity ℕ d β := by
  ext B hB
  have hg := measurable_cycShiftMap_at (β := β) z
  rw [Measure.map_apply hg hB, Measure.restrict_apply (hg hB), cycIntensity_apply hB,
    cycIntensity_apply ((hg hB).inter (measurableSet_shiftDom z))]
  set k := z.1
  have hkey : ∀ j : ℕ, ringIntensity d β (Prod.mk (k + j) ⁻¹' (cycShiftMap z ⁻¹' B ∩ shiftDom z)) =
      ringIntensity d β (Prod.mk j ⁻¹' B) := by
    intro j
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · have h1 : Prod.mk (k + 0) ⁻¹' (cycShiftMap z ⁻¹' B ∩ shiftDom z) =
          hitPhi (β := β) z.2.1 z.2.2 ⁻¹' (Prod.mk 0 ⁻¹' B) := by
        ext y
        simp [cycShiftMap, shiftDom, k]
      rw [h1]
      have hm := measurable_hitPhi_at (β := β) z.2.1 z.2.2
      have := Measure.map_apply hm (measurable_prodMk_left (x := (0 : ℕ)) hB) (μ := ringIntensity d β)
      rw [← this, map_hitPhi]
    · have h1 : Prod.mk (k + j) ⁻¹' (cycShiftMap z ⁻¹' B ∩ shiftDom z) = Prod.mk j ⁻¹' B := by
        ext y
        have : ¬ (k + j ≤ z.1) := by omega
        simp [cycShiftMap, shiftDom, k, this]
      rw [h1]
  have hsupp : Function.support
      (fun a : ℕ => ringIntensity d β (Prod.mk a ⁻¹' (cycShiftMap z ⁻¹' B ∩ shiftDom z))) ⊆
        Set.range (fun j : ℕ => k + j) := by
    intro a ha
    by_contra hnr
    apply ha
    have hak : a < k := by
      by_contra h
      exact hnr ⟨a - k, show k + (a - k) = a by omega⟩
    have : Prod.mk a ⁻¹' (cycShiftMap z ⁻¹' B ∩ shiftDom z) = ∅ := by
      ext y
      simp [shiftDom, k, not_le.2 hak]
    simp [this]
  rw [← Function.Injective.tsum_eq (add_right_injective k) hsupp]
  simp_rw [hkey]

/-- `Sh_z` carries a `PPP(# ⊗ μ_β)` to a `PPP(# ⊗ μ_β)`. -/
theorem isPoissonPointProcess_cycShift {Ω : Type*} [MeasurableSpace Ω] {Pr : Measure Ω}
    {N : Ω → Measure (ℕ × RingSpace d β)}
    (hN : IsPoissonPointProcess N (cycIntensity ℕ d β) Pr) (z : ShiftPar d) :
    IsPoissonPointProcess (fun ω => cycShift z (N ω)) (cycIntensity ℕ d β) Pr := by
  have h := ((hN.tau_comp).restrict (measurableSet_shiftDom z)).map_measure
    (measurable_cycShiftMap_at (β := β) z)
  rw [map_cycIntensity_shift] at h
  exact h

theorem law_cycShift {Ω : Type*} [MeasurableSpace Ω] {Pr : Measure Ω}
    {N : Ω → Measure (ℕ × RingSpace d β)}
    (hN : IsPoissonPointProcess N (cycIntensity ℕ d β) Pr) (z : ShiftPar d) :
    Pr.map (fun ω => cycShift z (N ω)) = Pr.map N :=
  hN.map_eq_map (isPoissonPointProcess_cycShift hN z)

theorem measurable_cycShift_at (z : ShiftPar d) :
    Measurable (cycShift (β := β) z) :=
  measurable_cycShift.comp measurable_prodMk_left

/-- Slice `0` of `Sh_z ν` is the recentred slice `k` of `τ(ν)`. -/
theorem cycSlice_zero_cycShift (z : ShiftPar d) (ν : Measure (ℕ × RingSpace d β)) :
    cycSlice 0 (cycShift z ν) = (cycSlice z.1 (tau (cycIntensity ℕ d β) ν)).map
      (hitPhi z.2.1 z.2.2) := by
  ext B hB
  have hg := measurable_cycShiftMap_at (β := β) z
  have hm := measurable_hitPhi_at (β := β) z.2.1 z.2.2
  unfold cycShift cycSlice
  rw [(measurableEmbedding_prodMk_left (0 : ℕ)).comap_apply, Measure.map_apply hg
    (measurableEmbedding_prodMk_left (0 : ℕ) |>.measurableSet_image.2 hB),
    Measure.restrict_apply (hg (measurableEmbedding_prodMk_left (0 : ℕ) |>.measurableSet_image.2 hB)),
    Measure.map_apply hm hB, (measurableEmbedding_prodMk_left z.1).comap_apply]
  congr 1
  ext ⟨a, y⟩
  simp only [mem_inter_iff, mem_preimage, mem_image, shiftDom, mem_ofPred_eq, cycShiftMap]
  constructor
  · rintro ⟨⟨y', hy', h⟩, ha⟩
    by_cases h1 : a ≤ z.1
    · rw [ite_eq_left h1] at h
      simp only [Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      exact ⟨y, by simpa using hy', by simp [show a = z.1 by omega]⟩
    · rw [ite_eq_right h1] at h
      simp only [Prod.mk.injEq] at h
      omega
  · rintro ⟨y', hy', h⟩
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨⟨hitPhi z.2.1 z.2.2 y', hy', by simp⟩, le_rfl⟩

/-- Slice `j + 1` of `Sh_z ν` is slice `k + 1 + j` of `τ(ν)`. -/
theorem cycSlice_succ_cycShift (z : ShiftPar d) (ν : Measure (ℕ × RingSpace d β)) (j : ℕ) :
    cycSlice (j + 1) (cycShift z ν) = cycSlice (z.1 + 1 + j) (tau (cycIntensity ℕ d β) ν) := by
  ext B hB
  have hg := measurable_cycShiftMap_at (β := β) z
  unfold cycShift cycSlice
  rw [(measurableEmbedding_prodMk_left (j + 1)).comap_apply, Measure.map_apply hg
    (measurableEmbedding_prodMk_left (j + 1) |>.measurableSet_image.2 hB),
    Measure.restrict_apply (hg (measurableEmbedding_prodMk_left (j + 1) |>.measurableSet_image.2 hB)),
    (measurableEmbedding_prodMk_left (z.1 + 1 + j)).comap_apply]
  congr 1
  ext ⟨a, y⟩
  simp only [mem_inter_iff, mem_preimage, mem_image, shiftDom, mem_ofPred_eq, cycShiftMap]
  constructor
  · rintro ⟨⟨y', hy', h⟩, ha⟩
    by_cases h1 : a ≤ z.1
    · rw [ite_eq_left h1] at h
      simp only [Prod.mk.injEq] at h
      omega
    · rw [ite_eq_right h1] at h
      simp only [Prod.mk.injEq] at h
      obtain ⟨h2, h3⟩ := h
      exact ⟨y', hy', by simp only [Prod.mk.injEq]; exact ⟨by omega, h3⟩⟩
  · rintro ⟨y', hy', h⟩
    simp only [Prod.mk.injEq] at h
    obtain ⟨h2, h3⟩ := h
    subst h2
    subst h3
    refine ⟨⟨y', hy', ?_⟩, by omega⟩
    rw [ite_eq_right (by omega)]
    simp only [Prod.mk.injEq]
    exact ⟨by omega, trivial⟩

end ElboimSly.Cyclic

end
