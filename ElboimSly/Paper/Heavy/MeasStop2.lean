/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Heavy.MeasStop
public import ElboimSly.Paper.Heavy.CountVisited
public import ElboimSly.Paper.Heavy.NoFast

/-!
# Stopping times for adapted cyclic paths: the entrance times `s_i(B)`

Measurability (a).

* `heavySubIdx_finite`: the sub-blocks of a block form a finite set.
* `isStoppingTime_add_nnreal`: `τ + c` is a stopping time for a constant `c ≥ 0`.
* `AdaptedCyclic.isStoppingTime_entSeq`: each `s_i(B)` is a stopping time.
* `heavyEntSeq_eq_entrance`: on `{s_i(B) < ∞}`, `s_i(B) = ξ_{B''}` for a sub-block `B''`.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Paper

open ElboimSly

variable {d : ℕ}

theorem heavySubIdx_finite (j m : ℕ) (ι : Fin d → ℤ) : (heavySubIdx d j m ι).Finite := by
  refine ((ncard_heavyBlock_le m ι).1.image (heavyBlockIdx j)).subset ?_
  intro ι' hι'
  obtain ⟨a, ha⟩ := heavyBlock_nonempty j ι'
  exact ⟨a, hι' ha, heavyBlock_eq_of_mem (mem_heavyBlock_idx j a) ha⟩

theorem heavyEntrances_finite (w : ℝ → Fin d → ℤ) (j m : ℕ) (ι : Fin d → ℤ) :
    (heavyEntrances w j m ι).Finite :=
  (heavySubIdx_finite j m ι).image _

theorem sInf_le_iff_of_finite {S : Set ℝ≥0∞} (hS : S.Finite) {t : ℝ≥0∞} (ht : t ≠ ⊤) :
    sInf S ≤ t ↔ ∃ x ∈ S, x ≤ t := by
  constructor
  · intro h
    rcases S.eq_empty_or_nonempty with rfl | hne
    · simp at h; exact absurd h ht
    · exact ⟨_, hne.csInf_mem hS, h⟩
  · rintro ⟨x, hx, hxt⟩
    exact (sInf_le hx).trans hxt

variable {Ω : Type*} {m : MeasurableSpace Ω} {f : Filtration ℝ≥0 m}

theorem isStoppingTime_add_nnreal {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime f τ) (c : ℝ≥0) :
    IsStoppingTime f (fun ω => τ ω + (c : WithTop ℝ≥0)) := by
  intro i
  by_cases hc : c ≤ i
  · have h_eq : {ω | τ ω + (c : WithTop ℝ≥0) ≤ i} = {ω | τ ω ≤ ((i - c : ℝ≥0) : WithTop ℝ≥0)} := by
      ext ω
      simp only [mem_ofPred_eq]
      cases τ ω with
      | top =>
        rw [WithTop.top_add]
        exact ⟨fun h => absurd (top_le_iff.1 h) WithTop.coe_ne_top,
          fun h => absurd (top_le_iff.1 h) WithTop.coe_ne_top⟩
      | coe a =>
        norm_cast
        exact (le_tsub_iff_right hc).symm
    rw [h_eq]
    exact (f.mono (tsub_le_self)) _ (hτ (i - c))
  · have h_eq : {ω | τ ω + (c : WithTop ℝ≥0) ≤ i} = ∅ := by
      ext ω
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_le]
      calc (i : WithTop ℝ≥0) < c := by exact_mod_cast not_le.1 hc
        _ ≤ τ ω + c := le_add_self
    rw [h_eq]
    exact @MeasurableSet.empty Ω (f i)

theorem measurableSet_le_inter_le {σ ρ : Ω → WithTop ℝ≥0} (hσ : IsStoppingTime f σ)
    (hρ : IsStoppingTime f ρ) (t : ℝ≥0) :
    MeasurableSet[f t] ({ω | σ ω ≤ ρ ω} ∩ {ω | ρ ω ≤ t}) :=
  ((hρ.measurableSet _).1 (hσ.measurableSet_stopping_time_le hρ)).2 t

variable {w : Ω → ℝ → Fin d → ℤ} {j mm : ℕ} {ι : Fin d → ℤ}

/-- Measurability (a): each `s_i(B)` is a stopping time. -/
theorem AdaptedCyclic.isStoppingTime_entSeq (h : AdaptedCyclic f w) (c : ℝ≥0) :
    ∀ i : ℕ, IsStoppingTime f (fun ω => heavyEntSeq (w ω) j mm (c : ℝ≥0∞) ι i)
  | 0 => h.isStoppingTime_entrance (heavyBlock mm ι)
  | i + 1 => by
    have hs := AdaptedCyclic.isStoppingTime_entSeq h c i
    have hsD := isStoppingTime_add_nnreal hs c
    intro t
    have hset : {ω | heavyEntSeq (w ω) j mm (c : ℝ≥0∞) ι (i + 1) ≤ (t : WithTop ℝ≥0)} =
        ⋃ ι' ∈ heavySubIdx d j mm ι,
          ({ω | heavyEntSeq (w ω) j mm (c : ℝ≥0∞) ι i + (c : ℝ≥0∞) ≤
              entranceTime (w ω) (heavyBlock j ι')} ∩
            {ω | entranceTime (w ω) (heavyBlock j ι') ≤ (t : ℝ≥0∞)}) := by
      ext ω
      simp only [mem_ofPred_eq, mem_iUnion, mem_inter_iff, exists_prop]
      show sInf _ ≤ _ ↔ _
      refine (sInf_le_iff_of_finite (t := (t : ℝ≥0∞)) (((heavyEntrances_finite (w ω) j mm ι)).subset
        fun x hx => hx.1) (ENNReal.coe_ne_top)).trans ?_
      constructor
      · rintro ⟨x, ⟨⟨ι', hι', rfl⟩, hx⟩, hxt⟩
        exact ⟨ι', hι', hx, hxt⟩
      · rintro ⟨ι', hι', hx, hxt⟩
        exact ⟨_, ⟨⟨ι', hι', rfl⟩, hx⟩, hxt⟩
    have key : MeasurableSet[f t] (⋃ ι' ∈ heavySubIdx d j mm ι,
          ({ω | heavyEntSeq (w ω) j mm (c : ℝ≥0∞) ι i + (c : ℝ≥0∞) ≤
              entranceTime (w ω) (heavyBlock j ι')} ∩
            {ω | entranceTime (w ω) (heavyBlock j ι') ≤ (t : ℝ≥0∞)})) :=
      MeasurableSet.biUnion (heavySubIdx_finite j mm ι).countable fun ι' _ =>
        measurableSet_le_inter_le hsD (h.isStoppingTime_entrance (heavyBlock j ι')) t
    exact (congrArg (MeasurableSet[f t]) hset).mpr key

end ElboimSly.Paper
