/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycTruncSpec
public import Mathlib

/-!
# Measurability of `(ρ, s) ↦ Trunc_s(ρ)`

Measurability of record functionals (b).
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

variable {I : Type*} [MeasurableSpace I] {d : ℕ}

theorem measurable_cum (junk : CycEntry I d) (j : ℕ) :
    Measurable fun ρ : CycRec I d => ρ.cum j := by
  have : (fun ρ : CycRec I d => ρ.cum j) = fun ρ => ∑ i ∈ Finset.range j,
      if (i : ℕ∞) < ρ.num then (ρ.coord junk i).len else 0 := funext fun ρ => by
    unfold CycRec.cum; exact Finset.sum_congr rfl fun i _ => CycRec.lenAt_eq junk ρ i
  rw [this]
  refine Finset.measurable_sum _ fun i _ => ?_
  refine Measurable.ite ?_ ?_ measurable_const
  · exact CycRec.measurable_num (MeasurableSet.of_discrete (s := {x : ℕ∞ | (i : ℕ∞) < x}))
  · exact (CPath.measurable_len.comp (measurable_subtype_coe.comp measurable_snd)).comp
      (CycRec.measurable_coord junk i)

theorem measurableSet_surv (junk : CycEntry I d) (j : ℕ) :
    MeasurableSet {q : CycRec I d × ℝ≥0 | j ∈ q.1.surv q.2} := by
  have h1 : MeasurableSet {q : CycRec I d × ℝ≥0 | (j : ℕ∞) < q.1.num} :=
    (CycRec.measurable_num.comp measurable_fst)
      (MeasurableSet.of_discrete (s := {x : ℕ∞ | (j : ℕ∞) < x}))
  have h2 : MeasurableSet {q : CycRec I d × ℝ≥0 | q.1.cum j ≤ q.2} :=
    measurableSet_le ((measurable_cum junk j).comp measurable_fst)
      (measurable_coe_nnreal_ennreal.comp measurable_snd)
  exact h1.inter h2

/-- Measurability of record functionals (b): `(ρ, s) ↦ Trunc_s(ρ)` is measurable. -/
theorem measurable_trunc [Nonempty (CycEntry I d)] :
    Measurable (fun q : CycRec I d × ℝ≥0 => CycRec.trunc q.2 q.1) := by
  classical
  obtain ⟨junk⟩ := ‹Nonempty (CycEntry I d)›
  refine measurable_cycRec_of_coords _ junk ?_ fun j => ?_
  · rw [ENat.measurable_iff]
    intro n
    have : (fun q : CycRec I d × ℝ≥0 => (CycRec.trunc q.2 q.1).num) ⁻¹' {(n : ℕ∞)} =
        ({q | (n - 1) ∈ q.1.surv q.2} ∪ {_q | n = 0}) ∩ {q | n ∈ q.1.surv q.2}ᶜ := by
      ext q
      obtain ⟨m, hm, hiff, -, -⟩ := CycRec.trunc_spec junk q.2 q.1
      simp only [mem_preimage, mem_singleton_iff, hm, mem_inter_iff, mem_union, mem_ofPred_eq,
        mem_compl_iff]
      constructor
      · rintro rfl
        refine ⟨?_, fun h => ?_⟩
        · by_cases hn : n = 0
          · exact Or.inr hn
          · left
            exact (hiff _).1 (by exact_mod_cast (show n - 1 < n by omega))
        · exact absurd ((hiff n).2 h) (lt_irrefl _)
      · rintro ⟨hh, hn⟩
        rcases lt_trichotomy m (n : ℕ∞) with hlt | heq | hgt
        · exfalso
          obtain ⟨k, rfl⟩ := ENat.ne_top_iff_exists.mp (ne_top_of_lt hlt)
          have hkn : k < n := by exact_mod_cast hlt
          rcases hh with hh | hh
          · have := (hiff (n - 1)).2 hh
            have : ((n - 1 : ℕ) : ℕ∞) < (k : ℕ∞) := by simpa using this
            have : n - 1 < k := by exact_mod_cast this
            omega
          · omega
        · exact heq
        · exact absurd ((hiff n).1 hgt) hn
    rw [this]
    refine (((measurableSet_surv junk (n - 1)).union (MeasurableSet.const _)).inter
      (measurableSet_surv junk n).compl)
  · have key : (fun q : CycRec I d × ℝ≥0 => (CycRec.trunc q.2 q.1).coord junk j) =
        fun q => if j ∈ q.1.surv q.2 then
          CycRec.truncEntry q.2 q.1 j (q.1.coord junk j) else junk := funext fun q => by
      obtain ⟨m, hm, hiff, h1, h2⟩ := CycRec.trunc_spec junk q.2 q.1
      by_cases h : j ∈ q.1.surv q.2
      · rw [ite_eq_left h]; exact h1 j h
      · rw [ite_eq_right h]; exact h2 j h
    rw [key]
    refine Measurable.ite (measurableSet_surv junk j) ?_ measurable_const
    have hc : Measurable fun q : CycRec I d × ℝ≥0 => q.1.coord junk j :=
      (CycRec.measurable_coord junk j).comp measurable_fst
    have hs : Measurable fun q : CycRec I d × ℝ≥0 => (q.2 : ℝ≥0∞) :=
      measurable_coe_nnreal_ennreal.comp measurable_snd
    have hcj : ∀ k, Measurable fun q : CycRec I d × ℝ≥0 => q.1.cum k := fun k =>
      (measurable_cum junk k).comp measurable_fst
    unfold CycRec.truncEntry
    refine Measurable.ite (measurableSet_le (hcj (j + 1)) hs) hc ?_
    exact measurable_entry_cut.comp (hc.prodMk (hs.sub (hcj j)))

end ElboimSly.Cyclic

end
