/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycDrivenRegenMeas
public import ElboimSly.Foundations.Cyclic.CycRegWalk
public import ElboimSly.Foundations.Cyclic.CycTruncMeas
public import ElboimSly.Foundations.Cyclic.CycRegionMeas
public import ElboimSly.Foundations.Cyclic.CycRegenCut
public import ElboimSly.Foundations.Cyclic.CycHitCoupleDriven
public import Mathlib

/-!
# Measurability of the regenerated walks

The constructions of the regenerated walk ("`W_reg` is a measurable function of the record, and evaluation
of a path at a measurable time is measurable by right-continuity").

* `measurable_gluedCount_of`: the number of completed pieces by time `t` is measurable when the
  partial sums are;
* `measurable_regRecWalk`: `ρ ↦ W_reg(ρ)(t)` is measurable on records;
* `measurable_drivenRegenWalk_at`: `W_reg` built from a measurable family of driving paths;
* `drivenRegenWalkCut_eq_drivenRegenFrom`: construction (iii) agrees with `W^x_reg`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

theorem sSup_nat_eq_iff (S : Set ℕ) (n : ℕ) :
    sSup S = n ↔ (n ∈ S ∧ ∀ m, n < m → m ∉ S) ∨
      (n = 0 ∧ ((∀ m, m ∉ S) ∨ ∀ N, ∃ m, N < m ∧ m ∈ S)) := by
  by_cases hb : BddAbove S
  · by_cases hne : S.Nonempty
    · have hmem : sSup S ∈ S := Nat.sSup_mem hne hb
      have hle : ∀ m ∈ S, m ≤ sSup S := fun m hm => le_csSup hb hm
      constructor
      · rintro rfl
        exact Or.inl ⟨hmem, fun m hm hmS => absurd (hle m hmS) (not_le.2 hm)⟩
      · rintro (⟨h1, h2⟩ | ⟨-, h | h⟩)
        · refine le_antisymm (csSup_le hne fun m hm => ?_) (le_csSup hb h1)
          by_contra hc
          exact h2 m (not_le.1 hc) hm
        · obtain ⟨m, hm⟩ := hne
          exact absurd hm (h m)
        · obtain ⟨M, hM⟩ := hb
          obtain ⟨m, hm1, hm2⟩ := h M
          exact absurd (hM hm2) (not_le.2 hm1)
    · rw [Set.not_nonempty_iff_eq_empty] at hne
      subst hne
      simp only [csSup_empty, Nat.bot_eq_zero, mem_empty_iff_false, false_and, false_or]
      constructor
      · intro h; exact ⟨h.symm, Or.inl fun m => id⟩
      · rintro ⟨h, -⟩; exact h.symm
  · rw [Nat.sSup_of_not_bddAbove hb]
    constructor
    · intro h
      right
      refine ⟨h.symm, Or.inr fun N => ?_⟩
      by_contra hc
      push Not at hc
      exact hb ⟨N, fun m hm => by by_contra h; exact hc m (not_le.1 h) hm⟩
    · rintro (⟨h1, h2⟩ | ⟨h, -⟩)
      · exfalso; apply hb
        exact ⟨n, fun m hm => by by_contra h; exact h2 m (not_le.1 h) hm⟩
      · exact h.symm

theorem measurable_gluedCount_of {α : Type*} [MeasurableSpace α] {σ : α → ℕ → ℝ≥0∞}
    (hσ : ∀ n, Measurable fun a => σ a n) (t : ℝ≥0) :
    Measurable fun a => gluedCount (σ a) t := by
  have hS : ∀ m, MeasurableSet {a | σ a m ≤ (t : ℝ≥0∞)} := fun m =>
    measurableSet_le (hσ m) measurable_const
  refine measurable_to_countable' fun n => ?_
  have : (fun a => gluedCount (σ a) t) ⁻¹' {n} =
      ({a | σ a n ≤ (t : ℝ≥0∞)} ∩ ⋂ m, ⋂ (_ : n < m), {a | σ a m ≤ (t : ℝ≥0∞)}ᶜ) ∪
      ({_a | n = 0} ∩ ((⋂ m, {a | σ a m ≤ (t : ℝ≥0∞)}ᶜ) ∪
        ⋂ N, ⋃ m, ⋃ (_ : N < m), {a | σ a m ≤ (t : ℝ≥0∞)})) := by
    ext a
    simp only [mem_preimage, mem_singleton_iff, gluedCount, sSup_nat_eq_iff, mem_union,
      mem_inter_iff, mem_ofPred_eq, mem_iInter, mem_iUnion, mem_compl_iff, exists_prop]
  rw [this]
  refine MeasurableSet.union ((hS n).inter ?_) (MeasurableSet.inter (MeasurableSet.const _) ?_)
  · exact MeasurableSet.iInter fun m => MeasurableSet.iInter fun _ => (hS m).compl
  · refine MeasurableSet.union (MeasurableSet.iInter fun m => (hS m).compl) ?_
    exact MeasurableSet.iInter fun N => MeasurableSet.iUnion fun m => MeasurableSet.iUnion fun _ =>
      hS m

section Rec

variable {I : Type*} [MeasurableSpace I] {d : ℕ}

omit [MeasurableSpace I] in
theorem nth_getD_eq (junk : CycEntry I d) (ρ : CycRec I d) (k : ℕ) {γ : Type*} (f : CycEntry I d → γ)
    (z : γ) : ((ρ.nth k).map f).getD z = if (k : ℕ∞) < ρ.num then f (ρ.coord junk k) else z := by
  rcases ρ with ⟨n, g⟩ | g
  · by_cases hk : k < n
    · simp [CycRec.nth, CycRec.num, CycRec.coord, hk]
    · simp [CycRec.nth, CycRec.num, hk]
  · simp [CycRec.nth, CycRec.num, CycRec.coord]

theorem measurable_regRecWalk [MeasurableSingletonClass I] [Countable I] (t : ℝ≥0)
    [Nonempty (CycEntry I d)] :
    Measurable fun ρ : CycRec I d => regRecWalk ρ t := by
  classical
  obtain ⟨junk⟩ := ‹Nonempty (CycEntry I d)›
  have hσ : ∀ n, Measurable fun ρ : CycRec I d => ρ.cum n := fun n => measurable_cum junk n
  have hF : ∀ k, Measurable fun ρ : CycRec I d =>
      ((ρ.nth k).map fun e => e.path.fn).getD (fun _ => 0) (t - (ρ.cum k).toNNReal) := by
    intro k
    have e : (fun ρ : CycRec I d => ((ρ.nth k).map fun e => e.path.fn).getD (fun _ => 0)
        (t - (ρ.cum k).toNNReal)) = fun ρ => if (k : ℕ∞) < ρ.num then
          (ρ.coord junk k).path.fn (t - (ρ.cum k).toNNReal) else 0 := by
      funext ρ
      rw [show ((ρ.nth k).map fun e => e.path.fn).getD (fun _ => 0) (t - (ρ.cum k).toNNReal) =
        (((ρ.nth k).map fun e => e.path.fn).getD (fun _ => 0)) (t - (ρ.cum k).toNNReal) from rfl,
        nth_getD_eq junk ρ k]
      split_ifs <;> rfl
    rw [e]
    refine Measurable.ite ?_ ?_ measurable_const
    · exact CycRec.measurable_num (MeasurableSet.of_discrete (s := {x : ℕ∞ | (k : ℕ∞) < x}))
    · exact measurable_fn_at (fun ρ : CycRec I d => (ρ.coord junk k).path)
        (measurable_entry_path.comp (CycRec.measurable_coord junk k)) _
        (measurable_const.sub (ENNReal.measurable_toNNReal.comp (hσ k)))
  exact measurable_index (measurable_gluedCount_of hσ t) hF

end Rec

end ElboimSly.Cyclic

end
