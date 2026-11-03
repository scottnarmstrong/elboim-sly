/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycDrivenRule
public import ElboimSly.Foundations.Cyclic.CycDrivenUnique
public import Mathlib

/-!
# Existence of the driven path

Basic properties of world-lines (c). Abstract form: let `E ⊆ (0, ∞)` be locally finite and such that
outside `E` nothing can move the path (hypotheses `h2`, `h3`, `h4` below, which are proved for the
written proof's `E_k` in `CycDrivenEvents`). Then a driven path exists, with all jumps in `E`.
Induction on `|E ∩ (0, T]|` gives a solution constant after `T` for each `T`; uniqueness glues them.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

variable {I : Type*} [MeasurableSpace I] {d : ℕ} {β : ℝ} [Fact (0 < β)]
  {R Q : Set (I × RingSpace d β)} {δ : CycData I d} {X : CPath (Fin d → ℤ)} {a : ℝ≥0}

omit [MeasurableSpace I] in
theorem DrvRule.congr {p p' : CPath (Fin d → ℤ)} {r : ℝ≥0} (hr : 0 < r)
    (h : DrvRule β R Q δ X a p r) (hag : ∀ t ≤ r, p.fn t = p'.fn t) :
    DrvRule β R Q δ X a p' r := by
  have hlt : ∀ t < r, p.fn t = p'.fn t := fun t ht => hag t ht.le
  have hl : p'.left r = p.left r := (CPath.left_congr p p' hr hlt).symm
  have hl' : ∀ t, 0 < t → t < r → p'.left t = p.left t := fun t ht htr =>
    (CPath.left_congr p p' ht fun u hu => hlt u (hu.trans htr)).symm
  have hZ : drvZown β δ p' r = drvZown β δ p r := by
    ext x
    simp only [drvZown, mem_ofPred_eq]
    refine exists_congr fun r' => and_congr_right fun h0 => and_congr_right fun h1 => ?_
    rw [hl' r' h0 h1]
  have hQ : drvQown β δ p' r = drvQown β δ p r := by
    ext x
    simp only [drvQown, mem_ofPred_eq]
    refine exists_congr fun r' => and_congr_right fun h0 => and_congr_right fun h1 => ?_
    rw [hl' r' h0 h1, hlt r' h1]
  unfold DrvRule at h ⊢
  rw [hl, ← hag r le_rfl, hZ, hQ]
  exact h

omit [MeasurableSpace I] in
theorem DrvRule.fn_eq {p p' : CPath (Fin d → ℤ)} {r : ℝ≥0} (hr : 0 < r)
    (h : DrvRule β R Q δ X a p r) (h' : DrvRule β R Q δ X a p' r)
    (hlt : ∀ t < r, p.fn t = p'.fn t) : p.fn r = p'.fn r := by
  have hl : p'.left r = p.left r := (CPath.left_congr p p' hr hlt).symm
  have hl' : ∀ t, 0 < t → t < r → p'.left t = p.left t := fun t ht htr =>
    (CPath.left_congr p p' ht fun u hu => hlt u (hu.trans htr)).symm
  have hZ : drvZown β δ p' r = drvZown β δ p r := by
    ext x
    simp only [drvZown, mem_ofPred_eq]
    refine exists_congr fun r' => and_congr_right fun h0 => and_congr_right fun h1 => ?_
    rw [hl' r' h0 h1]
  have hQ : drvQown β δ p' r = drvQown β δ p r := by
    ext x
    simp only [drvQown, mem_ofPred_eq]
    refine exists_congr fun r' => and_congr_right fun h0 => and_congr_right fun h1 => ?_
    rw [hl' r' h0 h1, hlt r' h1]
  unfold DrvRule at h h'
  rw [hl, hZ, hQ] at h'
  exact RuleFn.unique h h'

omit [MeasurableSpace I] in
/-- Uniqueness of solutions of the rules on `[0, T]`. -/
theorem drv_eq_of_le {T : ℝ≥0} {p p' : CPath (Fin d → ℤ)} (h0 : p.fn 0 = p'.fn 0)
    (hp : ∀ r, 0 < r → r ≤ T → DrvRule β R Q δ X a p r)
    (hp' : ∀ r, 0 < r → r ≤ T → DrvRule β R Q δ X a p' r) : ∀ t ≤ T, p.fn t = p'.fn t := by
  by_contra hne
  push Not at hne
  set B := {t : ℝ≥0 | t ≤ T ∧ p.fn t ≠ p'.fn t} with hB
  have hBne : B.Nonempty := by
    obtain ⟨t, ht, ht2⟩ := hne
    exact ⟨t, ht, ht2⟩
  set s := sInf B with hs
  have hsT : s ≤ T := (csInf_le (OrderBot.bddBelow B) hBne.some_mem).trans hBne.some_mem.1
  have hbelow : ∀ t < s, p.fn t = p'.fn t := fun t ht => by
    by_contra hh
    exact absurd (csInf_le (OrderBot.bddBelow B) ⟨(ht.le.trans hsT), hh⟩) (not_le.mpr ht)
  have hsB : p.fn s = p'.fn s := by
    rcases eq_or_ne s 0 with hz | hz
    · rw [hz]; exact h0
    · exact DrvRule.fn_eq (pos_iff_ne_zero.mpr hz) (hp s (pos_iff_ne_zero.mpr hz) hsT)
        (hp' s (pos_iff_ne_zero.mpr hz) hsT) hbelow
  obtain ⟨u1, hu1, hs1⟩ := mem_nhdsGE_iff_exists_Ico_subset.mp (p.rc s)
  obtain ⟨u2, hu2, hs2⟩ := mem_nhdsGE_iff_exists_Ico_subset.mp (p'.rc s)
  have hge : ∀ t ∈ B, min u1 u2 ≤ t := fun t ht => by
    by_contra hlt
    push Not at hlt
    have hst : s ≤ t := csInf_le (OrderBot.bddBelow B) ht
    have e1 : p.fn t = p.fn s := hs1 ⟨hst, hlt.trans_le (min_le_left _ _)⟩
    have e2 : p'.fn t = p'.fn s := hs2 ⟨hst, hlt.trans_le (min_le_right _ _)⟩
    exact ht.2 (e1.trans (hsB.trans e2.symm))
  have := le_csInf hBne hge
  exact absurd this (not_le.mpr (lt_min hu1 hu2))

end ElboimSly.Cyclic

end
