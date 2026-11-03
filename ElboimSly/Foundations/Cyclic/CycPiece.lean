/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycPathType
public import ElboimSly.Foundations.Cyclic.CPathCount
public import ElboimSly.Foundations.Cyclic.CPathJump
public import Mathlib

/-!
# Initial pieces of paths

Measurability of record functionals (e). A path `p` is an *initial piece* of `q` if `p = q(· ∧ ℓ)` with
`ℓ = len p ≤ len q`. We show that the jump times of an initial piece are those of `q` that are at
most `ℓ` (and `∞` otherwise), and the values agree.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

variable {V : Type*} [MeasurableSpace V] [Countable V] [MeasurableSingletonClass V]

omit [MeasurableSpace V] [Countable V] [MeasurableSingletonClass V] in
theorem CPath.ext' {p q : CPath V} (hl : p.len = q.len) (hf : p.fn = q.fn) : p = q := by
  cases p; cases q
  simp only at hl hf
  subst hl; subst hf; rfl

/-- `p` is an initial piece of `q`. -/
def CPath.IsPiece (p q : CPath V) : Prop := p.len ≤ q.len ∧ p = q.cut p.len

omit [MeasurableSpace V] [Countable V] [MeasurableSingletonClass V] in
theorem CPath.cut_len_self (p : CPath V) : p.cut p.len = p := by
  refine CPath.ext' (CPath.cut_len _ _) (funext fun s => ?_)
  rw [CPath.cut_fn]
  by_cases hl : p.len = ⊤
  · rw [hl]; simp
  · rcases le_total (s : ℝ≥0∞) p.len with h | h
    · rw [min_eq_left h]; simp
    · rw [min_eq_right h]
      refine p.const _ _ (by rw [ENNReal.coe_toNNReal hl]) h

omit [MeasurableSpace V] [Countable V] [MeasurableSingletonClass V] in
theorem CPath.isPiece_refl (p : CPath V) : p.IsPiece p := ⟨le_rfl, (CPath.cut_len_self p).symm⟩

omit [MeasurableSpace V] [Countable V] [MeasurableSingletonClass V] in
theorem CPath.cut_cut (p : CPath V) {a b : ℝ≥0∞} (h : b ≤ a) : (p.cut a).cut b = p.cut b := by
  refine CPath.ext' (by simp) (funext fun s => ?_)
  rw [CPath.cut_fn, CPath.cut_fn, CPath.cut_fn]
  congr 1
  by_cases hb : b = ⊤
  · have : a = ⊤ := top_le_iff.mp (hb ▸ h)
    simp [hb, this]
  · have hbs : (min (s : ℝ≥0∞) b) ≠ ⊤ := ne_top_of_le_ne_top hb (min_le_right _ _)
    have : ((min (s : ℝ≥0∞) b).toNNReal : ℝ≥0∞) = min (s : ℝ≥0∞) b := ENNReal.coe_toNNReal hbs
    rw [this, min_assoc, min_eq_left h]

omit [MeasurableSpace V] [Countable V] [MeasurableSingletonClass V] in
theorem CPath.IsPiece.trans {p q r : CPath V} (hpq : p.IsPiece q) (hqr : q.IsPiece r) :
    p.IsPiece r := by
  refine ⟨hpq.1.trans hqr.1, ?_⟩
  calc p = q.cut p.len := hpq.2
    _ = (r.cut q.len).cut p.len := by rw [← hqr.2]
    _ = r.cut p.len := CPath.cut_cut r hpq.1

theorem CPath.fn_cut_of_le {V : Type*} (p : CPath V) {ℓ : ℝ≥0∞} {r : ℝ≥0} (h : (r : ℝ≥0∞) ≤ ℓ) :
    (p.cut ℓ).fn r = p.fn r := by
  rw [CPath.cut_fn, min_eq_left h]
  simp

theorem ennreal_eq_of_forall_le_iff {x y : ℝ≥0∞} (h : ∀ s : ℝ≥0, x ≤ s ↔ y ≤ s) : x = y := by
  have key : ∀ x y : ℝ≥0∞, (∀ s : ℝ≥0, x ≤ s ↔ y ≤ s) → x ≤ y := by
    intro x y h
    rcases eq_or_ne y ⊤ with rfl | hy
    · exact le_top
    · lift y to ℝ≥0 using hy
      exact (h y).mpr le_rfl
  exact le_antisymm (key x y h) (key y x fun s => (h s).symm)

theorem CPath.mem_CDisc_cut (p : CPath V) (ℓ : ℝ≥0∞) {s : ℝ≥0} :
    s ∈ CDisc (p.cut ℓ).fn ↔ s ∈ CDisc p.fn ∧ (s : ℝ≥0∞) ≤ ℓ := by
  by_cases hs0 : 0 < s
  · constructor
    · intro h
      by_cases hl : ℓ = ⊤
      · have hfn : (p.cut ℓ).fn = p.fn := funext fun x => by simp [CPath.cut_fn, hl]
        rw [hfn] at h
        exact ⟨h, by simp [hl]⟩
      · have hc : p.cut ℓ = p.stop ℓ.toNNReal := by simp [CPath.cut, hl]
        rw [hc] at h
        obtain ⟨h1, h2⟩ := CPath.CDisc_stop_subset p _ h
        refine ⟨h1, ?_⟩
        have : s ≤ ℓ.toNNReal := h2
        rw [← ENNReal.coe_toNNReal hl]; exact_mod_cast this
    · rintro ⟨h1, h2⟩
      rw [CPath.mem_CDisc_iff _ hs0, CPath.left_cut _ _ hs0 h2, CPath.fn_cut_of_le _ h2]
      exact (CPath.mem_CDisc_iff _ hs0).mp h1
  · exact ⟨fun h => absurd h.1 hs0, fun h => absurd h.1.1 hs0⟩

theorem CPath.cnt_cut (p : CPath V) (ℓ : ℝ≥0∞) (s : ℝ≥0) :
    (p.cut ℓ).cnt s = p.cnt (min (s : ℝ≥0∞) ℓ).toNNReal := by
  unfold CPath.cnt
  congr 1
  ext r
  simp only [mem_inter_iff, mem_Iic, CPath.mem_CDisc_cut]
  have hm : (min (s : ℝ≥0∞) ℓ) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_left _ _)
  have : r ≤ (min (s : ℝ≥0∞) ℓ).toNNReal ↔ (r : ℝ≥0∞) ≤ min (s : ℝ≥0∞) ℓ := by
    rw [← ENNReal.coe_le_coe, ENNReal.coe_toNNReal hm]
  rw [this, le_min_iff]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, by exact_mod_cast h3, h2⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, h3⟩, by exact_mod_cast h2⟩

/-- The jump times of an initial piece: those of `p` up to `ℓ`, and `∞` afterwards. -/
theorem CPath.jt_cut (p : CPath V) (ℓ : ℝ≥0∞) (a : ℕ) :
    (p.cut ℓ).jt a = if p.jt a ≤ ℓ then p.jt a else ⊤ := by
  refine ennreal_eq_of_forall_le_iff fun s => ?_
  rw [(p.cut ℓ).jt_le_iff, CPath.cnt_cut]
  have hm : (min (s : ℝ≥0∞) ℓ) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_left _ _)
  rw [← p.jt_le_iff, ENNReal.coe_toNNReal hm, le_min_iff]
  split_ifs with h
  · constructor
    · rintro ⟨h1, -⟩; exact h1
    · intro h1; exact ⟨h1, h⟩
  · simp only [top_le_iff, ENNReal.coe_ne_top, iff_false, not_and]
    intro _ h2
    exact h h2

end ElboimSly.Cyclic

end
