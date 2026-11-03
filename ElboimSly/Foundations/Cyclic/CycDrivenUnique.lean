/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycLines
public import Mathlib

/-!
# Uniqueness of the driven path

Basic properties of world-lines (c), uniqueness. Two paths satisfying `IsDriven` (same data) coincide:
the rules (D1′)–(D3′) at `r` determine `p(r)` from `p` on `[0, r)`, and a first-disagreement
argument using right-continuity finishes.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

variable {I : Type*} [MeasurableSpace I] {d : ℕ} {β : ℝ} [Fact (0 < β)]

theorem CPath.left_congr {V : Type*} [MeasurableSpace V] [Countable V]
    [MeasurableSingletonClass V] (p p' : CPath V) {s : ℝ≥0} (hs : 0 < s)
    (h : ∀ t < s, p.fn t = p'.fn t) : p.left s = p'.left s := by
  refine p.left_eq_of_eventually hs ?_
  filter_upwards [p'.eventually_left hs, self_mem_nhdsWithin (a := s) (s := Iio s)] with u hu hus
  rw [h u hus, hu]

omit [MeasurableSpace I] in
/-- The rules determine `p(r)` from the left limit and the sets `Z`, `Q'`. -/
theorem IsDriven.fn_eq_of_data {R Q : Set (I × RingSpace d β)} {δ : CycData I d}
    {X : CPath (Fin d → ℤ)} {a : ℝ≥0} {p p' : CPath (Fin d → ℤ)}
    (h : IsDriven β R Q δ X a p) (h' : IsDriven β R Q δ X a p') {r : ℝ≥0} (hr : 0 < r)
    (hs : ∀ t < r, p.fn t = p'.fn t) : p.fn r = p'.fn r := by
  have hl : p.left r = p'.left r := CPath.left_congr p p' hr hs
  have hl' : ∀ t, 0 < t → t < r → p.left t = p'.left t := fun t ht htr =>
    CPath.left_congr p p' ht fun u hu => hs u (hu.trans htr)
  have h1 := h.2.2 r hr
  have h2 := h'.2.2 r hr
  simp only at h1 h2
  rw [← hl] at h2
  have hZ : {x : I × RingSpace d β | ∃ r' : ℝ≥0, 0 < r' ∧ r' < r ∧
      x.1 = δ.copy ∧ x.2.2 = δ.clock β r' ∧ Edge.Mem (p'.left r') x.2.1} =
      {x | ∃ r' : ℝ≥0, 0 < r' ∧ r' < r ∧
      x.1 = δ.copy ∧ x.2.2 = δ.clock β r' ∧ Edge.Mem (p.left r') x.2.1} := by
    ext x
    simp only [mem_ofPred_eq]
    refine exists_congr fun r' => and_congr_right fun h0 => and_congr_right fun h1 => ?_
    rw [hl' r' h0 h1]
  have hQ : {x : I × RingSpace d β | ∃ r' : ℝ≥0, 0 < r' ∧ r' < r ∧
      p'.left r' ≠ p'.fn r' ∧ x.1 = δ.copy ∧ x.2.2 = δ.clock β r' ∧
      x.2.1.1 = s(p'.left r', p'.fn r')} =
      {x | ∃ r' : ℝ≥0, 0 < r' ∧ r' < r ∧
      p.left r' ≠ p.fn r' ∧ x.1 = δ.copy ∧ x.2.2 = δ.clock β r' ∧
      x.2.1.1 = s(p.left r', p.fn r')} := by
    ext x
    simp only [mem_ofPred_eq]
    refine exists_congr fun r' => and_congr_right fun h0 => and_congr_right fun h1 => ?_
    rw [hl' r' h0 h1, hs r' h1]
  rw [hZ, hQ] at h2
  obtain ⟨d1, d2, d3⟩ := h1
  obtain ⟨d1', d2', d3'⟩ := h2
  set w := p.left r
  by_cases hc : ∃ e : Edge d, Edge.Mem w e ∧ (δ.copy, (e, δ.clock β r)) ∈
      (Q ∪ {x : I × RingSpace d β | ∃ r' : ℝ≥0, 0 < r' ∧ r' < r ∧
      p.left r' ≠ p.fn r' ∧ x.1 = δ.copy ∧ x.2.2 = δ.clock β r' ∧
      x.2.1.1 = s(p.left r', p.fn r')})
  · -- least edge
    classical
    let S : Set ℕ := {n | ∃ e : Edge d, Edge.Mem w e ∧ (δ.copy, (e, δ.clock β r)) ∈
      (Q ∪ {x : I × RingSpace d β | ∃ r' : ℝ≥0, 0 < r' ∧ r' < r ∧
      p.left r' ≠ p.fn r' ∧ x.1 = δ.copy ∧ x.2.2 = δ.clock β r' ∧
      x.2.1.1 = s(p.left r', p.fn r')}) ∧ n = edgeEnc e}
    have hSne : S.Nonempty := by
      obtain ⟨e, he1, he2⟩ := hc
      exact ⟨_, e, he1, he2, rfl⟩
    obtain ⟨e0, he0, he0', hn⟩ : ∃ e0 : Edge d, Edge.Mem w e0 ∧ (δ.copy, (e0, δ.clock β r)) ∈
        (Q ∪ {x : I × RingSpace d β | ∃ r' : ℝ≥0, 0 < r' ∧ r' < r ∧
        p.left r' ≠ p.fn r' ∧ x.1 = δ.copy ∧ x.2.2 = δ.clock β r' ∧
        x.2.1.1 = s(p.left r', p.fn r')}) ∧ edgeEnc e0 = sInf S := by
      have := Nat.sInf_mem hSne
      obtain ⟨e, he1, he2, he3⟩ := this
      exact ⟨e, he1, he2, he3.symm⟩
    have hmin : ∀ e' : Edge d, Edge.Mem w e' → (δ.copy, (e', δ.clock β r)) ∈
        (Q ∪ {x : I × RingSpace d β | ∃ r' : ℝ≥0, 0 < r' ∧ r' < r ∧
        p.left r' ≠ p.fn r' ∧ x.1 = δ.copy ∧ x.2.2 = δ.clock β r' ∧
        x.2.1.1 = s(p.left r', p.fn r')}) → edgeEnc e0 ≤ edgeEnc e' := fun e' h1 h2 => by
      rw [hn]; exact Nat.sInf_le ⟨e', h1, h2, rfl⟩
    have a1 := d1 e0 he0 he0' hmin
    have a2 := d1' e0 he0 he0' hmin
    have : s(w, p.fn r) = s(w, p'.fn r) := a1.symm.trans a2
    exact Sym2.congr_right.mp this
  · have hc' := hc
    by_cases hj : (X.left (a + r) ≠ X.fn (a + r) ∧
        (∀ e : Edge d, e.1 = s(w, w + (X.fn (a + r) - X.left (a + r))) →
          (δ.copy, (e, δ.clock β r)) ∉ (R ∪ {x : I × RingSpace d β | ∃ r' : ℝ≥0, 0 < r' ∧ r' < r ∧
      x.1 = δ.copy ∧ x.2.2 = δ.clock β r' ∧ Edge.Mem (p.left r') x.2.1})))
    · rw [d2 hc hj.1 hj.2, d2' hc hj.1 hj.2]
    · rw [d3 hc hj, d3' hc hj]

omit [MeasurableSpace I] in
theorem IsDriven.fn_eq {R Q : Set (I × RingSpace d β)} {δ : CycData I d}
    {X : CPath (Fin d → ℤ)} {a : ℝ≥0} {p p' : CPath (Fin d → ℤ)}
    (h : IsDriven β R Q δ X a p) (h' : IsDriven β R Q δ X a p') : p.fn = p'.fn := by
  by_contra hne
  have hB : {t : ℝ≥0 | p.fn t ≠ p'.fn t}.Nonempty := by
    by_contra hE
    exact hne (funext fun t => by_contra fun ht => hE ⟨t, ht⟩)
  set B := {t : ℝ≥0 | p.fn t ≠ p'.fn t}
  set s := sInf B with hs
  have hbelow : ∀ t < s, p.fn t = p'.fn t := fun t ht => by
    by_contra hh
    exact absurd (csInf_le (OrderBot.bddBelow B) hh) (not_le.mpr ht)
  have hsB : p.fn s = p'.fn s := by
    rcases eq_or_ne s 0 with h0 | h0
    · rw [h0, h.2.1, h'.2.1]
    · exact h.fn_eq_of_data h' (pos_iff_ne_zero.mpr h0) hbelow
  obtain ⟨u1, hu1, hs1⟩ := mem_nhdsGE_iff_exists_Ico_subset.mp (p.rc s)
  obtain ⟨u2, hu2, hs2⟩ := mem_nhdsGE_iff_exists_Ico_subset.mp (p'.rc s)
  have hge : ∀ t ∈ B, min u1 u2 ≤ t := fun t ht => by
    by_contra hlt
    push Not at hlt
    have hst : s ≤ t := csInf_le (OrderBot.bddBelow B) ht
    have e1 : p.fn t = p.fn s := hs1 ⟨hst, hlt.trans_le (min_le_left _ _)⟩
    have e2 : p'.fn t = p'.fn s := hs2 ⟨hst, hlt.trans_le (min_le_right _ _)⟩
    exact ht (e1.trans (hsB.trans e2.symm))
  have := le_csInf hB hge
  exact absurd this (not_le.mpr (lt_min hu1 hu2 |>.trans_le' le_rfl |> fun x => by
    have : s < min u1 u2 := lt_min hu1 hu2
    exact this))

end ElboimSly.Cyclic

end
