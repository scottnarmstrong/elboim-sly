/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CPathStop
public import Mathlib

/-!
# Left limits of paths with finitely many jumps

Paths (a): `p(ς_a -) = p(ς_{a-1})`, and the form
`p(r-) = p(ς_a)` for `r ∈ (ς_a, ς_{a+1}]` used throughout paths, records and exploration plans.

`CPath.left p r` is the left limit `p(r-)`, defined as the value after the discontinuities
strictly before `r`. It is the eventual value of `p` on a left neighbourhood of `r`
(`CPath.eventually_left`), hence the left limit in every sense; the definition avoids any choice.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

variable {V : Type*} [MeasurableSpace V] [Countable V] [MeasurableSingletonClass V]

/-- The left limit `p(r-)`: the value after the discontinuities strictly before `r`. -/
noncomputable def CPath.left (p : CPath V) (r : ℝ≥0) : V :=
  p.jv (CDisc p.fn ∩ Iio r).ncard

omit [MeasurableSpace V] [Countable V] [MeasurableSingletonClass V] in
theorem CPath.eventually_left (p : CPath V) {r : ℝ≥0} (hr : 0 < r) :
    ∀ᶠ u in 𝓝[<] r, p.fn u = p.left r := by
  obtain ⟨t, htr, ht⟩ := p.exists_left_gap hr
  filter_upwards [Ioo_mem_nhdsLT htr] with u hu
  rw [p.fn_eq_jv, CPath.left]
  congr 1
  unfold CPath.cnt
  congr 1
  ext x
  simp only [mem_inter_iff, mem_Iic, mem_Iio]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, h2.trans_lt hu.2⟩
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    by_contra hxu
    exact ht x h1 (hu.1.trans (not_le.mp hxu)) h2

omit [MeasurableSpace V] [Countable V] [MeasurableSingletonClass V] in
theorem CPath.left_eq_of_eventually (p : CPath V) {r : ℝ≥0} (hr : 0 < r) {z : V}
    (h : ∀ᶠ u in 𝓝[<] r, p.fn u = z) : p.left r = z := by
  have : (𝓝[<] r).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, hr⟩
  obtain ⟨u, hu1, hu2⟩ := ((p.eventually_left hr).and h).exists
  exact hu1.symm.trans hu2

omit [MeasurableSpace V] [Countable V] [MeasurableSingletonClass V] in
theorem CPath.mem_CDisc_iff (p : CPath V) {r : ℝ≥0} (hr : 0 < r) :
    r ∈ CDisc p.fn ↔ p.left r ≠ p.fn r := by
  unfold CDisc
  simp only [mem_ofPred_eq]
  constructor
  · rintro ⟨_, h⟩ hl
    exact h (by filter_upwards [p.eventually_left hr] with u hu; rw [hu, hl])
  · intro h
    refine ⟨hr, fun hev => h ?_⟩
    exact p.left_eq_of_eventually hr hev

omit [MeasurableSpace V] [Countable V] [MeasurableSingletonClass V] in
theorem CPath.left_eq_fn_of_notMem (p : CPath V) {r : ℝ≥0} (hr : 0 < r) (h : r ∉ CDisc p.fn) :
    p.left r = p.fn r := by
  by_contra hne
  exact h ((p.mem_CDisc_iff hr).2 hne)

omit [MeasurableSpace V] [Countable V] [MeasurableSingletonClass V] in
/-- `p(r-) = p(ς_a)` for `r ∈ (ς_a, ς_{a+1}]`. -/
theorem CPath.left_eq_jv (p : CPath V) {a : ℕ} {r : ℝ≥0} (h1 : p.jt a < r)
    (h2 : (r : ℝ≥0∞) ≤ p.jt (a + 1)) : p.left r = p.jv a := by
  have hta : p.jt a < ⊤ := h1.trans ENNReal.coe_lt_top
  have hr : 0 < r := by
    rcases eq_or_ne r 0 with h0 | h0
    · subst h0; simp at h1
    · exact pos_iff_ne_zero.mpr h0
  have hb : (p.jt a).toNNReal < r := by
    have : ((p.jt a).toNNReal : ℝ≥0∞) < r := by rwa [ENNReal.coe_toNNReal hta.ne]
    exact_mod_cast this
  have : (𝓝[<] r).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, hr⟩
  obtain ⟨u, hu1, hu2⟩ := ((p.eventually_left hr).and (Ioo_mem_nhdsLT hb)).exists
  rw [← hu1, p.fn_eq_jv]
  have h3 : a ≤ p.cnt u := by
    rw [← p.jt_le_iff]
    rw [← ENNReal.coe_toNNReal hta.ne]
    exact_mod_cast hu2.1.le
  have h4 : p.cnt u < a + 1 := by
    refine p.cnt_lt_of_lt_jt ?_
    exact lt_of_lt_of_le (by exact_mod_cast hu2.2) h2
  have : p.cnt u = a := by omega
  rw [this]

end ElboimSly.Cyclic

end
