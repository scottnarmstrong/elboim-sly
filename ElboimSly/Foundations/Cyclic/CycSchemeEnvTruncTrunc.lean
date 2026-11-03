/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycTruncSpec
public import ElboimSly.Foundations.Cyclic.CycFirstEvents2
public import ElboimSly.Foundations.Cyclic.CycSchemeEnvLim
public import Mathlib

/-!
# Truncating a truncation

The environment scheme (c): `cycRec(s') = Trunc_{s'}(cycRec(s_∘))` for `s' ≤ s_∘`.
`CycRec.trunc_trunc`: `Trunc_{s'}(Trunc_s(ρ)) = Trunc_{s'}(ρ)` for `s' ≤ s` and every record `ρ`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

variable {I : Type*} [MeasurableSpace I] {d : ℕ}

namespace CycRec

open scoped Classical in
omit [MeasurableSpace I] in
theorem trunc_nth (junk : CycEntry I d) (s : ℝ≥0) (ρ : CycRec I d) (k : ℕ) :
    (CycRec.trunc s ρ).nth k =
      if k ∈ ρ.surv s then some (CycRec.truncEntry s ρ k (ρ.coord junk k)) else none := by
  obtain ⟨m, hm, hiff, hcoord, -⟩ := CycRec.trunc_spec junk s ρ
  by_cases hs : k ∈ ρ.surv s
  · have hkm : (k : ℕ∞) < (CycRec.trunc s ρ).num := by rw [hm]; exact (hiff k).2 hs
    obtain ⟨e, he⟩ := nth_of_lt_num hkm
    have hcoe : (CycRec.trunc s ρ).coord junk k = e := by
      unfold CycRec.coord; rw [he]; rfl
    rw [ite_eq_left hs, he, ← hcoord k hs, hcoe]
  · have hkm : ¬ (k : ℕ∞) < (CycRec.trunc s ρ).num := by
      rw [hm]; exact fun h => hs ((hiff k).1 h)
    have hn : (CycRec.trunc s ρ).nth k = none := by
      by_contra hne
      obtain ⟨e, he⟩ := Option.ne_none_iff_exists'.1 hne
      exact hkm (lt_num_of_nth he)
    rw [hn, ite_eq_right hs]

omit [MeasurableSpace I] in
theorem cum_trunc_eq (junk : CycEntry I d) (s : ℝ≥0) (ρ : CycRec I d) {j : ℕ}
    (hj : j ∈ ρ.surv s) : (CycRec.trunc s ρ).cum j = ρ.cum j := by
  unfold CycRec.cum
  refine Finset.sum_congr rfl fun i hi => ?_
  have hij : i < j := Finset.mem_range.1 hi
  have his : i ∈ ρ.surv s := CycRec.surv_downward s ρ i j hij.le hj
  have hcs : ρ.cum (i + 1) ≤ s := (ρ.cum_mono (Nat.succ_le_of_lt hij)).trans hj.2
  have hn := trunc_nth junk s ρ i
  rw [ite_eq_left his] at hn
  unfold CycRec.truncEntry at hn
  rw [ite_eq_left hcs] at hn
  unfold CycRec.lenAt
  rw [hn]
  have hlt : (i : ℕ∞) < ρ.num := his.1
  obtain ⟨e, he⟩ := nth_of_lt_num hlt
  have hce : ρ.coord junk i = e := by unfold CycRec.coord; rw [he]; rfl
  rw [hce, he]

end CycRec


omit [MeasurableSpace I] in
theorem CycEntry.cut_cut (e : CycEntry I d) {a b : ℝ≥0∞} (h : b ≤ a) : (e.cut a).cut b = e.cut b :=
  Prod.ext rfl (Subtype.ext (CPath.cut_cut e.2.1 h))

namespace CycRec

open scoped Classical in
omit [MeasurableSpace I] in
theorem truncEntry_aux (e : CycEntry I d) {c : ℝ≥0∞} {s s' : ℝ≥0} (hss : (s' : ℝ≥0∞) ≤ s)
    (hcs : c ≤ (s : ℝ≥0∞)) :
    (if c + (if c + e.len ≤ (s : ℝ≥0∞) then e else e.cut ((s : ℝ≥0∞) - c)).len ≤ (s' : ℝ≥0∞)
      then (if c + e.len ≤ (s : ℝ≥0∞) then e else e.cut ((s : ℝ≥0∞) - c))
      else (if c + e.len ≤ (s : ℝ≥0∞) then e else e.cut ((s : ℝ≥0∞) - c)).cut ((s' : ℝ≥0∞) - c)) =
    if c + e.len ≤ (s' : ℝ≥0∞) then e else e.cut ((s' : ℝ≥0∞) - c) := by
  by_cases h1 : c + e.len ≤ (s : ℝ≥0∞)
  · simp only [h1, ite_true]
  · simp only [h1, ite_false]
    have h2 : ¬ c + e.len ≤ (s' : ℝ≥0∞) := fun h => h1 (h.trans hss)
    rw [ite_eq_right h2, CycEntry.len_cut, add_tsub_cancel_of_le hcs]
    by_cases h3 : (s : ℝ≥0∞) ≤ s'
    · have : (s : ℝ≥0∞) = s' := le_antisymm h3 hss
      rw [ite_eq_left h3, this]
    · rw [ite_eq_right h3]
      exact CycEntry.cut_cut e (tsub_le_tsub_right hss c)

open scoped Classical in
/-- `Trunc_{s'}(Trunc_s(ρ)) = Trunc_{s'}(ρ)` for `s' ≤ s`. -/
theorem trunc_trunc [Countable I] [MeasurableSingletonClass I] (junk : CycEntry I d) {s s' : ℝ≥0}
    (h : s' ≤ s) (ρ : CycRec I d) :
    CycRec.trunc s' (CycRec.trunc s ρ) = CycRec.trunc s' ρ := by
  refine CycSchemeEnv.CycRec.ext_nth' fun k => ?_
  rw [trunc_nth junk, trunc_nth junk]
  obtain ⟨m, hm, hiff, hcoord, -⟩ := CycRec.trunc_spec junk s ρ
  have hss : (s' : ℝ≥0∞) ≤ s := by exact_mod_cast h
  by_cases hk : k ∈ ρ.surv s'
  · have hks : k ∈ ρ.surv s := ⟨hk.1, hk.2.trans hss⟩
    have hcum := cum_trunc_eq junk s ρ hks
    have hk' : k ∈ (CycRec.trunc s ρ).surv s' := by
      refine ⟨?_, by rw [hcum]; exact hk.2⟩
      rw [hm]; exact (hiff k).2 hks
    rw [ite_eq_left hk', ite_eq_left hk]
    congr 1
    have hco : (CycRec.trunc s ρ).coord junk k = CycRec.truncEntry s ρ k (ρ.coord junk k) :=
      hcoord k hks
    have hlenA : ρ.lenAt k = (ρ.coord junk k).len := by
      rw [CycRec.lenAt_eq junk, ite_eq_left hks.1]
    have hlenB : (CycRec.trunc s ρ).lenAt k = (CycRec.truncEntry s ρ k (ρ.coord junk k)).len := by
      rw [CycRec.lenAt_eq junk, ite_eq_left (by rw [hm]; exact (hiff k).2 hks), hco]
    have hc1 : ρ.cum (k + 1) = ρ.cum k + (ρ.coord junk k).len := by
      unfold CycRec.cum; rw [Finset.sum_range_succ, hlenA]
    have hc2 : (CycRec.trunc s ρ).cum (k + 1) =
        ρ.cum k + (CycRec.truncEntry s ρ k (ρ.coord junk k)).len := by
      have : (CycRec.trunc s ρ).cum k = ρ.cum k := hcum
      unfold CycRec.cum at this ⊢
      rw [Finset.sum_range_succ, this, hlenB]
    have hE' : CycRec.truncEntry s ρ k (ρ.coord junk k) =
        if ρ.cum k + (ρ.coord junk k).len ≤ (s : ℝ≥0∞) then ρ.coord junk k
        else (ρ.coord junk k).cut ((s : ℝ≥0∞) - ρ.cum k) := by
      unfold CycRec.truncEntry; rw [hc1]
    rw [hco]
    have e1 : CycRec.truncEntry s' (CycRec.trunc s ρ) k (CycRec.truncEntry s ρ k (ρ.coord junk k)) =
        if (CycRec.trunc s ρ).cum (k + 1) ≤ (s' : ℝ≥0∞) then
          CycRec.truncEntry s ρ k (ρ.coord junk k)
        else (CycRec.truncEntry s ρ k (ρ.coord junk k)).cut
          ((s' : ℝ≥0∞) - (CycRec.trunc s ρ).cum k) := rfl
    have e2 : CycRec.truncEntry s' ρ k (ρ.coord junk k) =
        if ρ.cum (k + 1) ≤ (s' : ℝ≥0∞) then ρ.coord junk k
        else (ρ.coord junk k).cut ((s' : ℝ≥0∞) - ρ.cum k) := rfl
    rw [e1, e2, hc2, hcum, hc1, hE']
    exact truncEntry_aux _ hss (hk.2.trans hss)
  · have hk' : k ∉ (CycRec.trunc s ρ).surv s' := by
      intro hk'
      have hks : k ∈ ρ.surv s := by
        have := (hiff k).1 (by rw [← hm]; exact hk'.1)
        exact this
      have hcum := cum_trunc_eq junk s ρ hks
      exact hk ⟨hks.1, by rw [← hcum]; exact hk'.2⟩
    rw [ite_eq_right hk', ite_eq_right hk]

end CycRec

end ElboimSly.Cyclic

end
