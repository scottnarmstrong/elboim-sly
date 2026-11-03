/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycTruncSpec
public import ElboimSly.Foundations.Cyclic.CycFirstEvents2
public import ElboimSly.Foundations.Cyclic.CycPiece
public import Mathlib

/-!
# Right-continuity of `s ↦ Trunc_s(ρ)`

Measurability of record functionals (the closing remark). As `s' ↓ s`, the number of entries, the data and
every coordinate `p(r)` of `Trunc_{s'}(ρ)` are eventually constant, and the lengths converge.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

theorem enat_ext_lt {a b : ℕ∞} (h : ∀ j : ℕ, (j : ℕ∞) < a ↔ (j : ℕ∞) < b) : a = b := by
  have key : ∀ a b : ℕ∞, (∀ j : ℕ, (j : ℕ∞) < a ↔ (j : ℕ∞) < b) → a ≤ b := by
    intro a b h
    cases b using ENat.recTopCoe with
    | top => exact le_top
    | coe c =>
      cases a using ENat.recTopCoe with
      | top => exact absurd ((h c).mp (ENat.natCast_lt_top c)) (lt_irrefl _)
      | coe c' =>
        by_contra hh
        push Not at hh
        exact absurd ((h c).mp (by exact_mod_cast hh)) (lt_irrefl _)
  exact le_antisymm (key a b h) (key b a fun j => (h j).symm)

variable {I : Type*} [MeasurableSpace I] {d : ℕ}

omit [MeasurableSpace I] in
/-- The cumulative lengths have no accumulation point from the right. -/
theorem CycRec.exists_cum_gap (ρ : CycRec I d) (s : ℝ≥0) :
    ∃ ε : ℝ≥0, 0 < ε ∧ ∀ k, ¬ ((s : ℝ≥0∞) < ρ.cum k ∧ ρ.cum k < s + ε) := by
  classical
  by_cases h : ∃ k, (s : ℝ≥0∞) < ρ.cum k
  · set k0 := Nat.find h with hk0
    have hk0s : (s : ℝ≥0∞) < ρ.cum k0 := Nat.find_spec h
    have hge : ∀ k, (s : ℝ≥0∞) < ρ.cum k → ρ.cum k0 ≤ ρ.cum k := fun k hk =>
      ρ.cum_mono (Nat.find_min' h hk)
    by_cases hT : ρ.cum k0 = ⊤
    · refine ⟨1, one_pos, fun k ⟨h1, h2⟩ => ?_⟩
      have := hge k h1
      rw [hT] at this
      rw [top_le_iff.mp this] at h2
      exact absurd h2 (by simp)
    · refine ⟨(ρ.cum k0).toNNReal - s, ?_, fun k ⟨h1, h2⟩ => ?_⟩
      · have : (s : ℝ≥0∞) < ((ρ.cum k0).toNNReal : ℝ≥0∞) := by
          rwa [ENNReal.coe_toNNReal hT]
        exact tsub_pos_of_lt (by exact_mod_cast this)
      · have h3 := hge k h1
        have h4 : (s : ℝ≥0∞) + (((ρ.cum k0).toNNReal - s : ℝ≥0) : ℝ≥0∞) = ρ.cum k0 := by
          have hle : s ≤ (ρ.cum k0).toNNReal := by
            have : (s : ℝ≥0∞) ≤ ((ρ.cum k0).toNNReal : ℝ≥0∞) := by
              rw [ENNReal.coe_toNNReal hT]; exact hk0s.le
            exact_mod_cast this
          rw [← ENNReal.coe_add, add_tsub_cancel_of_le hle, ENNReal.coe_toNNReal hT]
        rw [h4] at h2
        exact absurd h3 (not_le.mpr h2)
  · push Not at h
    exact ⟨1, one_pos, fun k hk => absurd (h k) (not_le.mpr hk.1)⟩

theorem CPath.cut_fn_eventually {V : Type*} (e : CPath V) (t r : ℝ≥0) :
    ∃ ε : ℝ≥0, 0 < ε ∧ ∀ u : ℝ≥0, t ≤ u → u < t + ε →
      (e.cut (u : ℝ≥0∞)).fn r = (e.cut (t : ℝ≥0∞)).fn r := by
  rcases le_or_gt r t with hrt | htr
  · refine ⟨1, one_pos, fun u htu _ => ?_⟩
    rw [CPath.fn_cut_of_le _ (by exact_mod_cast hrt.trans htu),
      CPath.fn_cut_of_le _ (by exact_mod_cast hrt)]
  · obtain ⟨u', hu', hsub⟩ := mem_nhdsGE_iff_exists_Ico_subset.mp (e.rc t)
    refine ⟨min (u' - t) (r - t), lt_min (tsub_pos_of_lt hu') (tsub_pos_of_lt htr),
      fun u htu hut => ?_⟩
    have hu1 : u < u' := by
      have hu'' : t < u' := hu'
      have : u < t + (u' - t) := lt_of_lt_of_le hut (by gcongr; exact min_le_left _ _)
      rwa [add_tsub_cancel_of_le hu''.le] at this
    have hu2 : u < r := by
      have : u < t + (r - t) := lt_of_lt_of_le hut (by gcongr; exact min_le_right _ _)
      rwa [add_tsub_cancel_of_le htr.le] at this
    rw [CPath.cut_fn, CPath.cut_fn, min_eq_right (by exact_mod_cast hu2.le),
      min_eq_right (by exact_mod_cast htr.le)]
    simp only [ENNReal.toNNReal_coe]
    exact hsub ⟨htu, hu1⟩

omit [MeasurableSpace I] in
theorem CycRec.trunc_num_eventually (junk : CycEntry I d) (ρ : CycRec I d) (s : ℝ≥0) :
    ∃ ε : ℝ≥0, 0 < ε ∧ ∀ s' : ℝ≥0, s ≤ s' → s' < s + ε →
      (CycRec.trunc s' ρ).num = (CycRec.trunc s ρ).num := by
  obtain ⟨ε, hε, hgap⟩ := ρ.exists_cum_gap s
  refine ⟨ε, hε, fun s' hs hs' => ?_⟩
  obtain ⟨m, hm, hiff, -⟩ := CycRec.trunc_spec junk s ρ
  obtain ⟨m', hm', hiff', -⟩ := CycRec.trunc_spec junk s' ρ
  have hsurv : ρ.surv s' = ρ.surv s := by
    ext k
    simp only [CycRec.surv, mem_ofPred_eq]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      by_contra hh
      push Not at hh
      exact hgap k ⟨hh, lt_of_le_of_lt h2 (by exact_mod_cast hs')⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, h2.trans (by exact_mod_cast hs)⟩
  rw [hm, hm']
  exact enat_ext_lt fun j => by rw [hiff', hiff, hsurv]

omit [MeasurableSpace I] in
theorem CycRec.trunc_coord_eventually (junk : CycEntry I d) (ρ : CycRec I d) (s : ℝ≥0) (j : ℕ) (r : ℝ≥0) :
    ∃ ε : ℝ≥0, 0 < ε ∧ ∀ s' : ℝ≥0, s ≤ s' → s' < s + ε →
      ((CycRec.trunc s' ρ).coord junk j).data = ((CycRec.trunc s ρ).coord junk j).data ∧
      ((CycRec.trunc s' ρ).coord junk j).path.fn r = ((CycRec.trunc s ρ).coord junk j).path.fn r := by
  classical
  obtain ⟨ε0, hε0, hgap⟩ := ρ.exists_cum_gap s
  have hsurv : ∀ s' : ℝ≥0, s ≤ s' → s' < s + ε0 → ρ.surv s' = ρ.surv s := fun s' hs hs' => by
    ext k
    simp only [CycRec.surv, mem_ofPred_eq]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      by_contra hh
      push Not at hh
      exact hgap k ⟨hh, lt_of_le_of_lt h2 (by exact_mod_cast hs')⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, h2.trans (by exact_mod_cast hs)⟩
  by_cases hj : j ∈ ρ.surv s
  · set e := ρ.coord junk j with he
    by_cases hc : ρ.cum (j + 1) ≤ s
    · refine ⟨ε0, hε0, fun s' hs hs' => ?_⟩
      obtain ⟨-, -, -, hco, -⟩ := CycRec.trunc_spec junk s ρ
      obtain ⟨-, -, -, hco', -⟩ := CycRec.trunc_spec junk s' ρ
      rw [hco j hj, hco' j (hsurv s' hs hs' ▸ hj)]
      unfold CycRec.truncEntry
      rw [ite_eq_left hc, ite_eq_left (hc.trans (by exact_mod_cast hs))]
      exact ⟨rfl, rfl⟩
    · -- the entry that is cut at `s`
      have hcj : ρ.cum j ≤ s := hj.2
      have hcfin : ρ.cum j ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top hcj
      set c : ℝ≥0 := (ρ.cum j).toNNReal with hcdef
      have hcc : (c : ℝ≥0∞) = ρ.cum j := ENNReal.coe_toNNReal hcfin
      have hcs : c ≤ s := by
        have : (c : ℝ≥0∞) ≤ s := by rw [hcc]; exact hcj
        exact_mod_cast this
      obtain ⟨ε1, hε1, hrc⟩ := e.path.cut_fn_eventually (s - c) r
      refine ⟨min ε0 ε1, lt_min hε0 hε1, fun s' hs hs' => ?_⟩
      have hs1 : s' < s + ε0 := lt_of_lt_of_le hs' (by gcongr; exact min_le_left _ _)
      have hs2 : s' < s + ε1 := lt_of_lt_of_le hs' (by gcongr; exact min_le_right _ _)
      obtain ⟨-, -, -, hco, -⟩ := CycRec.trunc_spec junk s ρ
      obtain ⟨-, -, -, hco', -⟩ := CycRec.trunc_spec junk s' ρ
      rw [hco j hj, hco' j (hsurv s' hs hs1 ▸ hj)]
      unfold CycRec.truncEntry
      have hc' : ¬ ρ.cum (j + 1) ≤ s' := by
        intro h
        have h1 : (s : ℝ≥0∞) < ρ.cum (j + 1) := not_le.mp hc
        exact hgap (j + 1) ⟨h1, lt_of_le_of_lt h (by exact_mod_cast hs1)⟩
      rw [ite_eq_right hc, ite_eq_right hc']
      refine ⟨rfl, ?_⟩
      have e1 : ((s : ℝ≥0∞) - ρ.cum j) = ((s - c : ℝ≥0) : ℝ≥0∞) := by
        rw [ENNReal.coe_sub, hcc]
      have e2 : ((s' : ℝ≥0∞) - ρ.cum j) = ((s' - c : ℝ≥0) : ℝ≥0∞) := by
        rw [ENNReal.coe_sub, hcc]
      show (e.path.cut ((s' : ℝ≥0∞) - ρ.cum j)).fn r = (e.path.cut ((s : ℝ≥0∞) - ρ.cum j)).fn r
      rw [e1, e2]
      refine hrc (s' - c) (tsub_le_tsub_right hs c) ?_
      have h3 : s' - c = (s - c) + (s' - s) := by
        rw [add_comm, tsub_add_tsub_cancel hs hcs]
      rw [h3]
      have : s' - s < ε1 := (tsub_lt_iff_left hs).mpr hs2
      gcongr
  · -- the entry does not occur at `s`
    refine ⟨ε0, hε0, fun s' hs hs' => ?_⟩
    obtain ⟨-, -, -, -, hco⟩ := CycRec.trunc_spec junk s ρ
    obtain ⟨-, -, -, -, hco'⟩ := CycRec.trunc_spec junk s' ρ
    rw [hco j hj, hco' j (by rwa [hsurv s' hs hs'])]
    exact ⟨rfl, rfl⟩

theorem tsub_aux {c : ℝ≥0∞} {s s' : ℝ≥0} (hc : c ≤ s) (hs : s ≤ s') :
    (s' : ℝ≥0∞) - c ≤ ((s : ℝ≥0∞) - c) + ((s' - s : ℝ≥0) : ℝ≥0∞) := by
  have hcfin : c ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top hc
  lift c to ℝ≥0 using hcfin with c'
  have hc' : c' ≤ s := by exact_mod_cast hc
  rw [← ENNReal.coe_sub, ← ENNReal.coe_sub, ← ENNReal.coe_add, ENNReal.coe_le_coe, tsub_le_iff_right]
  refine le_of_eq ?_
  calc s' = s + (s' - s) := (add_tsub_cancel_of_le hs).symm
    _ = (s - c') + c' + (s' - s) := by rw [tsub_add_cancel_of_le hc']
    _ = (s - c') + (s' - s) + c' := by ring

omit [MeasurableSpace I] in
theorem CycRec.trunc_len_bounds (junk : CycEntry I d) (ρ : CycRec I d) {s s' : ℝ≥0} (hs : s ≤ s')
    {j : ℕ} (hj : j ∈ ρ.surv s) :
    ((CycRec.trunc s ρ).coord junk j).len ≤ ((CycRec.trunc s' ρ).coord junk j).len ∧
      ((CycRec.trunc s' ρ).coord junk j).len ≤
        ((CycRec.trunc s ρ).coord junk j).len + ((s' - s : ℝ≥0) : ℝ≥0∞) := by
  classical
  have hj' : j ∈ ρ.surv s' := ⟨hj.1, hj.2.trans (by exact_mod_cast hs)⟩
  obtain ⟨-, -, -, hco, -⟩ := CycRec.trunc_spec junk s ρ
  obtain ⟨-, -, -, hco', -⟩ := CycRec.trunc_spec junk s' ρ
  rw [hco j hj, hco' j hj']
  unfold CycRec.truncEntry
  have hss' : (s : ℝ≥0∞) ≤ s' := by exact_mod_cast hs
  have hsucc := CycRec.cum_succ_eq junk ρ j hj.1
  have haux := tsub_aux hj.2 hs
  have hcfin : ρ.cum j ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top hj.2
  by_cases hc : ρ.cum (j + 1) ≤ s
  · rw [ite_eq_left hc, ite_eq_left (hc.trans hss')]
    exact ⟨le_rfl, le_self_add⟩
  · by_cases hc' : ρ.cum (j + 1) ≤ s'
    · rw [ite_eq_right hc, ite_eq_left hc']
      have hl : (ρ.coord junk j).len ≤ (s' : ℝ≥0∞) - ρ.cum j := by
        rw [hsucc] at hc'
        exact ENNReal.le_sub_of_add_le_left hcfin hc'
      show ((ρ.coord junk j).cut ((s : ℝ≥0∞) - ρ.cum j)).len ≤ (ρ.coord junk j).len ∧
        (ρ.coord junk j).len ≤
          ((ρ.coord junk j).cut ((s : ℝ≥0∞) - ρ.cum j)).len + ((s' - s : ℝ≥0) : ℝ≥0∞)
      rw [CycEntry.len_cut]
      refine ⟨?_, hl.trans haux⟩
      rw [hsucc] at hc
      push Not at hc
      exact tsub_le_iff_left.mpr hc.le
    · rw [ite_eq_right hc, ite_eq_right hc']
      show ((ρ.coord junk j).cut ((s : ℝ≥0∞) - ρ.cum j)).len ≤
        ((ρ.coord junk j).cut ((s' : ℝ≥0∞) - ρ.cum j)).len ∧
        ((ρ.coord junk j).cut ((s' : ℝ≥0∞) - ρ.cum j)).len ≤
          ((ρ.coord junk j).cut ((s : ℝ≥0∞) - ρ.cum j)).len + ((s' - s : ℝ≥0) : ℝ≥0∞)
      rw [CycEntry.len_cut, CycEntry.len_cut]
      exact ⟨tsub_le_tsub_right hss' _, haux⟩

end ElboimSly.Cyclic

end
