/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Base.StepPath
public import Mathlib

/-!
# Causal recursion along the jumps of a step path

Supports the two-particle map (existence and uniqueness of the two-particle map).

`exists_unique_stepRec`: if `z` is a step path and `G r` is the identity for every `r` that is
not a discontinuity of `z`, then for every `b` there is a unique step path `y` with `y 0 = b` and
`y r = G r (y (r-))` for all `r > 0`.
-/

@[expose] public section

open Set Filter Topology Function
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Base

open ElboimSly.Cyclic

variable {V E : Type*} [MeasurableSpace E] [Countable E] [MeasurableSingletonClass E]

section Left

variable (p : CPath E)

omit [MeasurableSpace E] [Countable E] [MeasurableSingletonClass E] in
theorem cnt_zero : p.cnt 0 = 0 := by
  unfold CPath.cnt
  have : CDisc p.fn ∩ Iic 0 = ∅ := by
    ext r
    simp only [CDisc, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_Iic, Set.mem_empty_iff_false,
      iff_false, not_and]
    intro h1 h2
    exact absurd h2 (not_le.mpr h1.1)
  rw [this]; simp

omit [MeasurableSpace E] [Countable E] [MeasurableSingletonClass E] in
/-- Just left of `r > 0` the jump count equals `cnt r`, minus one if `r` is a jump. -/
theorem cnt_left {r : ℝ≥0} (hr : 0 < r) :
    ∃ t, t < r ∧ ∀ u, t < u → u < r →
      CDisc p.fn ∩ Iic u = (CDisc p.fn ∩ Iic r) \ {r} := by
  obtain ⟨t, htr, ht⟩ := (IsStepPath.mk p.rc p.fin).exists_left_gap hr
  refine ⟨t, htr, fun u htu hur => ?_⟩
  ext x
  simp only [mem_inter_iff, mem_Iic, Set.mem_sdiff, mem_singleton_iff]
  constructor
  · rintro ⟨hx, hxu⟩
    exact ⟨⟨hx, hxu.trans hur.le⟩, (hxu.trans_lt hur).ne⟩
  · rintro ⟨⟨hx, hxr⟩, hne⟩
    refine ⟨hx, ?_⟩
    by_contra hxu
    exact ht x hx (htu.trans (not_le.mp hxu)) (lt_of_le_of_ne hxr hne)

omit [MeasurableSpace E] [Countable E] [MeasurableSingletonClass E] in
theorem cnt_left_eq_of_notMem {r : ℝ≥0} (hr : 0 < r) (hJ : r ∉ CDisc p.fn) :
    ∃ t, t < r ∧ ∀ u, t < u → u < r → p.cnt u = p.cnt r := by
  obtain ⟨t, htr, h⟩ := cnt_left p hr
  refine ⟨t, htr, fun u htu hur => ?_⟩
  unfold CPath.cnt
  rw [h u htu hur, sdiff_singleton_eq_self (fun hh => hJ hh.1)]

omit [MeasurableSpace E] [Countable E] [MeasurableSingletonClass E] in
theorem cnt_left_eq_of_mem {r : ℝ≥0} (hr : 0 < r) (hJ : r ∈ CDisc p.fn) :
    ∃ t, t < r ∧ ∀ u, t < u → u < r → p.cnt u + 1 = p.cnt r := by
  obtain ⟨t, htr, h⟩ := cnt_left p hr
  refine ⟨t, htr, fun u htu hur => ?_⟩
  have hmem : r ∈ CDisc p.fn ∩ Iic r := ⟨hJ, le_rfl⟩
  have h1 : 1 ≤ (CDisc p.fn ∩ Iic r).ncard :=
    (Set.ncard_pos (p.fin r)).2 ⟨r, hmem⟩
  unfold CPath.cnt
  rw [h u htu hur, Set.ncard_sdiff_singleton_of_mem hmem]
  omega

omit [MeasurableSpace E] [Countable E] [MeasurableSingletonClass E] in
theorem cnt_lt_of_lt {r s : ℝ≥0} (hJ : r ∈ CDisc p.fn) (hs : s < r) : p.cnt s < p.cnt r := by
  unfold CPath.cnt
  have hsub : CDisc p.fn ∩ Iic s ⊆ (CDisc p.fn ∩ Iic r) \ {r} := fun x hx =>
    ⟨⟨hx.1, hx.2.trans hs.le⟩, fun hh => absurd (hh ▸ hx.2) (not_le.mpr hs)⟩
  have h1 := Set.ncard_le_ncard hsub ((p.fin r).sdiff)
  rw [Set.ncard_sdiff_singleton_of_mem (show r ∈ CDisc p.fn ∩ Iic r from ⟨hJ, le_rfl⟩)] at h1
  have h2 : 1 ≤ (CDisc p.fn ∩ Iic r).ncard :=
    (Set.ncard_pos (p.fin r)).2 ⟨r, hJ, le_rfl⟩
  omega

omit [MeasurableSpace E] [Countable E] [MeasurableSingletonClass E] in
theorem jt_cnt_eq {r : ℝ≥0} (hJ : r ∈ CDisc p.fn) : p.jt (p.cnt r) = (r : ℝ≥0∞) := by
  refine le_antisymm ((p.jt_le_iff _ _).2 le_rfl) ?_
  by_contra hlt
  push Not at hlt
  have hfin : p.jt (p.cnt r) < ⊤ := hlt.trans ENNReal.coe_lt_top
  have hs : (p.jt (p.cnt r)).toNNReal < r := by
    have : ((p.jt (p.cnt r)).toNNReal : ℝ≥0∞) < r := by
      rwa [ENNReal.coe_toNNReal hfin.ne]
    exact_mod_cast this
  have := p.cnt_ge_of_jt hfin
  exact absurd (cnt_lt_of_lt p hJ hs) (not_lt.mpr this)

end Left

section Rec

variable [TopologicalSpace V] [T2Space V]

/-- The sequence of values after `k` jumps. -/
noncomputable def jumpSeq (p : CPath E) (G : ℝ≥0 → V → V) (b : V) : ℕ → V
  | 0 => b
  | k + 1 => G (p.jt (k + 1)).toNNReal (jumpSeq p G b k)

/-- The explicit solution of the causal recursion. -/
noncomputable def recSol (p : CPath E) (G : ℝ≥0 → V → V) (b : V) (s : ℝ≥0) : V :=
  jumpSeq p G b (p.cnt s)

omit [TopologicalSpace V] [T2Space V] in
omit [MeasurableSpace E] [Countable E] [MeasurableSingletonClass E] in
theorem recSol_left (p : CPath E) (G : ℝ≥0 → V → V) (b : V)
    (_hG : ∀ r, r ∉ CDisc p.fn → ∀ w, G r w = w) {r : ℝ≥0} (hr : 0 < r) :
    (r ∈ CDisc p.fn → ∀ᶠ u in 𝓝[<] r, recSol p G b u = jumpSeq p G b (p.cnt r - 1)) ∧
    (r ∉ CDisc p.fn → ∀ᶠ u in 𝓝[<] r, recSol p G b u = recSol p G b r) := by
  constructor
  · intro hJ
    obtain ⟨t, htr, ht⟩ := cnt_left_eq_of_mem p hr hJ
    filter_upwards [Ioo_mem_nhdsLT htr] with u hu
    unfold recSol
    congr 1
    have := ht u hu.1 hu.2
    omega
  · intro hJ
    obtain ⟨t, htr, ht⟩ := cnt_left_eq_of_notMem p hr hJ
    filter_upwards [Ioo_mem_nhdsLT htr] with u hu
    unfold recSol
    rw [ht u hu.1 hu.2]

omit [MeasurableSpace E] [Countable E] [MeasurableSingletonClass E] in
theorem recSol_eq (p : CPath E) (G : ℝ≥0 → V → V) (b : V)
    (hG : ∀ r, r ∉ CDisc p.fn → ∀ w, G r w = w) {r : ℝ≥0} (hr : 0 < r) :
    recSol p G b r = G r (leftLim (recSol p G b) r) := by
  by_cases hJ : r ∈ CDisc p.fn
  · have h := (recSol_left p G b hG hr).1 hJ
    rw [IsStepPath.leftLim_eq hr h]
    have hk : p.cnt r = (p.cnt r - 1) + 1 := by
      have : 1 ≤ p.cnt r := by
        have := cnt_lt_of_lt p hJ (show (0 : ℝ≥0) < r from hr)
        omega
      omega
    unfold recSol
    rw [hk, jumpSeq, ← hk, jt_cnt_eq p hJ]
    simp
  · have h := (recSol_left p G b hG hr).2 hJ
    rw [IsStepPath.leftLim_eq hr h, hG r hJ]

omit [TopologicalSpace V] [T2Space V] in
omit [MeasurableSpace E] [Countable E] [MeasurableSingletonClass E] in
theorem recSol_isStepPath (p : CPath E) (G : ℝ≥0 → V → V) (b : V)
    (hG : ∀ r, r ∉ CDisc p.fn → ∀ w, G r w = w) : IsStepPath (recSol p G b) := by
  refine ⟨fun s => ?_, fun T => ?_⟩
  · obtain ⟨ε, hε, hc⟩ := p.cnt_rightCont s
    filter_upwards [Ico_mem_nhdsGE (show s < s + ε from lt_add_of_pos_right s hε)] with u hu
    unfold recSol
    rw [hc u hu.1 hu.2]
  · refine (p.fin T).subset fun r hr => ⟨?_, hr.2⟩
    by_contra hJ
    refine hr.1.2 ?_
    exact (recSol_left p G b hG hr.1.1).2 hJ

omit [MeasurableSpace E] [Countable E] [MeasurableSingletonClass E] in
theorem exists_unique_stepRec {z : ℝ≥0 → E} (hz : IsStepPath z) (G : ℝ≥0 → V → V)
    (hG : ∀ r, r ∉ CDisc z → ∀ w, G r w = w) (b : V) :
    ∃! y : ℝ≥0 → V, IsStepPath y ∧ y 0 = b ∧ ∀ r, 0 < r → y r = G r (leftLim y r) := by
  let p : CPath E := ⟨⊤, z, hz.rc, hz.fin, fun s s' h _ => by simp at h⟩
  have hGp : ∀ r, r ∉ CDisc p.fn → ∀ w, G r w = w := hG
  refine ⟨recSol p G b, ⟨recSol_isStepPath p G b hGp, ?_, fun r hr => recSol_eq p G b hGp hr⟩,
    ?_⟩
  · unfold recSol; rw [cnt_zero]; rfl
  · rintro y' ⟨hy', h0, hrec⟩
    have hy := recSol_isStepPath p G b hGp
    refine funext (real_induction (Q := fun s => y' s = recSol p G b s) ?_ ?_ ?_)
    · rw [h0]; unfold recSol; rw [cnt_zero]; rfl
    · intro r hr hev
      rw [hrec r hr, recSol_eq p G b hGp hr]
      congr 1
      have h2 := hy.eventually_left_leftLim hr
      exact IsStepPath.leftLim_eq hr ((hev.and h2).mono fun u hu => hu.1.trans hu.2) ▸ rfl
    · intro r hr
      filter_upwards [hy'.rc r, hy.rc r] with u h1 h2
      rw [h1, h2, hr]

end Rec

end ElboimSly.Paper.Base
