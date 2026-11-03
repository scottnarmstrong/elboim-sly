/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Frozen.Defs.IsRelaxedTimeWrt
public import ElboimSly.Frozen.Defs.VisitedSet
public import Mathlib

/-!
# First relaxed times are relaxed (pathwise part)

First relaxed times are relaxed and are stopping times (a) and (b).  Part (c) (stopping times) needs the measurability
of relaxed times and is stated separately.

* `relaxedSet β w a`: `S = {s ≥ a : s relaxed w.r.t. w|[a,s]}`.
* `mem_relaxedSet_of_rightLim`: closure from the right (a).
* `csInf_mem_relaxedSet`: `inf (S ∩ [c,∞)) ∈ S` when nonempty (a).
* `mem_relaxedSet_of_le`: on an interval of constancy `S` is an initial segment (b).
-/

@[expose] public section

open Filter Topology Set

namespace ElboimSly.Paper

variable {d : ℕ}

/-- First relaxed times are relaxed and are stopping times: `S = {s ≥ a : s is relaxed w.r.t. w|[a,s]}`. -/
def relaxedSet (β : ℝ) (w : ℝ → Fin d → ℤ) (a : ℝ) : Set ℝ :=
  {s | a ≤ s ∧ ElboimSly.IsRelaxedTimeWrt β w a s}

lemma visitedSet_eq_of_const {w : ℝ → Fin d → ℤ} {a s s' : ℝ} (has : a ≤ s) (hss : s ≤ s')
    (h : ∀ u ∈ Icc s s', w u = w s) :
    ElboimSly.visitedSet w a s' = ElboimSly.visitedSet w a s := by
  unfold ElboimSly.visitedSet
  apply Set.Subset.antisymm
  · rintro _ ⟨u, hu, rfl⟩
    by_cases hus : u ≤ s
    · exact ⟨u, ⟨hu.1, hus⟩, rfl⟩
    · exact ⟨s, ⟨has, le_rfl⟩, by rw [h u ⟨(not_le.1 hus).le, hu.2⟩]⟩
  · exact Set.image_mono (Set.Icc_subset_Icc le_rfl hss)

lemma box_finite (x : Fin d → ℤ) (r : ℝ) : {v : Fin d → ℤ | ‖v - x‖ ≤ r}.Finite := by
  have : {v : Fin d → ℤ | ‖v - x‖ ≤ r} = Metric.closedBall x r := by
    ext v; simp [dist_eq_norm]
  rw [this]
  exact (isCompact_closedBall x r).finite_of_discrete

lemma isHeavy_mono {w w' : ℝ → Fin d → ℤ} {a t t' : ℝ} {x : Fin d → ℤ} {r : ℝ}
    (h : ElboimSly.visitedSet w a t ⊆ ElboimSly.visitedSet w' a t')
    (hh : ElboimSly.IsHeavy w a t x r) : ElboimSly.IsHeavy w' a t' x r := by
  refine ⟨hh.1, hh.2.trans ?_⟩
  exact_mod_cast Set.ncard_le_ncard (Set.inter_subset_inter_right _ h)
    ((box_finite x r).subset Set.inter_subset_left)

/-- Part (b) of first relaxed times are relaxed and are stopping times: if `w` is constant on `[e, e')` and `s' ∈ S` lies in
it, then every `s''` with `max a e ≤ s'' ≤ s'` is in `S`. -/
theorem mem_relaxedSet_of_le {β : ℝ} {w : ℝ → Fin d → ℤ} {a e s' s'' : ℝ}
    (hconst : ∀ u ∈ Icc e s', w u = w e) (hs' : s' ∈ relaxedSet β w a)
    (hes'' : e ≤ s'') (has'' : a ≤ s'') (hle : s'' ≤ s') : s'' ∈ relaxedSet β w a := by
  have hw : w s'' = w s' := by
    rw [hconst s'' ⟨hes'', hle⟩, hconst s' ⟨hes''.trans hle, le_rfl⟩]
  refine ⟨has'', ?_, ?_⟩
  · intro r hr hh
    refine hs'.2.1 r hr (isHeavy_mono (w := w) (w' := w) (a := a) (t := s'') (t' := s') ?_ ?_)
    · exact Set.image_mono (Set.Icc_subset_Icc le_rfl hle)
    · rwa [hw] at hh
  · intro x hax hxs
    rw [hw]
    exact hs'.2.2 x hax (by linarith)

/-- Part (a) of first relaxed times are relaxed and are stopping times, at a single time: if `s ≥ a` is a right limit of points
of `S` (and `w` is right-continuous at `s`), then `s ∈ S`. -/
theorem mem_relaxedSet_of_rightLim {β : ℝ} {w : ℝ → Fin d → ℤ} {a s : ℝ} (has : a ≤ s)
    (hrc : ∀ᶠ u in 𝓝[≥] s, w u = w s)
    (hlim : ∀ ε > 0, ∃ s' ∈ relaxedSet β w a, s ≤ s' ∧ s' < s + ε) :
    s ∈ relaxedSet β w a := by
  obtain ⟨u', hu', hsub⟩ := (mem_nhdsGE_iff_exists_Ico_subset).1 hrc
  obtain ⟨s', hs', hss', hsu'⟩ := hlim (u' - s) (by simpa using hu')
  have hconst : ∀ u ∈ Icc s s', w u = w s := fun u hu =>
    hsub ⟨hu.1, by linarith [hu.2]⟩
  have hw : w s' = w s := hconst s' ⟨hss', le_rfl⟩
  refine ⟨has, ?_, ?_⟩
  · intro r hr hh
    refine hs'.2.1 r hr (isHeavy_mono (w := w) (w' := w) (a := a) (t := s) (t' := s') ?_ ?_)
    · rw [visitedSet_eq_of_const has hss' hconst]
    · rwa [hw]
  · intro x hax hxs
    rw [← hw]
    exact hs'.2.2 x hax (by linarith)

/-- Part (a) of first relaxed times are relaxed and are stopping times: `inf (S ∩ [c,∞)) ∈ S` when the set is nonempty. -/
theorem csInf_mem_relaxedSet {β : ℝ} {w : ℝ → Fin d → ℤ} {a c : ℝ}
    (hrc : ∀ s, a ≤ s → ∀ᶠ u in 𝓝[≥] s, w u = w s)
    (hne : (relaxedSet β w a ∩ Ici c).Nonempty) :
    sInf (relaxedSet β w a ∩ Ici c) ∈ relaxedSet β w a ∧
      c ≤ sInf (relaxedSet β w a ∩ Ici c) := by
  have hc : c ≤ sInf (relaxedSet β w a ∩ Ici c) := le_csInf hne fun x hx => hx.2
  have ha : a ≤ sInf (relaxedSet β w a ∩ Ici c) := le_csInf hne fun x hx => hx.1.1
  refine ⟨mem_relaxedSet_of_rightLim ha (hrc _ ha) fun ε hε => ?_, hc⟩
  obtain ⟨x, hx, hxlt⟩ := exists_lt_of_csInf_lt hne (by linarith :
    sInf (relaxedSet β w a ∩ Ici c) < sInf (relaxedSet β w a ∩ Ici c) + ε)
  exact ⟨x, hx.1, csInf_le ⟨c, fun y hy => hy.2⟩ hx, hxlt⟩

end ElboimSly.Paper
