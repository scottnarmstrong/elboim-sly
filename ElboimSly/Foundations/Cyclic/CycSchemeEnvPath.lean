/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycSchemeDef
public import ElboimSly.Foundations.Cyclic.CycPiece
public import Mathlib

/-!
# The environment scheme (b): path-level step lemmas

The environment scheme (b), (i)--(ii).

Pure path lemmas about a right-continuous path `p` with finitely many unit jumps that obeys a
*swap rule* with respect to a predicate `A t e` ("the edge `e` rings at time `t`"): on a stretch
`(r, r + S)` where no edge at `p(r)` rings the path stays constant (`fn_eq_of_quiet`), its left
limit at `r + S` is `p(r)`, and its value at `r + S` is the other end of the edge ringing there,
if any (`fn_end_ring`, `fn_end_quiet`). Consequently the truncation of `p` at `r + S` is the
guarded extension of the truncation at `r` (`cut_add_eq_extend`), which is how the update of
The environment scheme of a plan reproduces the environment path.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

namespace CycSchemeEnv

variable {d : ℕ}

theorem jt_zero (f : CPath (Fin d → ℤ)) : f.jt 0 = 0 := by
  have := (f.jt_le_iff 0 0).2 (Nat.zero_le _)
  simpa using this

/-- The swap rule, part 2: no edge at the left limit rings, so there is no jump. -/
def QuietRule (p : CPath (Fin d → ℤ)) (A : ℝ≥0 → Edge d → Prop) : Prop :=
  ∀ t, 0 < t → (¬ ∃ e, Edge.Mem (p.left t) e ∧ A t e) → p.fn t = p.left t

/-- The swap rule, part 1: an edge at the left limit that rings is the edge crossed. -/
def RingRule (p : CPath (Fin d → ℤ)) (A : ℝ≥0 → Edge d → Prop) : Prop :=
  ∀ t, 0 < t → ∀ e, Edge.Mem (p.left t) e → A t e → e.1 = s(p.left t, p.fn t)

variable {p : CPath (Fin d → ℤ)} {A : ℝ≥0 → Edge d → Prop}

/-- If no edge at `p(r)` rings in `(r, r + S)`, the path is constant on `[r, r + S)`. -/
theorem fn_eq_of_quiet (hsw : QuietRule p A) {r S : ℝ≥0}
    (hq : ∀ t, r < t → t < r + S → ∀ e, Edge.Mem (p.fn r) e → ¬ A t e) :
    ∀ t, r ≤ t → t < r + S → p.fn t = p.fn r := by
  by_contra hcon
  push Not at hcon
  obtain ⟨t1, hrt1, ht1S, hne⟩ := hcon
  set F : Set ℝ≥0 := (CDisc p.fn ∩ Iic t1) ∩ Ioi r with hF
  have hFfin : F.Finite := (p.fin t1).subset inter_subset_left
  have hFne : F.Nonempty := by
    by_contra hE
    rw [Set.not_nonempty_iff_eq_empty] at hE
    apply hne
    refine eq_of_no_disc p.rc hrt1 (fun s hs hd => ?_)
    have : s ∈ F := ⟨⟨hd, hs.2⟩, hs.1⟩
    rw [hE] at this
    exact this
  obtain ⟨t0, ht0F, hmin⟩ := Set.exists_min_image F id hFfin hFne
  have ht0r : r < t0 := ht0F.2
  have ht0t1 : t0 ≤ t1 := ht0F.1.2
  have hconst : ∀ u, r ≤ u → u < t0 → p.fn u = p.fn r := by
    intro u hru hut
    refine eq_of_no_disc p.rc hru (fun s hs hd => ?_)
    have hsF : s ∈ F := ⟨⟨hd, hs.2.trans (hut.le.trans ht0t1)⟩, hs.1⟩
    exact absurd (hmin s hsF) (not_le.mpr (lt_of_le_of_lt hs.2 hut))
  have ht0pos : 0 < t0 := lt_of_le_of_lt bot_le ht0r
  have hleft : p.left t0 = p.fn r := by
    refine p.left_eq_of_eventually ht0pos ?_
    filter_upwards [Ioo_mem_nhdsLT ht0r] with u hu using hconst u hu.1.le hu.2
  have hdisc : p.left t0 ≠ p.fn t0 := (p.mem_CDisc_iff ht0pos).1 ht0F.1.1
  by_contra _
  have hex : ∃ e, Edge.Mem (p.left t0) e ∧ A t0 e := by
    by_contra hno
    exact hdisc (hsw t0 ht0pos hno).symm
  obtain ⟨e, he, hAe⟩ := hex
  rw [hleft] at he
  exact hq t0 ht0r (lt_of_le_of_lt ht0t1 ht1S) e he hAe

/-- The left limit at `r + S` is `p(r)` if no edge at `p(r)` rings in `(r, r + S)`. -/
theorem left_eq_of_quiet (hsw : QuietRule p A) {r S : ℝ≥0} (hS : 0 < S)
    (hq : ∀ t, r < t → t < r + S → ∀ e, Edge.Mem (p.fn r) e → ¬ A t e) :
    p.left (r + S) = p.fn r := by
  have hlt : r < r + S := lt_add_of_pos_right r hS
  refine p.left_eq_of_eventually (lt_of_le_of_lt bot_le hlt) ?_
  filter_upwards [Ioo_mem_nhdsLT hlt] with u hu
  exact fn_eq_of_quiet hsw hq u hu.1.le hu.2

/-- The other end of an edge `e = {w, v}` is `v`. -/
theorem edgeOther_eq {w v : Fin d → ℤ} {e : Edge d} (h : e.1 = s(w, v)) : edgeOther w e = v := by
  have hw : w ∈ e.1 := by rw [h]; exact Sym2.mem_mk_left _ _
  unfold edgeOther
  rw [dite_eq_left hw]
  have h2 : s(w, Sym2.Mem.other hw) = s(w, v) := (Sym2.other_spec hw).trans h
  exact Sym2.congr_right.mp h2

/-- At `r + S`, if an edge at `p(r)` rings, the path moves to its other end. -/
theorem fn_end_ring (hring : RingRule p A) {r S : ℝ≥0} (hS : 0 < S)
    (hleft : p.left (r + S) = p.fn r) {e : Edge d} (he : Edge.Mem (p.fn r) e)
    (hA : A (r + S) e) : p.fn (r + S) = edgeOther (p.fn r) e := by
  have hpos : 0 < r + S := lt_of_le_of_lt bot_le (lt_add_of_pos_right r hS)
  have h1 := hring (r + S) hpos e (by rw [hleft]; exact he) hA
  rw [hleft] at h1
  exact (edgeOther_eq h1).symm

/-- At `r + S`, if no edge at `p(r)` rings, the path does not move. -/
theorem fn_end_quiet (hsw : QuietRule p A) {r S : ℝ≥0} (hS : 0 < S)
    (hleft : p.left (r + S) = p.fn r) (hno : ∀ e, Edge.Mem (p.fn r) e → ¬ A (r + S) e) :
    p.fn (r + S) = p.fn r := by
  have hpos : 0 < r + S := lt_of_le_of_lt bot_le (lt_add_of_pos_right r hS)
  rw [hsw (r + S) hpos (by rw [hleft]; rintro ⟨e, he, hA⟩; exact hno e he hA), hleft]

/-- The guarded value is the value itself at a point of the path (unit jumps). -/
theorem extVal_fn (q : CPath (Fin d → ℤ)) (hq : q.UnitJumps) (T : ℝ≥0) :
    q.extVal T (q.fn T) = q.fn T := by
  classical
  unfold CPath.extVal
  split_ifs with h
  · rfl
  · rcases eq_or_ne T 0 with rfl | hT
    · rw [CPath.left_zero, CPath.jv, jt_zero]
      simp
    · have hT' : 0 < T := pos_iff_ne_zero.mpr hT
      by_contra hne
      have hd : T ∈ CDisc q.fn := (q.mem_CDisc_iff hT').2 (fun hh => hne hh)
      have := hq T hd
      exact h ⟨hT', this⟩

theorem cut_left_of_gt (q : CPath (Fin d → ℤ)) {r T : ℝ≥0} (hrT : r < T) :
    (q.cut (r : ℝ≥0∞)).left T = q.fn r := by
  refine (q.cut (r : ℝ≥0∞)).left_eq_of_eventually (lt_of_le_of_lt bot_le hrT) ?_
  filter_upwards [Ioo_mem_nhdsLT hrT] with u hu
  rw [CPath.cut_fn]
  have : (min (u : ℝ≥0∞) (r : ℝ≥0∞)) = (r : ℝ≥0∞) := min_eq_right (by exact_mod_cast hu.1.le)
  rw [this]
  simp

/-- The truncation at `r + S` is the guarded extension of the truncation at `r`. -/
theorem cut_add_eq_extend (q : CPath (Fin d → ℤ)) (hq : q.UnitJumps) (r S : ℝ≥0)
    (hconst : ∀ t, r ≤ t → t < r + S → q.fn t = q.fn r)
    (hleft : 0 < S → q.left (r + S) = q.fn r) :
    q.cut ((r + S : ℝ≥0) : ℝ≥0∞) = (q.cut (r : ℝ≥0∞)).extend (r + S) (q.fn (r + S)) := by
  have hqc : (q.cut (r : ℝ≥0∞)).UnitJumps := hq.cut _
  have hval : (q.cut (r : ℝ≥0∞)).extVal (r + S) (q.fn (r + S)) = q.fn (r + S) := by
    rcases eq_zero_or_pos S with h0 | hS
    · subst h0
      rw [add_zero]
      have h1 : (q.cut (r : ℝ≥0∞)).fn r = q.fn r := by simp [CPath.cut_fn]
      have := extVal_fn _ hqc r
      rwa [h1] at this
    · classical
      have hL := cut_left_of_gt q (lt_add_of_pos_right r hS)
      unfold CPath.extVal
      split_ifs with hh
      · rfl
      · rw [hL]
        by_cases hv : q.fn (r + S) = q.fn r
        · rw [hv]
        · exfalso
          apply hh
          have hpos : 0 < r + S := lt_of_le_of_lt bot_le (lt_add_of_pos_right r hS)
          have hd : (r + S) ∈ CDisc q.fn := (q.mem_CDisc_iff hpos).2 (by rw [hleft hS]; exact fun h => hv h.symm)
          have := hq _ hd
          rw [hleft hS] at this
          exact ⟨hpos, by rw [hL]; exact this⟩
  refine CPath.ext' (by simp) (funext fun t => ?_)
  rw [CPath.cut_fn]
  rcases lt_or_ge t (r + S) with ht | ht
  · rw [CPath.extend_fn_of_lt _ _ _ ht, CPath.cut_fn]
    have e1 : min (t : ℝ≥0∞) ((r + S : ℝ≥0) : ℝ≥0∞) = t := min_eq_left (by exact_mod_cast ht.le)
    rw [e1]
    simp only [ENNReal.toNNReal_coe]
    rcases lt_or_ge t r with htr | htr
    · have e2 : min (t : ℝ≥0∞) (r : ℝ≥0∞) = t := min_eq_left (by exact_mod_cast htr.le)
      rw [e2]; simp
    · have e2 : min (t : ℝ≥0∞) (r : ℝ≥0∞) = r := min_eq_right (by exact_mod_cast htr)
      rw [e2]; simpa using hconst t htr ht
  · rw [CPath.extend_fn_of_le _ _ _ ht, hval]
    have e1 : min (t : ℝ≥0∞) ((r + S : ℝ≥0) : ℝ≥0∞) = ((r + S : ℝ≥0) : ℝ≥0∞) :=
      min_eq_right (by exact_mod_cast ht)
    rw [e1]; simp only [ENNReal.toNNReal_coe]

end CycSchemeEnv

end ElboimSly.Cyclic

end
