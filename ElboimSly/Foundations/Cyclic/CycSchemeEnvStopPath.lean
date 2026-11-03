/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycSchemeEnvPath
public import Mathlib

/-!
# The environment scheme (b): jump counts and stopping candidates

The environment scheme (b) (iii). Jump counting for a path that is constant on
`[r, r + s)` (`cnt_add_of_fn_eq`, `cnt_add_of_fn_ne`, `jt_cnt_succ_eq`, `lt_jt_of_fn_eq`), and the
characterisation of when `r + s` is a stopping candidate of world-lines, records, exploration plans (`candAbs`,
`cand_ge`, `T_mem_cand_iff`): the scheme's stop test is exactly this.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic
namespace CycSchemeEnv
variable {d : ℕ}

/-- No discontinuity of `p` in `(r, T)` when `p` is constant `= p(r)` on `[r, T)`. -/
theorem notMem_CDisc_of_const (p : CPath (Fin d → ℤ)) {r T x : ℝ≥0} (hrx : r < x) (hxT : x < T)
    (hconst : ∀ t, r ≤ t → t < T → p.fn t = p.fn r) : x ∉ CDisc p.fn := by
  intro hx
  apply hx.2
  filter_upwards [Ioo_mem_nhdsLT hrx] with u hu
  rw [hconst u hu.1.le (hu.2.trans hxT), hconst x hrx.le hxT]

theorem CDisc_inter_Iic_of_const (p : CPath (Fin d → ℤ)) (r s : ℝ≥0)
    (hconst : ∀ t, r ≤ t → t < r + s → p.fn t = p.fn r) :
    CDisc p.fn ∩ Iic (r + s) = (CDisc p.fn ∩ Iic r) ∪ (CDisc p.fn ∩ (({r + s} : Set ℝ≥0) \ Iic r)) := by
  ext x
  simp only [mem_inter_iff, mem_Iic, mem_union, Set.mem_sdiff, mem_singleton_iff, not_le]
  constructor
  · rintro ⟨hx, hxT⟩
    by_cases hxr : x ≤ r
    · exact Or.inl ⟨hx, hxr⟩
    · right
      have hxr' : r < x := not_le.1 hxr
      refine ⟨hx, ?_, hxr'⟩
      rcases hxT.lt_or_eq with hlt | heq
      · exact absurd hx (notMem_CDisc_of_const p hxr' hlt hconst)
      · exact heq
  · rintro (⟨hx, hxr⟩ | ⟨hx, rfl, hxr⟩)
    · exact ⟨hx, hxr.trans (by simp)⟩
    · exact ⟨hx, le_rfl⟩

theorem cnt_eq_of_lt (p : CPath (Fin d → ℤ)) {r T x : ℝ≥0}
    (hconst : ∀ t, r ≤ t → t < T → p.fn t = p.fn r) (hrx : r ≤ x) (hxT : x < T) :
    p.cnt x = p.cnt r := by
  unfold CPath.cnt
  congr 1
  ext y
  simp only [mem_inter_iff, mem_Iic]
  constructor
  · rintro ⟨hy, hyx⟩
    refine ⟨hy, ?_⟩
    by_contra hyr
    exact notMem_CDisc_of_const p (not_le.1 hyr) (lt_of_le_of_lt hyx hxT) hconst hy
  · rintro ⟨hy, hyr⟩
    exact ⟨hy, hyr.trans hrx⟩

theorem cnt_add_of_fn_eq (p : CPath (Fin d → ℤ)) (r s : ℝ≥0)
    (hconst : ∀ t, r ≤ t → t < r + s → p.fn t = p.fn r)
    (hleft : 0 < s → p.left (r + s) = p.fn r) (hfn : p.fn (r + s) = p.fn r) :
    p.cnt (r + s) = p.cnt r := by
  rcases eq_zero_or_pos s with rfl | hs
  · simp
  unfold CPath.cnt
  congr 1
  rw [CDisc_inter_Iic_of_const p r s hconst]
  have : CDisc p.fn ∩ (({r + s} : Set ℝ≥0) \ Iic r) = ∅ := by
    ext x
    simp only [Set.mem_sdiff, mem_inter_iff, mem_singleton_iff, mem_Iic, not_le, mem_empty_iff_false,
      iff_false, not_and]
    rintro hx rfl _
    have hpos : 0 < r + s := lt_of_le_of_lt bot_le (lt_add_of_pos_right r hs)
    rw [p.mem_CDisc_iff hpos, hleft hs, hfn] at hx
    exact hx rfl
  rw [this, union_empty]

theorem cnt_add_of_fn_ne (p : CPath (Fin d → ℤ)) (r s : ℝ≥0)
    (hconst : ∀ t, r ≤ t → t < r + s → p.fn t = p.fn r)
    (hleft : 0 < s → p.left (r + s) = p.fn r) (hfn : p.fn (r + s) ≠ p.fn r) :
    p.cnt (r + s) = p.cnt r + 1 := by
  have hs : 0 < s := by
    rcases eq_zero_or_pos s with rfl | hs
    · simp at hfn
    · exact hs
  unfold CPath.cnt
  rw [CDisc_inter_Iic_of_const p r s hconst]
  have hpos : 0 < r + s := lt_of_le_of_lt bot_le (lt_add_of_pos_right r hs)
  have : CDisc p.fn ∩ (({r + s} : Set ℝ≥0) \ Iic r) = {r + s} := by
    ext x
    simp only [Set.mem_sdiff, mem_inter_iff, mem_singleton_iff, mem_Iic, not_le]
    constructor
    · rintro ⟨_, h, _⟩; exact h
    · rintro rfl
      refine ⟨?_, rfl, lt_add_of_pos_right r hs⟩
      rw [p.mem_CDisc_iff hpos, hleft hs]
      exact fun h => hfn h.symm
  rw [this]
  have hdisj : Disjoint (CDisc p.fn ∩ Iic r) {r + s} := by
    rw [Set.disjoint_singleton_right]
    intro hx
    exact absurd hx.2 (not_le.2 (lt_add_of_pos_right r hs))
  rw [Set.ncard_union_eq hdisj ((p.fin r)) (Set.finite_singleton _), Set.ncard_singleton]

theorem lt_jt_cnt_succ (p : CPath (Fin d → ℤ)) (r : ℝ≥0) :
    (r : ℝ≥0∞) < p.jt (p.cnt r + 1) := by
  by_contra h
  have := (p.jt_le_iff (p.cnt r + 1) r).1 (not_lt.1 h)
  omega

theorem jt_cnt_succ_eq (p : CPath (Fin d → ℤ)) (r s : ℝ≥0)
    (hconst : ∀ t, r ≤ t → t < r + s → p.fn t = p.fn r)
    (hleft : 0 < s → p.left (r + s) = p.fn r) (hfn : p.fn (r + s) ≠ p.fn r) :
    p.jt (p.cnt r + 1) = ((r + s : ℝ≥0) : ℝ≥0∞) := by
  have hc := cnt_add_of_fn_ne p r s hconst hleft hfn
  have h1 : p.jt (p.cnt r + 1) ≤ ((r + s : ℝ≥0) : ℝ≥0∞) := (p.jt_le_iff _ _).2 hc.symm.le
  refine le_antisymm h1 ?_
  by_contra hlt
  push Not at hlt
  have hfin : p.jt (p.cnt r + 1) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top h1
  lift p.jt (p.cnt r + 1) to ℝ≥0 using hfin with x hx
  have hxT : x < r + s := by exact_mod_cast hlt
  have h2 := (p.jt_le_iff (p.cnt r + 1) x).1 (by rw [← hx])
  have hrx : r < x := by
    have := lt_jt_cnt_succ p r
    rw [← hx] at this
    exact_mod_cast this
  have h3 : p.cnt x = p.cnt r := cnt_eq_of_lt p hconst hrx.le hxT
  omega

theorem lt_jt_of_fn_eq (p : CPath (Fin d → ℤ)) (r s : ℝ≥0)
    (hconst : ∀ t, r ≤ t → t < r + s → p.fn t = p.fn r)
    (hleft : 0 < s → p.left (r + s) = p.fn r) (hfn : p.fn (r + s) = p.fn r) :
    ((r + s : ℝ≥0) : ℝ≥0∞) < p.jt (p.cnt r + 1) := by
  by_contra h
  have := (p.jt_le_iff (p.cnt r + 1) (r + s)).1 (not_lt.1 h)
  rw [cnt_add_of_fn_eq p r s hconst hleft hfn] at this
  omega

theorem jt_mono' (p : CPath (Fin d → ℤ)) {b b' : ℕ} (h : b ≤ b') : p.jt b ≤ p.jt b' := by
  by_cases htop : p.jt b' = ⊤
  · rw [htop]; exact le_top
  lift p.jt b' to ℝ≥0 using htop with x hx
  have h1 : p.jt b' ≤ (x : ℝ≥0∞) := by rw [← hx]
  have h2 := (p.jt_le_iff b' x).1 h1
  exact (p.jt_le_iff b x).2 (h.trans h2)

theorem jt_lt' (p : CPath (Fin d → ℤ)) {b b' : ℕ} (h : b < b') (htop : p.jt b' < ⊤) :
    p.jt b < p.jt b' := by
  have h1 : p.jt (b + 1) ≤ p.jt b' := jt_mono' p h
  exact lt_of_lt_of_le (p.jt_lt_succ (lt_of_le_of_lt h1 htop)) h1

theorem cnt_zero' (p : CPath (Fin d → ℤ)) : p.cnt 0 = 0 := by
  unfold CPath.cnt
  have : CDisc p.fn ∩ Iic (0 : ℝ≥0) = ∅ := by
    ext x; simp only [mem_inter_iff, mem_Iic, mem_empty_iff_false, iff_false, not_and]
    intro hx hx0
    have := hx.1
    have : x = 0 := le_antisymm hx0 bot_le
    simp_all
  rw [this]; simp

/-- The stopping candidates of a path, in terms of the decision and the deadline at each jump. -/
def candAbs (p : CPath (Fin d → ℤ)) (St : ℕ → Prop) (D : ℕ → ℝ≥0∞) : Set ℝ≥0∞ :=
  {t | ∃ a : ℕ, 1 ≤ a ∧ p.jt a < ⊤ ∧ St a ∧ t = p.jt a} ∪
    {t | ∃ a : ℕ, p.jt a < ⊤ ∧ t = p.jt a + D a ∧ t < p.jt (a + 1)}

variable (p : CPath (Fin d → ℤ)) (St : ℕ → Prop) (D : ℕ → ℝ≥0∞) (r s : ℝ≥0)

/-- `r ≤ ς + D`: a candidate cannot lie at or before `r` unless `r = 0`. -/
theorem le_jt_add_D (hpre : r = 0 ∨ ∀ c ∈ candAbs p St D, (r : ℝ≥0∞) < c) :
    (r : ℝ≥0∞) ≤ p.jt (p.cnt r) + D (p.cnt r) := by
  rcases hpre with rfl | hpre
  · simp
  by_cases hc : p.jt (p.cnt r) + D (p.cnt r) < p.jt (p.cnt r + 1)
  · have hfin : p.jt (p.cnt r) < ⊤ :=
      lt_of_le_of_lt ((p.jt_le_iff _ r).2 le_rfl) ENNReal.coe_lt_top
    exact (hpre _ (Or.inr ⟨p.cnt r, hfin, rfl, hc⟩)).le
  · exact (lt_jt_cnt_succ p r).le.trans (not_lt.1 hc)

theorem jt_cnt_le (p : CPath (Fin d → ℤ)) (r : ℝ≥0) : p.jt (p.cnt r) ≤ (r : ℝ≥0∞) :=
  (p.jt_le_iff _ r).2 le_rfl

/-- A candidate of the first kind at index `b ≤ cnt r` is excluded by `pre`. -/
theorem type1_gt (hpre : r = 0 ∨ ∀ c ∈ candAbs p St D, (r : ℝ≥0∞) < c) {b : ℕ} (hb1 : 1 ≤ b)
    (hbt : p.jt b < ⊤) (hSt : St b) : p.cnt r + 1 ≤ b := by
  by_contra hb
  have hba : b ≤ p.cnt r := by omega
  rcases hpre with rfl | hpre
  · rw [cnt_zero'] at hba; omega
  · have h1 := hpre _ (Or.inl ⟨b, hb1, hbt, hSt, rfl⟩)
    exact absurd (h1.trans_le ((jt_mono' p hba).trans (jt_cnt_le p r))) (lt_irrefl _)

/-- A candidate of the second kind at index `b < cnt r` is excluded by `pre`. -/
theorem type2_ge (hpre : r = 0 ∨ ∀ c ∈ candAbs p St D, (r : ℝ≥0∞) < c) {b : ℕ}
    (hbt : p.jt b < ⊤) (hlt : p.jt b + D b < p.jt (b + 1)) : p.cnt r ≤ b := by
  by_contra hb
  have hba : b + 1 ≤ p.cnt r := by omega
  have h1 : p.jt b + D b < r := hlt.trans_le ((jt_mono' p hba).trans (jt_cnt_le p r))
  rcases hpre with rfl | hpre
  · simp at h1
  · exact absurd (hpre _ (Or.inr ⟨b, hbt, rfl, hlt⟩)) (not_lt.2 h1.le)

theorem cand_ge (hpre : r = 0 ∨ ∀ c ∈ candAbs p St D, (r : ℝ≥0∞) < c)
    (hJ : ((r + s : ℝ≥0) : ℝ≥0∞) ≤ p.jt (p.cnt r + 1))
    (hD : ((r + s : ℝ≥0) : ℝ≥0∞) ≤ p.jt (p.cnt r) + D (p.cnt r)) :
    ∀ c ∈ candAbs p St D, ((r + s : ℝ≥0) : ℝ≥0∞) ≤ c := by
  rintro c (⟨b, hb1, hbt, hSt, rfl⟩ | ⟨b, hbt, rfl, hlt⟩)
  · exact hJ.trans (jt_mono' p (type1_gt p St D r hpre hb1 hbt hSt))
  · rcases lt_trichotomy b (p.cnt r) with hb | rfl | hb
    · exact absurd (type2_ge p St D r hpre hbt hlt) (by omega)
    · exact hD
    · exact hJ.trans ((jt_mono' p (by omega : p.cnt r + 1 ≤ b)).trans le_self_add)

theorem T_mem_cand_iff (hpre : r = 0 ∨ ∀ c ∈ candAbs p St D, (r : ℝ≥0∞) < c)
    (hJ : ((r + s : ℝ≥0) : ℝ≥0∞) ≤ p.jt (p.cnt r + 1))
    (hjump : p.fn (r + s) ≠ p.fn r → p.jt (p.cnt r + 1) = ((r + s : ℝ≥0) : ℝ≥0∞))
    (hnojump : p.fn (r + s) = p.fn r → ((r + s : ℝ≥0) : ℝ≥0∞) < p.jt (p.cnt r + 1)) :
    ((r + s : ℝ≥0) : ℝ≥0∞) ∈ candAbs p St D ↔
      (p.fn (r + s) ≠ p.fn r ∧ (St (p.cnt r + 1) ∨ D (p.cnt r + 1) = 0)) ∨
      (p.fn (r + s) = p.fn r ∧ ((r + s : ℝ≥0) : ℝ≥0∞) = p.jt (p.cnt r) + D (p.cnt r)) := by
  set T : ℝ≥0∞ := ((r + s : ℝ≥0) : ℝ≥0∞) with hT
  have hTfin : T ≠ ⊤ := ENNReal.coe_ne_top
  constructor
  · rintro (⟨b, hb1, hbt, hSt, hTb⟩ | ⟨b, hbt, hTb, hlt⟩)
    · have hba := type1_gt p St D r hpre hb1 hbt hSt
      have hJb := jt_mono' p hba
      have hJT : p.jt (p.cnt r + 1) = T := le_antisymm (hTb ▸ hJb) hJ
      have hfn : p.fn (r + s) ≠ p.fn r := fun hh => absurd (hnojump hh) (by rw [hJT]; exact lt_irrefl _)
      have hbeq : b = p.cnt r + 1 := by
        by_contra hne
        have : p.cnt r + 1 < b := by omega
        have := jt_lt' p this hbt
        rw [hJT, hTb] at this
        exact lt_irrefl _ this
      left
      exact ⟨hfn, Or.inl (hbeq ▸ hSt)⟩
    · rcases lt_trichotomy b (p.cnt r) with hb | rfl | hb
      · exact absurd (type2_ge p St D r hpre hbt (hTb ▸ hlt)) (by omega)
      · right
        refine ⟨?_, hTb⟩
        by_contra hne
        have := hjump hne
        rw [this] at hlt
        exact lt_irrefl _ hlt
      · have hba : p.cnt r + 1 ≤ b := by omega
        have h1 : T ≤ p.jt b := hJ.trans (jt_mono' p hba)
        have h2 : p.jt b ≤ T := by rw [hTb]; exact le_self_add
        have hjb : p.jt b = T := le_antisymm h2 h1
        have hD0 : D b = 0 := by
          have : p.jt b + D b = p.jt b + 0 := by rw [← hTb, hjb]; simp
          exact (ENNReal.add_right_inj (ne_top_of_lt hbt)).1 this
        have hJT : p.jt (p.cnt r + 1) = T := le_antisymm (hjb ▸ jt_mono' p hba) hJ
        have hfn : p.fn (r + s) ≠ p.fn r := fun hh => absurd (hnojump hh) (by rw [hJT]; exact lt_irrefl _)
        have hbeq : b = p.cnt r + 1 := by
          by_contra hne
          have : p.cnt r + 1 < b := by omega
          have := jt_lt' p this hbt
          rw [hJT, hjb] at this
          exact lt_irrefl _ this
        left
        exact ⟨hfn, Or.inr (hbeq ▸ hD0)⟩
  · rintro (⟨hfn, hst | hd⟩ | ⟨hfn, hTa⟩)
    · have hJT := hjump hfn
      exact Or.inl ⟨p.cnt r + 1, by omega, by rw [hJT]; exact lt_top_iff_ne_top.2 hTfin, hst, hJT.symm⟩
    · have hJT := hjump hfn
      refine Or.inr ⟨p.cnt r + 1, by rw [hJT]; exact lt_top_iff_ne_top.2 hTfin,
        by rw [hd, add_zero, hJT], ?_⟩
      by_cases htop : p.jt (p.cnt r + 1 + 1) = ⊤
      · rw [htop]; exact lt_top_iff_ne_top.2 hTfin
      · have := jt_lt' p (Nat.lt_succ_self (p.cnt r + 1)) (lt_top_iff_ne_top.2 htop)
        rw [hJT] at this
        exact this
    · refine Or.inr ⟨p.cnt r, lt_of_le_of_lt (jt_cnt_le p r) ENNReal.coe_lt_top, hTa, ?_⟩
      exact hnojump hfn

end CycSchemeEnv
end ElboimSly.Cyclic

end
