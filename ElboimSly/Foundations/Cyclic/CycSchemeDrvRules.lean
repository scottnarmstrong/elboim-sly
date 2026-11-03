/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycSchemeDrvPoints
public import ElboimSly.Foundations.Cyclic.CycSchemeEnvNewV
public import ElboimSly.Foundations.Cyclic.CycSchemeEnvPath
public import Mathlib

/-!
# The driving scheme (c): the driven rules read off the record

The driving scheme (c), (i), (ii). For a record with `GAt P (drl P jx Ñ) k r ρ`, the
rules (D1′)–(D3′) of the driven path of walk `k` at the local time `r + t`, `0 < t ≤ β`, with the
left limit `p(r + t-) = w` of the path equal to its current position `w = p(r)`, are stated in
terms of the record `ρ` and the atoms of `Ñ`:

* `rule_ring_gAt`: a known ring `(ι, e, c_δ(r + t))` of `ρ` at an edge `e ∋ w` forces the path to
  move to the other end of the `edgeEnc`-least such edge (D1′);
* `rule_jump_gAt`: with no such ring, an atom of `Ñ` at `qpt v t` with an unexplored image moves
  the path to `w + v` (D2′);
* `rule_stay_gAt`: with no such ring and no such atom, the path stays at `w` (D3′).

`fn_const_of_step` is the abstract "quiet interval" argument: if at every time of `(r, r + S)` the
path does not move when its left limit is `p(r)`, it is constant on `[r, r + S)`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic
namespace CycSchemeGen
open SRW

variable {I : Type*} [MeasurableSpace I] [Countable I] [MeasurableSingletonClass I] {d : ℕ}
  {β : ℝ} [Fact (0 < β)] {J : Type} [MeasurableSpace J] [Countable J] [MeasurableSingletonClass J]
  {jx : ∀ k : ℕ, CycRecN I d k → J} {P : CycPlan I d β} {sc : ℝ≥0∞}
  {Ñ : Measure (DrvS d J)} {k : ℕ} {r : ℝ≥0} {ρ : CycRec I d}

/-! ### Jumps of the canonical walk -/

omit [Countable I] [MeasurableSingletonClass I] in
theorem jump_iff_atom
    (hgood : relabel {x : Dir d × J | x.2 = gj P jx Ñ k} Prod.fst Ñ ∈ goodSet d) (t : ℝ≥0)
    (hpos : 0 < ga P jx Ñ k + (r + t)) :
    (srwPath Ñ (gj P jx Ñ k)).1.left (ga P jx Ñ k + (r + t)) ≠
        (srwPath Ñ (gj P jx Ñ k)).1.fn (ga P jx Ñ k + (r + t)) ↔
      ∃ v : Dir d, AtomAt P jx Ñ k r v t := by
  rw [srw_jump_iff hgood hpos]
  simp only [AtomAt, qpt, Set.singleton_prod_singleton]

omit [Countable I] [MeasurableSingletonClass I] in
theorem jump_dir_of_atom
    (hgood : relabel {x : Dir d × J | x.2 = gj P jx Ñ k} Prod.fst Ñ ∈ goodSet d) {v : Dir d}
    {t : ℝ≥0} (hpos : 0 < ga P jx Ñ k + (r + t)) (hat : AtomAt P jx Ñ k r v t) :
    (srwPath Ñ (gj P jx Ñ k)).1.fn (ga P jx Ñ k + (r + t)) -
        (srwPath Ñ (gj P jx Ñ k)).1.left (ga P jx Ñ k + (r + t)) = v.vec := by
  refine srw_jump_dir hgood hpos ?_
  simpa only [AtomAt, qpt, Set.singleton_prod_singleton] using hat

/-! ### The driven rules at the local time `r + t` -/

omit [Countable I] [MeasurableSingletonClass I] [Countable J] [MeasurableSingletonClass J] in
theorem drvRule_at (h : GAt P (drl P jx Ñ) k r ρ) {t : ℝ≥0} (ht : 0 < t) :
    DrvRule β (CycRec.region β (Sum.inl ⟨k, P.ideal (drl P jx Ñ) k⟩ : CycRec I d))
      (CycRec.ringSet β (Sum.inl ⟨k, P.ideal (drl P jx Ñ) k⟩ : CycRec I d))
      (gdat P (drl P jx Ñ) k) (srwPath Ñ (gj P jx Ñ k)).1 (ga P jx Ñ k)
      (gpth P (drl P jx Ñ) k).1 t :=
  (isDriven_gpth h).2.2 t ht

omit [Countable J] [MeasurableSingletonClass J] in
omit [Countable I] [MeasurableSingletonClass I] in
theorem mem_Q_iff_fp (h : GAt P (drl P jx Ñ) k r ρ) {t : ℝ≥0} (ht0 : 0 < t) (htb : (t : ℝ) ≤ β)
    (e : Edge d) :
    ((gdat P (drl P jx Ñ) k).copy, (e, (gdat P (drl P jx Ñ) k).clock β (r + t))) ∈
        CycRec.ringSet β (Sum.inl ⟨k, P.ideal (drl P jx Ñ) k⟩ : CycRec I d) ∪
        drvQown β (gdat P (drl P jx Ñ) k) (gpth P (drl P jx Ñ) k).1 (r + t) ↔
      CycSchemeEnv.fp P ρ e t ∈ ρ.ringSet β := by
  have h1 : r < r + t := lt_add_of_pos_right r ht0
  have h2 : ((r + t : ℝ≥0) : ℝ) ≤ r + β := by push_cast; linarith
  rw [fp_eq' h e t]
  exact mem_Q_iff_ringSet h h1 h2 (y := ((gdat P (drl P jx Ñ) k).copy,
    (e, (gdat P (drl P jx Ñ) k).clock β (r + t)))) rfl

omit [Countable J] [MeasurableSingletonClass J] in
omit [Countable I] [MeasurableSingletonClass I] in
/-- (D1′): the `edgeEnc`-least ringing edge at `w` is the edge crossed. -/
theorem rule_ring_gAt (h : GAt P (drl P jx Ñ) k r ρ) {t : ℝ≥0} (ht0 : 0 < t)
    (htb : (t : ℝ) ≤ β)
    (hleft : (gpth P (drl P jx Ñ) k).1.left (r + t) = (gpth P (drl P jx Ñ) k).1.fn r)
    {e1 : Edge d} (he1 : Edge.Mem ((gpth P (drl P jx Ñ) k).1.fn r) e1)
    (hr : CycSchemeEnv.fp P ρ e1 t ∈ ρ.ringSet β)
    (hmin : ∀ e' : Edge d, Edge.Mem ((gpth P (drl P jx Ñ) k).1.fn r) e' →
      CycSchemeEnv.fp P ρ e' t ∈ ρ.ringSet β → edgeEnc e1 ≤ edgeEnc e') :
    (gpth P (drl P jx Ñ) k).1.fn (r + t) =
      edgeOther ((gpth P (drl P jx Ñ) k).1.fn r) e1 := by
  have hpos : 0 < r + t := lt_of_le_of_lt bot_le (lt_add_of_pos_right r ht0)
  have hQ := fun e => mem_Q_iff_fp h ht0 htb e
  obtain ⟨d1, -, -⟩ := drvRule_at h hpos
  rw [hleft] at d1
  have := d1 e1 he1 ((hQ e1).2 hr) (fun e' he' hq' => hmin e' he' ((hQ e').1 hq'))
  exact (CycSchemeEnv.edgeOther_eq this).symm

/-- The condition "no ring of `ρ` at the front at time `t` at an edge at `w`". -/
def NoRing (P : CycPlan I d β) (ρ : CycRec I d) (w : Fin d → ℤ) (t : ℝ≥0) : Prop :=
  ∀ e : Edge d, Edge.Mem w e → CycSchemeEnv.fp P ρ e t ∉ ρ.ringSet β

omit [Countable J] [MeasurableSingletonClass J] in
omit [Countable I] [MeasurableSingletonClass I] in
theorem noRing_iff (h : GAt P (drl P jx Ñ) k r ρ) {t : ℝ≥0} (ht0 : 0 < t) (htb : (t : ℝ) ≤ β)
    (w : Fin d → ℤ) :
    (¬ ∃ e : Edge d, Edge.Mem w e ∧ ((gdat P (drl P jx Ñ) k).copy,
      (e, (gdat P (drl P jx Ñ) k).clock β (r + t))) ∈ CycRec.ringSet β
        (Sum.inl ⟨k, P.ideal (drl P jx Ñ) k⟩ : CycRec I d) ∪
        drvQown β (gdat P (drl P jx Ñ) k) (gpth P (drl P jx Ñ) k).1 (r + t)) ↔
      NoRing P ρ w t := by
  unfold NoRing
  constructor
  · intro hn e he hm
    exact hn ⟨e, he, (mem_Q_iff_fp h ht0 htb e).2 hm⟩
  · rintro hn ⟨e, he, hm⟩
    exact hn e he ((mem_Q_iff_fp h ht0 htb e).1 hm)

omit [Countable J] [MeasurableSingletonClass J] in
omit [Countable I] [MeasurableSingletonClass I] in
theorem notMem_Z_iff (h : GAt P (drl P jx Ñ) k r ρ) {t : ℝ≥0} (ht0 : 0 < t) (htb : (t : ℝ) ≤ β)
    (e : Edge d) :
    ((gdat P (drl P jx Ñ) k).copy, (e, (gdat P (drl P jx Ñ) k).clock β (r + t))) ∉
        CycRec.region β (Sum.inl ⟨k, P.ideal (drl P jx Ñ) k⟩ : CycRec I d) ∪
        drvZown β (gdat P (drl P jx Ñ) k) (gpth P (drl P jx Ñ) k).1 (r + t) ↔
      CycSchemeEnv.fp P ρ e t ∉ ρ.region β := by
  have h1 : r < r + t := lt_add_of_pos_right r ht0
  have h2 : ((r + t : ℝ≥0) : ℝ) ≤ r + β := by push_cast; linarith
  rw [not_congr (mem_Z_iff_region h h1 h2 (y := ((gdat P (drl P jx Ñ) k).copy,
    (e, (gdat P (drl P jx Ñ) k).clock β (r + t)))) rfl), fp_eq' h e t]

omit [Countable I] [MeasurableSingletonClass I] in
/-- (D2′): with no ring, an atom of `Ñ` with an unexplored image moves the path. -/
theorem rule_jump_gAt
    (hgood : relabel {x : Dir d × J | x.2 = gj P jx Ñ k} Prod.fst Ñ ∈ goodSet d)
    (h : GAt P (drl P jx Ñ) k r ρ) {t : ℝ≥0} (ht0 : 0 < t) (htb : (t : ℝ) ≤ β)
    (hleft : (gpth P (drl P jx Ñ) k).1.left (r + t) = (gpth P (drl P jx Ñ) k).1.fn r)
    (hnr : NoRing P ρ ((gpth P (drl P jx Ñ) k).1.fn r) t) {v : Dir d}
    (hat : AtomAt P jx Ñ k r v t)
    (hfresh : CycSchemeEnv.fp P ρ (stepEdge ((gpth P (drl P jx Ñ) k).1.fn r) v) t ∉
      ρ.region β) :
    (gpth P (drl P jx Ñ) k).1.fn (r + t) = (gpth P (drl P jx Ñ) k).1.fn r + v.vec := by
  have hpos : 0 < r + t := lt_of_le_of_lt bot_le (lt_add_of_pos_right r ht0)
  have hposa : 0 < ga P jx Ñ k + (r + t) := lt_of_lt_of_le hpos le_add_self
  obtain ⟨-, d2, -⟩ := drvRule_at h hpos
  rw [hleft] at d2
  have hdir := jump_dir_of_atom hgood hposa hat
  have hjmp : (srwPath Ñ (gj P jx Ñ k)).1.left (ga P jx Ñ k + (r + t)) ≠
      (srwPath Ñ (gj P jx Ñ k)).1.fn (ga P jx Ñ k + (r + t)) :=
    (jump_iff_atom hgood t hposa).2 ⟨v, hat⟩
  rw [hdir] at d2
  refine d2 ((noRing_iff h ht0 htb _).2 hnr) hjmp ?_
  intro e he
  have : e = stepEdge ((gpth P (drl P jx Ñ) k).1.fn r) v := Subtype.ext he
  subst this
  exact (notMem_Z_iff h ht0 htb _).2 hfresh

omit [Countable I] [MeasurableSingletonClass I] in
/-- (D3′): with no ring and no atom with an unexplored image, the path stays. -/
theorem rule_stay_gAt
    (hgood : relabel {x : Dir d × J | x.2 = gj P jx Ñ k} Prod.fst Ñ ∈ goodSet d)
    (h : GAt P (drl P jx Ñ) k r ρ) {t : ℝ≥0} (ht0 : 0 < t) (htb : (t : ℝ) ≤ β)
    (hleft : (gpth P (drl P jx Ñ) k).1.left (r + t) = (gpth P (drl P jx Ñ) k).1.fn r)
    (hnr : NoRing P ρ ((gpth P (drl P jx Ñ) k).1.fn r) t)
    (hno : ∀ v : Dir d, AtomAt P jx Ñ k r v t →
      CycSchemeEnv.fp P ρ (stepEdge ((gpth P (drl P jx Ñ) k).1.fn r) v) t ∈ ρ.region β) :
    (gpth P (drl P jx Ñ) k).1.fn (r + t) = (gpth P (drl P jx Ñ) k).1.fn r := by
  have hpos : 0 < r + t := lt_of_le_of_lt bot_le (lt_add_of_pos_right r ht0)
  have hposa : 0 < ga P jx Ñ k + (r + t) := lt_of_lt_of_le hpos le_add_self
  obtain ⟨-, -, d3⟩ := drvRule_at h hpos
  rw [hleft] at d3
  have := d3 ((noRing_iff h ht0 htb _).2 hnr) ?_
  · exact this
  rintro ⟨hjmp, hfr⟩
  obtain ⟨v, hv⟩ := (jump_iff_atom hgood t hposa).1 hjmp
  have hdir := jump_dir_of_atom hgood hposa hv
  rw [hdir] at hfr
  have := hfr (stepEdge ((gpth P (drl P jx Ñ) k).1.fn r) v) rfl
  exact ((notMem_Z_iff h ht0 htb _).1 this) (hno v hv)

/-! ### Quiet intervals -/

/-- If at every time of `(r, r + S)` at which the left limit is `p(r)` the path does not move, then
it is constant on `[r, r + S)`. -/
theorem fn_const_of_step {p : CPath (Fin d → ℤ)} {r S : ℝ≥0}
    (hstep : ∀ t, r < t → t < r + S → p.left t = p.fn r → p.fn t = p.left t) :
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
  exact hdisc (hstep t0 ht0r (lt_of_le_of_lt ht0t1 ht1S) hleft).symm

theorem left_eq_of_step {p : CPath (Fin d → ℤ)} {r S : ℝ≥0} (hS : 0 < S)
    (hstep : ∀ t, r < t → t < r + S → p.left t = p.fn r → p.fn t = p.left t) :
    p.left (r + S) = p.fn r := by
  have hlt : r < r + S := lt_add_of_pos_right r hS
  refine p.left_eq_of_eventually (lt_of_le_of_lt bot_le hlt) ?_
  filter_upwards [Ioo_mem_nhdsLT hlt] with u hu
  exact fn_const_of_step hstep u hu.1.le hu.2

end CycSchemeGen
end ElboimSly.Cyclic

end
