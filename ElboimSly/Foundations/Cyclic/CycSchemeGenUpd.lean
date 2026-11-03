/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycSchemeGenAt
public import ElboimSly.Foundations.Cyclic.CycSchemeEnvCore
public import Mathlib

/-!
# Generic update lemmas of the scheme (port of `CycSchemeEnvUpd`)

The environment scheme (b), the driving scheme (c).

`GStep P sc rl k r ρ o` collects what the correctness proof of a step must provide: the path of walk `k`
is constant on `[r, r + s*)` with left limit `p(r)` at `r + s*`, and the new vertex of the scheme is
`p(r + s*)`. Given this, the new entry, the stopping test, and the update are as in the recursion
of world-lines of a plan; joint exploration filtration (a) (`upd_notStop`, `upd_stop_end`, `upd_stop_next`).
-/

@[expose] public section

open MeasureTheory Set Filter Topology ElboimSly.Circle
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic
namespace CycSchemeGen
open ElboimSly.Cyclic.CycSchemeEnv (candAbs cut_add_eq_extend le_jt_add_D jt_cnt_succ_eq lt_jt_of_fn_eq T_mem_cand_iff cand_ge hOf_le_hDl sStar_le_h)
variable {I : Type*} [MeasurableSpace I] [Countable I] [MeasurableSingletonClass I] {d : ℕ} {β : ℝ} [Fact (0 < β)]
variable {P : CycPlan I d β} {sc : ℝ≥0∞} {rl : PathRule I d}
variable {k : ℕ} {r : ℝ≥0} {ρ : CycRec I d} {o : Outcome (CycS I d β)}

/-- The outputs of the correctness analysis of one step. -/
structure GStep (P : CycPlan I d β) (sc : ℝ≥0∞) (rl : PathRule I d) (k : ℕ) (r : ℝ≥0)
    (ρ : CycRec I d) (o : Outcome (CycS I d β)) : Prop where
  const : ∀ t, r ≤ t → t < r + CycScheme.sStar P sc (ρ, false) o →
    (gpth P rl k).1.fn t = (gpth P rl k).1.fn r
  left : 0 < CycScheme.sStar P sc (ρ, false) o →
    (gpth P rl k).1.left (r + CycScheme.sStar P sc (ρ, false) o) = (gpth P rl k).1.fn r
  newV : CycScheme.newV P sc (ρ, false) o = (gpth P rl k).1.fn (r + CycScheme.sStar P sc (ρ, false) o)
  marked : ¬ CycScheme.stops P sc (ρ, false) o →
    ((CycScheme.sStar P sc (ρ, false) o : ℝ≥0) : ℝ≥0∞) ≠
      CycScheme.hGl sc ρ (CycScheme.cur P (ρ, false)) →
    0 < CycScheme.sStar P sc (ρ, false) o ∧
      ((r + CycScheme.sStar P sc (ρ, false) o) ∈ CDisc (gpth P rl k).1.fn ∨
        ∃ m : ℕ, ((r + CycScheme.sStar P sc (ρ, false) o : ℝ≥0) : ℝ) = β * m)

theorem quiet_facts_of (hs : GStep P sc rl k r ρ o) :
    (∀ t, r ≤ t → t < r + CycScheme.sStar P sc (ρ, false) o →
        (gpth P rl k).1.fn t = (gpth P rl k).1.fn r) ∧
      (0 < CycScheme.sStar P sc (ρ, false) o →
        (gpth P rl k).1.left (r + CycScheme.sStar P sc (ρ, false) o) = (gpth P rl k).1.fn r) :=
  ⟨hs.const, hs.left⟩

/-- The initial entry of the recursion is the cut of the path of its walk at `0`. -/
def ZeroRule (P : CycPlan I d β) (rl : PathRule I d) : Prop :=
  ∀ k ρ, (P.start k ρ).newEntry = (P.start k ρ, (rl k ρ).cut ((0 : ℝ≥0) : ℝ≥0∞))

omit [Countable I] [MeasurableSingletonClass I] [Fact (0 < β)] in
/-- The stopping candidates of walk `k` are `candAbs` of the decision and deadline at each `ρ̂_a`. -/
theorem cand_eq (P : CycPlan I d β) (rl : PathRule I d) (k : ℕ) :
    gcand P rl k = candAbs (gpth P rl k).1
      (fun b => P.st k (P.hatRec k (P.ideal (rl) k) (gpth P rl k) b) = true)
      (fun b => P.dl k (P.hatRec k (P.ideal (rl) k) (gpth P rl k) b)) := rfl

omit [MeasurableSpace I] [Countable I] [MeasurableSingletonClass I] in
theorem setLast_snoc {k : ℕ} (g : CycRecN I d k) (e0 e : CycEntry I d) :
    CycRec.setLast e (Sum.inl ⟨k + 1, CycRec.snoc g e0⟩ : CycRec I d) =
      Sum.inl ⟨k + 1, CycRec.snoc g e⟩ := by
  show (Sum.inl ⟨k + 1, Function.update (CycRec.snoc g e0) (Fin.last k) e⟩ : CycRec I d) = _
  unfold CycRec.snoc
  congr 2
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp
  · rw [Function.update_of_ne (Fin.castSucc_lt_last j).ne]
    simp

theorem newEntry_eq (h : GAt P rl k r ρ) (hg : GStep P sc rl k r ρ o) :
    CycScheme.newEntry P sc (ρ, false) o =
      (gdat P rl k, (gpth P rl k).cut (((r + CycScheme.sStar P sc (ρ, false) o : ℝ≥0)) : ℝ≥0∞)) := by
  obtain ⟨hconst, hleft⟩ := quiet_facts_of hg
  unfold CycScheme.newEntry
  rw [h.data, h.time, h.cur, hg.newV]
  refine Prod.ext rfl (Subtype.ext ?_)
  show ((gpth P rl k).1.cut (r : ℝ≥0∞)).extend (r + CycScheme.sStar P sc (ρ, false) o) _ = _
  exact (cut_add_eq_extend (gpth P rl k).1 (gpth P rl k).2 r _ hconst hleft).symm

theorem newRec_eq (h : GAt P rl k r ρ) (hg : GStep P sc rl k r ρ o) :
    CycScheme.newRec P sc (ρ, false) o = Sum.inl ⟨k + 1, CycRec.snoc (P.ideal (rl) k)
      (gdat P rl k, (gpth P rl k).cut (((r + CycScheme.sStar P sc (ρ, false) o : ℝ≥0)) : ℝ≥0∞))⟩ := by
  unfold CycScheme.newRec
  rw [newEntry_eq h hg]
  show CycRec.setLast _ ρ = _
  rw [h.rec_eq, setLast_snoc]

omit [Countable I] [MeasurableSingletonClass I] [Fact (0 < β)] in
theorem pre_abs (h : GAt P rl k r ρ) :
    r = 0 ∨ ∀ c ∈ candAbs (gpth P rl k).1
      (fun b => P.st k (P.hatRec k (P.ideal (rl) k) (gpth P rl k) b) = true)
      (fun b => P.dl k (P.hatRec k (P.ideal (rl) k) (gpth P rl k) b)), (r : ℝ≥0∞) < c :=
  h.pre

theorem T_le_hDl (h : GAt P rl k r ρ) (_hg : GStep P sc rl k r ρ o) :
    ((r + CycScheme.sStar P sc (ρ, false) o : ℝ≥0) : ℝ≥0∞) ≤
      (gpth P rl k).1.jt ((gpth P rl k).1.cnt r) +
        P.dl k (P.hatRec k (P.ideal (rl) k) (gpth P rl k) ((gpth P rl k).1.cnt r)) := by
  have hrc := le_jt_add_D (gpth P rl k).1
    (fun b => P.st k (P.hatRec k (P.ideal (rl) k) (gpth P rl k) b) = true)
    (fun b => P.dl k (P.hatRec k (P.ideal (rl) k) (gpth P rl k) b)) r (pre_abs h)
  have h1 : ((CycScheme.sStar P sc (ρ, false) o : ℝ≥0) : ℝ≥0∞) ≤
      CycScheme.hDl P ρ (CycScheme.cur P (ρ, false)) :=
    (by exact_mod_cast sStar_le_h (P := P) (sc := sc) (ρ := ρ) o :
      ((CycScheme.sStar P sc (ρ, false) o : ℝ≥0) : ℝ≥0∞) ≤ CycScheme.hOf P sc (ρ, false)).trans
      (hOf_le_hDl ρ)
  rw [h.hDl] at h1
  have := (ENNReal.le_sub_iff_add_le_right ENNReal.coe_ne_top hrc).1 h1
  rw [ENNReal.coe_add, add_comm]
  exact this

theorem jump_facts (_h : GAt P rl k r ρ) (hg : GStep P sc rl k r ρ o) :
    ((r + CycScheme.sStar P sc (ρ, false) o : ℝ≥0) : ℝ≥0∞) ≤
        (gpth P rl k).1.jt ((gpth P rl k).1.cnt r + 1) ∧
      ((gpth P rl k).1.fn (r + CycScheme.sStar P sc (ρ, false) o) ≠ (gpth P rl k).1.fn r →
        (gpth P rl k).1.jt ((gpth P rl k).1.cnt r + 1) =
          ((r + CycScheme.sStar P sc (ρ, false) o : ℝ≥0) : ℝ≥0∞)) ∧
      ((gpth P rl k).1.fn (r + CycScheme.sStar P sc (ρ, false) o) = (gpth P rl k).1.fn r →
        ((r + CycScheme.sStar P sc (ρ, false) o : ℝ≥0) : ℝ≥0∞) <
          (gpth P rl k).1.jt ((gpth P rl k).1.cnt r + 1)) := by
  obtain ⟨hconst, hleft⟩ := quiet_facts_of hg
  have hj : (gpth P rl k).1.fn (r + CycScheme.sStar P sc (ρ, false) o) ≠ (gpth P rl k).1.fn r →
      (gpth P rl k).1.jt ((gpth P rl k).1.cnt r + 1) =
        ((r + CycScheme.sStar P sc (ρ, false) o : ℝ≥0) : ℝ≥0∞) :=
    fun hfn => jt_cnt_succ_eq (gpth P rl k).1 r _ hconst hleft hfn
  have hn : (gpth P rl k).1.fn (r + CycScheme.sStar P sc (ρ, false) o) = (gpth P rl k).1.fn r →
      ((r + CycScheme.sStar P sc (ρ, false) o : ℝ≥0) : ℝ≥0∞) <
        (gpth P rl k).1.jt ((gpth P rl k).1.cnt r + 1) :=
    fun hfn => lt_jt_of_fn_eq (gpth P rl k).1 r _ hconst hleft hfn
  refine ⟨?_, hj, hn⟩
  by_cases hfn : (gpth P rl k).1.fn (r + CycScheme.sStar P sc (ρ, false) o) = (gpth P rl k).1.fn r
  · exact (hn hfn).le
  · exact (hj hfn).ge

theorem stops_iff (h : GAt P rl k r ρ) (hg : GStep P sc rl k r ρ o) :
    CycScheme.stops P sc (ρ, false) o ↔
      ((r + CycScheme.sStar P sc (ρ, false) o : ℝ≥0) : ℝ≥0∞) ∈ gcand P rl k := by
  obtain ⟨hJ, hjump, hnojump⟩ := jump_facts h hg
  rw [cand_eq, T_mem_cand_iff (gpth P rl k).1 _ _ r _ (pre_abs h) hJ hjump hnojump]
  unfold CycScheme.stops
  rw [hg.newV, h.pos]
  by_cases hfn : (gpth P rl k).1.fn (r + CycScheme.sStar P sc (ρ, false) o) = (gpth P rl k).1.fn r
  · rw [ite_eq_right (not_not.2 hfn)]
    rw [h.hDl]
    have hrc := le_jt_add_D (gpth P rl k).1
      (fun b => P.st k (P.hatRec k (P.ideal (rl) k) (gpth P rl k) b) = true)
      (fun b => P.dl k (P.hatRec k (P.ideal (rl) k) (gpth P rl k) b)) r (pre_abs h)
    have key : ((CycScheme.sStar P sc (ρ, false) o : ℝ≥0) : ℝ≥0∞) =
        (gpth P rl k).1.jt ((gpth P rl k).1.cnt r) +
          P.dl k (P.hatRec k (P.ideal (rl) k) (gpth P rl k) ((gpth P rl k).1.cnt r)) - r ↔
        ((r + CycScheme.sStar P sc (ρ, false) o : ℝ≥0) : ℝ≥0∞) =
          (gpth P rl k).1.jt ((gpth P rl k).1.cnt r) +
          P.dl k (P.hatRec k (P.ideal (rl) k) (gpth P rl k) ((gpth P rl k).1.cnt r)) := by
      constructor
      · intro hs
        have := tsub_add_cancel_of_le hrc
        rw [← hs] at this
        rw [ENNReal.coe_add, add_comm]
        exact this
      · intro hs
        rw [ENNReal.coe_add] at hs
        rw [← hs, ENNReal.add_sub_cancel_left ENNReal.coe_ne_top]
    constructor
    · intro hs; right; exact ⟨hfn, key.1 hs⟩
    · rintro (⟨hne, _⟩ | ⟨_, hs⟩)
      · exact absurd hfn hne
      · exact key.2 hs
  · rw [ite_eq_left hfn]
    have hjt := hjump hfn
    have hhat : P.hatRec k (P.ideal (rl) k) (gpth P rl k) ((gpth P rl k).1.cnt r + 1) =
        CycRec.snoc (P.ideal (rl) k)
          (gdat P rl k, (gpth P rl k).cut (((r + CycScheme.sStar P sc (ρ, false) o : ℝ≥0)) : ℝ≥0∞)) := by
      unfold CycPlan.hatRec
      refine congrArg (CycRec.snoc _) (Prod.ext rfl (Subtype.ext ?_))
      show (gpth P rl k).1.cut ((gpth P rl k).1.jt ((gpth P rl k).1.cnt r + 1)) = _
      rw [hjt]
      rfl
    have hsd : (P.stOf (CycScheme.newRec P sc (ρ, false) o) = true ∨
        P.dlOf (CycScheme.newRec P sc (ρ, false) o) = 0) ↔
        (P.st k (P.hatRec k (P.ideal (rl) k) (gpth P rl k) ((gpth P rl k).1.cnt r + 1)) = true ∨
          P.dl k (P.hatRec k (P.ideal (rl) k) (gpth P rl k) ((gpth P rl k).1.cnt r + 1)) = 0) := by
      rw [newRec_eq h hg, hhat]
      rfl
    rw [hsd]
    constructor
    · intro hs; left; exact ⟨hfn, hs⟩
    · rintro (⟨_, hs⟩ | ⟨heq, _⟩)
      · exact hs
      · exact absurd heq hfn

theorem cand_lt_of_not_stops (h : GAt P rl k r ρ) (hg : GStep P sc rl k r ρ o)
    (hns : ¬ CycScheme.stops P sc (ρ, false) o) :
    ∀ c ∈ gcand P rl k, ((r + CycScheme.sStar P sc (ρ, false) o : ℝ≥0) : ℝ≥0∞) < c := by
  intro c hc
  have hge := cand_ge (gpth P rl k).1
    (fun b => P.st k (P.hatRec k (P.ideal (rl) k) (gpth P rl k) b) = true)
    (fun b => P.dl k (P.hatRec k (P.ideal (rl) k) (gpth P rl k) b)) r _ (pre_abs h)
    (jump_facts h hg).1 (T_le_hDl h hg) c hc
  refine lt_of_le_of_ne hge fun heq => hns ((stops_iff h hg).2 ?_)
  rw [heq]; exact hc

theorem sInf_cand_eq (h : GAt P rl k r ρ) (hg : GStep P sc rl k r ρ o)
    (hs : CycScheme.stops P sc (ρ, false) o) :
    sInf (gcand P rl k) = ((r + CycScheme.sStar P sc (ρ, false) o : ℝ≥0) : ℝ≥0∞) := by
  refine le_antisymm (sInf_le ((stops_iff h hg).1 hs)) (le_sInf ?_)
  exact cand_ge (gpth P rl k).1
    (fun b => P.st k (P.hatRec k (P.ideal (rl) k) (gpth P rl k) b) = true)
    (fun b => P.dl k (P.hatRec k (P.ideal (rl) k) (gpth P rl k) b)) r _ (pre_abs h)
    (jump_facts h hg).1 (T_le_hDl h hg)

omit [Countable I] [MeasurableSingletonClass I] [Fact (0 < β)] in
theorem num_eq (h : GAt P rl k r ρ) : ρ.num = ((k + 1 : ℕ) : ℕ∞) := by
  rw [h.rec_eq]; rfl

theorem upd_notStop (h : GAt P rl k r ρ) (hg : GStep P sc rl k r ρ o)
    (hns : ¬ CycScheme.stops P sc (ρ, false) o) :
    GAt P rl k (r + CycScheme.sStar P sc (ρ, false) o) (CycScheme.upd P sc (ρ, false) o).1 ∧
      (CycScheme.upd P sc (ρ, false) o).2 =
        decide (((CycScheme.sStar P sc (ρ, false) o : ℝ≥0) : ℝ≥0∞) =
          CycScheme.hGl sc ρ (CycScheme.cur P (ρ, false))) := by
  have hu : CycScheme.upd P sc (ρ, false) o =
      (CycScheme.newRec P sc (ρ, false) o, decide (((CycScheme.sStar P sc (ρ, false) o : ℝ≥0) : ℝ≥0∞) =
          CycScheme.hGl sc ρ (CycScheme.cur P (ρ, false)))) := by
    unfold CycScheme.upd
    simp [hns]
  rw [hu]
  refine ⟨⟨newRec_eq h hg, h.allFin, h.lt_K, Or.inr (cand_lt_of_not_stops h hg hns)⟩, rfl⟩

theorem E_eq_of_stops (h : GAt P rl k r ρ) (hg : GStep P sc rl k r ρ o)
    (hs : CycScheme.stops P sc (ρ, false) o) :
    P.E (rl) k = (gdat P rl k, (gpth P rl k).cut
      (((r + CycScheme.sStar P sc (ρ, false) o : ℝ≥0)) : ℝ≥0∞)) := by
  rw [E_eq', sInf_cand_eq h hg hs]

theorem upd_stop_end (h : GAt P rl k r ρ) (hg : GStep P sc rl k r ρ o)
    (hs : CycScheme.stops P sc (ρ, false) o) (hK : ¬ ((k + 1 : ℕ) : ℕ∞) < P.K) :
    CycScheme.upd P sc (ρ, false) o = (Sum.inl ⟨k + 1, P.ideal (rl) (k + 1)⟩, true) := by
  unfold CycScheme.upd
  have hn := num_eq h
  simp only [Bool.false_eq_true, ite_false, hs, ite_true]
  rw [hn, ite_eq_right hK, newRec_eq h hg, ← E_eq_of_stops h hg hs]
  rfl

theorem upd_stop_next (hz : ZeroRule P rl) (h : GAt P rl k r ρ) (hg : GStep P sc rl k r ρ o)
    (hs : CycScheme.stops P sc (ρ, false) o) (hK : ((k + 1 : ℕ) : ℕ∞) < P.K) :
    (CycScheme.upd P sc (ρ, false) o).2 = false ∧
      GAt P rl (k + 1) 0 (CycScheme.upd P sc (ρ, false) o).1 := by
  have hu : CycScheme.upd P sc (ρ, false) o =
      (CycRec.push (P.startOf (CycScheme.newRec P sc (ρ, false) o)).newEntry
        (CycScheme.newRec P sc (ρ, false) o), false) := by
    unfold CycScheme.upd
    have hn := num_eq h
    simp only [Bool.false_eq_true, ite_false, hs, ite_true]
    rw [hn, ite_eq_left hK]
  rw [hu]
  refine ⟨rfl, ?_, ?_, ?_, Or.inl rfl⟩
  · rw [newRec_eq h hg, ← E_eq_of_stops h hg hs]
    have hne : (P.start (k + 1) (CycRec.snoc (P.ideal (rl) k) (P.E (rl) k))).newEntry =
        (gdat P rl (k + 1), (gpth P rl (k + 1)).cut ((0 : ℝ≥0) : ℝ≥0∞)) :=
      hz _ _
    show (Sum.inl ⟨k + 1 + 1, CycRec.snoc (CycRec.snoc (P.ideal (rl) k) (P.E (rl) k))
      (P.start (k + 1) (CycRec.snoc (P.ideal (rl) k) (P.E (rl) k))).newEntry⟩ : CycRec I d) = _
    rw [hne]
    rfl
  · intro i hi
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hlt | heq
    · exact h.allFin i hlt
    · rw [heq, E_eq_of_stops h hg hs]
      show ((gpth P rl k).1.cut _).len < ⊤
      rw [CPath.cut_len]; exact ENNReal.coe_lt_top
  · exact_mod_cast hK

omit [Countable I] [MeasurableSingletonClass I] [Fact (0 < β)] in
theorem gAt_init (hz : ZeroRule P rl) (hK : 0 < P.K) : GAt P rl 0 0 (CycScheme.init P).1 := by
  refine ⟨?_, fun i hi => absurd hi (Nat.not_lt_zero _), by exact_mod_cast hK, Or.inl rfl⟩
  have hne : (P.startOf (CycRec.empty : CycRec I d)).newEntry =
      (gdat P rl 0, (gpth P rl 0).cut ((0 : ℝ≥0) : ℝ≥0∞)) := hz _ _
  show (CycRec.empty.push (P.startOf (CycRec.empty : CycRec I d)).newEntry : CycRec I d) = _
  rw [hne]
  rfl


end CycSchemeGen
end ElboimSly.Cyclic

end
