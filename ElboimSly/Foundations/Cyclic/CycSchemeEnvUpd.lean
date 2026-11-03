/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycSchemeEnvNewV
public import ElboimSly.Foundations.Cyclic.CycSchemeEnvStopPath
public import Mathlib

/-!
# The environment scheme (b): the update reproduces the environment world-lines

The environment scheme (b) (i)--(v). For a good `ν`, a record with `EnvAt P ν k r ρ` and a good
outcome (`StepGood`):
* `newRec_eq`: the updated last entry is `(δ_k, P^ν_{δ_k}(· ∧ r + s*))`;
* `stops_iff`: the walk stops iff `r + s*` is a stopping candidate of world-lines, records, exploration plans;
* `upd_notStop`, `upd_stop_next`, `upd_stop_end`: the three cases of the update, in terms of the
  invariant `EnvAt` and the record `P.ideal` of the recursion of world-lines of a plan; joint exploration filtration (a);
* `envAt_init`: the initial state satisfies the invariant (for `K ≥ 1`).
-/

@[expose] public section

open MeasureTheory Set Filter Topology ElboimSly.Circle
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic
namespace CycSchemeEnv
variable {I : Type*} [MeasurableSpace I] [Countable I] [MeasurableSingletonClass I] {d : ℕ} {β : ℝ} [Fact (0 < β)]
variable {P : CycPlan I d β} {sc : ℝ≥0∞} {ν : Measure (I × RingSpace d β)}
variable {k : ℕ} {r : ℝ≥0} {ρ : CycRec I d} {o : Outcome (CycS I d β)}

omit [Countable I] [MeasurableSingletonClass I] [Fact (0 < β)] in
/-- The stopping candidates of walk `k` are `candAbs` of the decision and deadline at each `ρ̂_a`. -/
theorem cand_eq (P : CycPlan I d β) (ν : Measure (I × RingSpace d β)) (k : ℕ) :
    cand P ν k = candAbs (pth P ν k).1
      (fun b => P.st k (P.hatRec k (P.ideal (rule P ν) k) (pth P ν k) b) = true)
      (fun b => P.dl k (P.hatRec k (P.ideal (rule P ν) k) (pth P ν k) b)) := rfl

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

theorem newEntry_eq (hν : CycGood ν) (h : EnvAt P ν k r ρ) (hg : StepGood P sc ν ρ o) :
    CycScheme.newEntry P sc (ρ, false) o =
      (dat P ν k, (pth P ν k).cut (((r + CycScheme.sStar P sc (ρ, false) o : ℝ≥0)) : ℝ≥0∞)) := by
  obtain ⟨hconst, hleft⟩ := quiet_facts hν h hg
  unfold CycScheme.newEntry
  rw [h.data, h.time, h.cur, newV_eq hν h hg]
  refine Prod.ext rfl (Subtype.ext ?_)
  show ((pth P ν k).1.cut (r : ℝ≥0∞)).extend (r + CycScheme.sStar P sc (ρ, false) o) _ = _
  exact (cut_add_eq_extend (pth P ν k).1 (pth P ν k).2 r _ hconst hleft).symm

theorem newRec_eq (hν : CycGood ν) (h : EnvAt P ν k r ρ) (hg : StepGood P sc ν ρ o) :
    CycScheme.newRec P sc (ρ, false) o = Sum.inl ⟨k + 1, CycRec.snoc (P.ideal (rule P ν) k)
      (dat P ν k, (pth P ν k).cut (((r + CycScheme.sStar P sc (ρ, false) o : ℝ≥0)) : ℝ≥0∞))⟩ := by
  unfold CycScheme.newRec
  rw [newEntry_eq hν h hg]
  show CycRec.setLast _ ρ = _
  rw [h.rec_eq, setLast_snoc]

omit [Countable I] [MeasurableSingletonClass I] [Fact (0 < β)] in
theorem pre_abs (h : EnvAt P ν k r ρ) :
    r = 0 ∨ ∀ c ∈ candAbs (pth P ν k).1
      (fun b => P.st k (P.hatRec k (P.ideal (rule P ν) k) (pth P ν k) b) = true)
      (fun b => P.dl k (P.hatRec k (P.ideal (rule P ν) k) (pth P ν k) b)), (r : ℝ≥0∞) < c :=
  h.pre

omit [Countable I] [MeasurableSingletonClass I] in
theorem T_le_hDl (_hν : CycGood ν) (h : EnvAt P ν k r ρ) (_hg : StepGood P sc ν ρ o) :
    ((r + CycScheme.sStar P sc (ρ, false) o : ℝ≥0) : ℝ≥0∞) ≤
      (pth P ν k).1.jt ((pth P ν k).1.cnt r) +
        P.dl k (P.hatRec k (P.ideal (rule P ν) k) (pth P ν k) ((pth P ν k).1.cnt r)) := by
  have hrc := le_jt_add_D (pth P ν k).1
    (fun b => P.st k (P.hatRec k (P.ideal (rule P ν) k) (pth P ν k) b) = true)
    (fun b => P.dl k (P.hatRec k (P.ideal (rule P ν) k) (pth P ν k) b)) r (pre_abs h)
  have h1 : ((CycScheme.sStar P sc (ρ, false) o : ℝ≥0) : ℝ≥0∞) ≤
      CycScheme.hDl P ρ (CycScheme.cur P (ρ, false)) :=
    (by exact_mod_cast sStar_le_h (P := P) (sc := sc) (ρ := ρ) o :
      ((CycScheme.sStar P sc (ρ, false) o : ℝ≥0) : ℝ≥0∞) ≤ CycScheme.hOf P sc (ρ, false)).trans
      (hOf_le_hDl ρ)
  rw [h.hDl] at h1
  have := (ENNReal.le_sub_iff_add_le_right ENNReal.coe_ne_top hrc).1 h1
  rw [ENNReal.coe_add, add_comm]
  exact this

theorem jump_facts (hν : CycGood ν) (h : EnvAt P ν k r ρ) (hg : StepGood P sc ν ρ o) :
    ((r + CycScheme.sStar P sc (ρ, false) o : ℝ≥0) : ℝ≥0∞) ≤
        (pth P ν k).1.jt ((pth P ν k).1.cnt r + 1) ∧
      ((pth P ν k).1.fn (r + CycScheme.sStar P sc (ρ, false) o) ≠ (pth P ν k).1.fn r →
        (pth P ν k).1.jt ((pth P ν k).1.cnt r + 1) =
          ((r + CycScheme.sStar P sc (ρ, false) o : ℝ≥0) : ℝ≥0∞)) ∧
      ((pth P ν k).1.fn (r + CycScheme.sStar P sc (ρ, false) o) = (pth P ν k).1.fn r →
        ((r + CycScheme.sStar P sc (ρ, false) o : ℝ≥0) : ℝ≥0∞) <
          (pth P ν k).1.jt ((pth P ν k).1.cnt r + 1)) := by
  obtain ⟨hconst, hleft⟩ := quiet_facts hν h hg
  have hj : (pth P ν k).1.fn (r + CycScheme.sStar P sc (ρ, false) o) ≠ (pth P ν k).1.fn r →
      (pth P ν k).1.jt ((pth P ν k).1.cnt r + 1) =
        ((r + CycScheme.sStar P sc (ρ, false) o : ℝ≥0) : ℝ≥0∞) :=
    fun hfn => jt_cnt_succ_eq (pth P ν k).1 r _ hconst hleft hfn
  have hn : (pth P ν k).1.fn (r + CycScheme.sStar P sc (ρ, false) o) = (pth P ν k).1.fn r →
      ((r + CycScheme.sStar P sc (ρ, false) o : ℝ≥0) : ℝ≥0∞) <
        (pth P ν k).1.jt ((pth P ν k).1.cnt r + 1) :=
    fun hfn => lt_jt_of_fn_eq (pth P ν k).1 r _ hconst hleft hfn
  refine ⟨?_, hj, hn⟩
  by_cases hfn : (pth P ν k).1.fn (r + CycScheme.sStar P sc (ρ, false) o) = (pth P ν k).1.fn r
  · exact (hn hfn).le
  · exact (hj hfn).ge

theorem stops_iff (hν : CycGood ν) (h : EnvAt P ν k r ρ) (hg : StepGood P sc ν ρ o) :
    CycScheme.stops P sc (ρ, false) o ↔
      ((r + CycScheme.sStar P sc (ρ, false) o : ℝ≥0) : ℝ≥0∞) ∈ cand P ν k := by
  obtain ⟨hJ, hjump, hnojump⟩ := jump_facts hν h hg
  rw [cand_eq, T_mem_cand_iff (pth P ν k).1 _ _ r _ (pre_abs h) hJ hjump hnojump]
  unfold CycScheme.stops
  rw [newV_eq hν h hg, h.pos]
  by_cases hfn : (pth P ν k).1.fn (r + CycScheme.sStar P sc (ρ, false) o) = (pth P ν k).1.fn r
  · rw [ite_eq_right (not_not.2 hfn)]
    rw [h.hDl]
    have hrc := le_jt_add_D (pth P ν k).1
      (fun b => P.st k (P.hatRec k (P.ideal (rule P ν) k) (pth P ν k) b) = true)
      (fun b => P.dl k (P.hatRec k (P.ideal (rule P ν) k) (pth P ν k) b)) r (pre_abs h)
    have key : ((CycScheme.sStar P sc (ρ, false) o : ℝ≥0) : ℝ≥0∞) =
        (pth P ν k).1.jt ((pth P ν k).1.cnt r) +
          P.dl k (P.hatRec k (P.ideal (rule P ν) k) (pth P ν k) ((pth P ν k).1.cnt r)) - r ↔
        ((r + CycScheme.sStar P sc (ρ, false) o : ℝ≥0) : ℝ≥0∞) =
          (pth P ν k).1.jt ((pth P ν k).1.cnt r) +
          P.dl k (P.hatRec k (P.ideal (rule P ν) k) (pth P ν k) ((pth P ν k).1.cnt r)) := by
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
    have hhat : P.hatRec k (P.ideal (rule P ν) k) (pth P ν k) ((pth P ν k).1.cnt r + 1) =
        CycRec.snoc (P.ideal (rule P ν) k)
          (dat P ν k, (pth P ν k).cut (((r + CycScheme.sStar P sc (ρ, false) o : ℝ≥0)) : ℝ≥0∞)) := by
      unfold CycPlan.hatRec
      refine congrArg (CycRec.snoc _) (Prod.ext rfl (Subtype.ext ?_))
      show (pth P ν k).1.cut ((pth P ν k).1.jt ((pth P ν k).1.cnt r + 1)) = _
      rw [hjt]
      rfl
    have hsd : (P.stOf (CycScheme.newRec P sc (ρ, false) o) = true ∨
        P.dlOf (CycScheme.newRec P sc (ρ, false) o) = 0) ↔
        (P.st k (P.hatRec k (P.ideal (rule P ν) k) (pth P ν k) ((pth P ν k).1.cnt r + 1)) = true ∨
          P.dl k (P.hatRec k (P.ideal (rule P ν) k) (pth P ν k) ((pth P ν k).1.cnt r + 1)) = 0) := by
      rw [newRec_eq hν h hg, hhat]
      rfl
    rw [hsd]
    constructor
    · intro hs; left; exact ⟨hfn, hs⟩
    · rintro (⟨_, hs⟩ | ⟨heq, _⟩)
      · exact hs
      · exact absurd heq hfn

theorem cand_lt_of_not_stops (hν : CycGood ν) (h : EnvAt P ν k r ρ) (hg : StepGood P sc ν ρ o)
    (hns : ¬ CycScheme.stops P sc (ρ, false) o) :
    ∀ c ∈ cand P ν k, ((r + CycScheme.sStar P sc (ρ, false) o : ℝ≥0) : ℝ≥0∞) < c := by
  intro c hc
  have hge := cand_ge (pth P ν k).1
    (fun b => P.st k (P.hatRec k (P.ideal (rule P ν) k) (pth P ν k) b) = true)
    (fun b => P.dl k (P.hatRec k (P.ideal (rule P ν) k) (pth P ν k) b)) r _ (pre_abs h)
    (jump_facts hν h hg).1 (T_le_hDl hν h hg) c hc
  refine lt_of_le_of_ne hge fun heq => hns ((stops_iff hν h hg).2 ?_)
  rw [heq]; exact hc

theorem sInf_cand_eq (hν : CycGood ν) (h : EnvAt P ν k r ρ) (hg : StepGood P sc ν ρ o)
    (hs : CycScheme.stops P sc (ρ, false) o) :
    sInf (cand P ν k) = ((r + CycScheme.sStar P sc (ρ, false) o : ℝ≥0) : ℝ≥0∞) := by
  refine le_antisymm (sInf_le ((stops_iff hν h hg).1 hs)) (le_sInf ?_)
  exact cand_ge (pth P ν k).1
    (fun b => P.st k (P.hatRec k (P.ideal (rule P ν) k) (pth P ν k) b) = true)
    (fun b => P.dl k (P.hatRec k (P.ideal (rule P ν) k) (pth P ν k) b)) r _ (pre_abs h)
    (jump_facts hν h hg).1 (T_le_hDl hν h hg)

omit [Countable I] in
omit [MeasurableSingletonClass I] in
theorem newEntry_env {ν : Measure (I × RingSpace d β)} {δ : CycData I d}
    (hg : Good (cycSlice δ.copy ν)) :
    CycData.newEntry δ = (δ, (envPath ν δ).cut (((0 : ℝ≥0)) : ℝ≥0∞)) := by
  refine Prod.ext rfl (Subtype.ext (CPath.ext' ?_ (funext fun t => ?_)))
  · show ((CycPath.const δ.start).1.cut 0).len = ((envPath ν δ).1.cut ((0 : ℝ≥0) : ℝ≥0∞)).len
    rw [CPath.cut_len, CPath.cut_len]; simp
  show ((CycPath.const δ.start).1.cut 0).fn t = ((envPath ν δ).1.cut ((0 : ℝ≥0) : ℝ≥0∞)).fn t
  rw [CPath.cut_fn, CPath.cut_fn]
  simp only [ENNReal.coe_zero, min_zero, ENNReal.toNNReal_zero]
  rw [envPath_zero hg]
  rfl

omit [Countable I] [MeasurableSingletonClass I] [Fact (0 < β)] in
theorem num_eq (h : EnvAt P ν k r ρ) : ρ.num = ((k + 1 : ℕ) : ℕ∞) := by
  rw [h.rec_eq]; rfl

theorem upd_notStop (hν : CycGood ν) (h : EnvAt P ν k r ρ) (hg : StepGood P sc ν ρ o)
    (hns : ¬ CycScheme.stops P sc (ρ, false) o) :
    EnvAt P ν k (r + CycScheme.sStar P sc (ρ, false) o) (CycScheme.upd P sc (ρ, false) o).1 ∧
      (CycScheme.upd P sc (ρ, false) o).2 =
        decide (((CycScheme.sStar P sc (ρ, false) o : ℝ≥0) : ℝ≥0∞) =
          CycScheme.hGl sc ρ (CycScheme.cur P (ρ, false))) := by
  have hu : CycScheme.upd P sc (ρ, false) o =
      (CycScheme.newRec P sc (ρ, false) o, decide (((CycScheme.sStar P sc (ρ, false) o : ℝ≥0) : ℝ≥0∞) =
          CycScheme.hGl sc ρ (CycScheme.cur P (ρ, false)))) := by
    unfold CycScheme.upd
    simp [hns]
  rw [hu]
  refine ⟨⟨newRec_eq hν h hg, h.allFin, h.lt_K, Or.inr (cand_lt_of_not_stops hν h hg hns)⟩, rfl⟩

theorem E_eq_of_stops (hν : CycGood ν) (h : EnvAt P ν k r ρ) (hg : StepGood P sc ν ρ o)
    (hs : CycScheme.stops P sc (ρ, false) o) :
    P.E (rule P ν) k = (dat P ν k, (pth P ν k).cut
      (((r + CycScheme.sStar P sc (ρ, false) o : ℝ≥0)) : ℝ≥0∞)) := by
  rw [E_eq, sInf_cand_eq hν h hg hs]

theorem upd_stop_end (hν : CycGood ν) (h : EnvAt P ν k r ρ) (hg : StepGood P sc ν ρ o)
    (hs : CycScheme.stops P sc (ρ, false) o) (hK : ¬ ((k + 1 : ℕ) : ℕ∞) < P.K) :
    CycScheme.upd P sc (ρ, false) o = (Sum.inl ⟨k + 1, P.ideal (rule P ν) (k + 1)⟩, true) := by
  unfold CycScheme.upd
  have hn := num_eq h
  simp only [Bool.false_eq_true, ite_false, hs, ite_true]
  rw [hn, ite_eq_right hK, newRec_eq hν h hg, ← E_eq_of_stops hν h hg hs]
  rfl

theorem upd_stop_next (hν : CycGood ν) (h : EnvAt P ν k r ρ) (hg : StepGood P sc ν ρ o)
    (hs : CycScheme.stops P sc (ρ, false) o) (hK : ((k + 1 : ℕ) : ℕ∞) < P.K) :
    (CycScheme.upd P sc (ρ, false) o).2 = false ∧
      EnvAt P ν (k + 1) 0 (CycScheme.upd P sc (ρ, false) o).1 := by
  have hu : CycScheme.upd P sc (ρ, false) o =
      (CycRec.push (P.startOf (CycScheme.newRec P sc (ρ, false) o)).newEntry
        (CycScheme.newRec P sc (ρ, false) o), false) := by
    unfold CycScheme.upd
    have hn := num_eq h
    simp only [Bool.false_eq_true, ite_false, hs, ite_true]
    rw [hn, ite_eq_left hK]
  rw [hu]
  refine ⟨rfl, ?_, ?_, ?_, Or.inl rfl⟩
  · rw [newRec_eq hν h hg, ← E_eq_of_stops hν h hg hs]
    have hne : (P.start (k + 1) (CycRec.snoc (P.ideal (rule P ν) k) (P.E (rule P ν) k))).newEntry =
        (dat P ν (k + 1), (pth P ν (k + 1)).cut ((0 : ℝ≥0) : ℝ≥0∞)) :=
      newEntry_env (ν := ν) (hν _)
    show (Sum.inl ⟨k + 1 + 1, CycRec.snoc (CycRec.snoc (P.ideal (rule P ν) k) (P.E (rule P ν) k))
      (P.start (k + 1) (CycRec.snoc (P.ideal (rule P ν) k) (P.E (rule P ν) k))).newEntry⟩ : CycRec I d) = _
    rw [hne]
    rfl
  · intro i hi
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hlt | heq
    · exact h.allFin i hlt
    · rw [heq, E_eq_of_stops hν h hg hs]
      show ((pth P ν k).1.cut _).len < ⊤
      rw [CPath.cut_len]; exact ENNReal.coe_lt_top
  · exact_mod_cast hK

omit [Countable I] in
omit [MeasurableSingletonClass I] in
theorem envAt_init (hν : CycGood ν) (hK : 0 < P.K) : EnvAt P ν 0 0 (CycScheme.init P).1 := by
  refine ⟨?_, fun i hi => absurd hi (Nat.not_lt_zero _), by exact_mod_cast hK, Or.inl rfl⟩
  have hne : (P.startOf (CycRec.empty : CycRec I d)).newEntry =
      (dat P ν 0, (pth P ν 0).cut ((0 : ℝ≥0) : ℝ≥0∞)) := newEntry_env (ν := ν) (hν _)
  show (CycRec.empty.push (P.startOf (CycRec.empty : CycRec I d)).newEntry : CycRec I d) = _
  rw [hne]
  rfl

end CycSchemeEnv
end ElboimSly.Cyclic

end
