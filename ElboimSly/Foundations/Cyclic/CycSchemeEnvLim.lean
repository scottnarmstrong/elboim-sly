/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycSchemeEnvConv
public import ElboimSly.Foundations.Cyclic.CycRecLimitSpec
public import Mathlib

/-!
# The environment scheme (b): the limit of the records is the environment final record

The environment scheme (b), last sentence, for `s_∘ = ∞`. For a trajectory `T` of the scheme
(good `ν`, `K ≥ 1`, `T.S 0 = init`): the sequence of records `ρ_j = (T.S j).1` is increasing
(`Traj.hext`), the set `Θ_0` of measurability of record functionals (e) contains the point (`Traj.thetaZero`), and
the limit record `Φ = recLim` is the environment final record `ρ^𝒫(ν)` (`Traj.recLim_eq`), entry by
entry (`Traj.limEntry_eq`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic
namespace CycSchemeEnv
variable {I : Type*} [MeasurableSpace I] [Countable I] [MeasurableSingletonClass I] {d : ℕ} {β : ℝ}
  [Fact (0 < β)] {P : CycPlan I d β} {ν : Measure (I × RingSpace d β)} {sc : ℝ≥0∞}
variable (T : Traj P sc ν)

/-- The sequence of records of a trajectory, as a sequence over the one-point space. -/
def Traj.recSeq : ℕ → Unit → CycRec I d := fun j _ => (T.S j).1

theorem Traj.hext (hν : CycGood ν) (hK : 0 < P.K) (h0 : T.S 0 = CycScheme.init P) :
    ∀ j (ϑ : Unit), (T.recSeq j ϑ).Extends (T.recSeq (j + 1) ϑ) := fun j _ =>
  T.extends hν hK h0 j

theorem Traj.lt_numLim_iff_cont (hν : CycGood ν) (hK : 0 < P.K) (h0 : T.S 0 = CycScheme.init P)
    (hsc : sc = ⊤) (k : ℕ) :
    (k : ℕ∞) < numLim T.recSeq () ↔ P.Cont (rule P ν) k := by
  rw [lt_numLim_iff]
  constructor
  · rintro ⟨j, hj⟩
    obtain ⟨k', r, hrec, hall, hlt, -⟩ := (T.inv hν hK h0 j).rec_form
    have hnum : (T.recSeq j ()).num = ((k' + 1 : ℕ) : ℕ∞) := by
      show (T.S j).1.num = _
      rw [hrec]; rfl
    rw [hnum] at hj
    have : k ≤ k' := by exact_mod_cast Nat.lt_succ_iff.1 (by exact_mod_cast hj)
    exact CycPlan.Cont.anti P (rule P ν) this ⟨hlt, hall⟩
  · intro hc
    obtain ⟨j, r, h, -⟩ := T.reach hν hK h0 hsc k hc
    refine ⟨j, ?_⟩
    show (k : ℕ∞) < (T.S j).1.num
    rw [h.rec_eq]
    show (k : ℕ∞) < ((k + 1 : ℕ) : ℕ∞)
    exact_mod_cast Nat.lt_succ_self k

variable (junk : CycEntry I d)

/-- The stage entries of walk `k` are initial pieces of `E k`. -/
theorem Traj.stage_form (hν : CycGood ν) (hK : 0 < P.K) (h0 : T.S 0 = CycScheme.init P)
    (hsc : sc = ⊤) {k : ℕ} (hc : P.Cont (rule P ν) k) (j : ℕ) :
    ∃ ρ' : ℝ≥0∞, ρ' ≤ sInf (cand P ν k) ∧
      stageEntry T.recSeq junk k j () = (dat P ν k, (pth P ν k).cut ρ') := by
  have hk := (T.lt_numLim_iff_cont hν hK h0 hsc k).2 hc
  have h1 := stageEntry_nth (T.hext hν hK h0) junk () hk j
  exact nth_of_inv (T.inv hν hK h0 _) h1

theorem Traj.limGood (hν : CycGood ν) (hK : 0 < P.K) (h0 : T.S 0 = CycScheme.init P)
    (hsc : sc = ⊤) {k : ℕ} (hc : P.Cont (rule P ν) k) : LimGood T.recSeq junk k () := by
  intro M
  refine ⟨(pth P ν k).1.cnt (M : ℝ≥0) + 1, ?_⟩
  have h1 : ((M : ℝ≥0) : ℝ≥0∞) < (pth P ν k).1.jt ((pth P ν k).1.cnt (M : ℝ≥0) + 1) :=
    lt_jt_cnt_succ _ _
  refine lt_of_lt_of_le (by simpa using h1) (le_iInf fun j => ?_)
  obtain ⟨ρ', -, hρ⟩ := T.stage_form junk hν hK h0 hsc hc j
  show _ ≤ (stageEntry T.recSeq junk k j ()).path.jt _
  rw [hρ]
  show _ ≤ ((pth P ν k).1.cut ρ').jt _
  rw [CPath.jt_cut]
  split_ifs
  · exact le_rfl
  · exact le_top

theorem Traj.stage_conv (hν : CycGood ν) (hK : 0 < P.K) (h0 : T.S 0 = CycScheme.init P)
    (hsc : sc = ⊤) {k : ℕ} (hc : P.Cont (rule P ν) k) :
    (sInf (cand P ν k) = ⊤ ∧ ∀ M : ℝ≥0, ∃ J, ∀ j, J ≤ j → ∃ ρ'' : ℝ≥0∞, (M : ℝ≥0∞) < ρ'' ∧
        stageEntry T.recSeq junk k j () = (dat P ν k, (pth P ν k).cut ρ'')) ∨
    (sInf (cand P ν k) < ⊤ ∧ ∃ J, ∀ j, J ≤ j →
        stageEntry T.recSeq junk k j () = P.E (rule P ν) k) := by
  have hk := (T.lt_numLim_iff_cont hν hK h0 hsc k).2 hc
  have hst : ∀ j, (T.S (max j (firstStage T.recSeq k ()))).1.nth k =
      some (stageEntry T.recSeq junk k j ()) := fun j =>
    stageEntry_nth (T.hext hν hK h0) junk () hk j
  by_cases htop : sInf (cand P ν k) = ⊤
  · left
    refine ⟨htop, fun M => ?_⟩
    obtain ⟨J, hJ⟩ := T.case_top hν hK h0 hsc hc htop M
    refine ⟨J, fun j hj => ?_⟩
    obtain ⟨r, hMr, hr⟩ := hJ (max j (firstStage T.recSeq k ())) (le_trans hj (le_max_left _ _))
    rw [hst j] at hr
    exact ⟨r, by exact_mod_cast hMr, Option.some.inj hr⟩
  · right
    refine ⟨lt_top_iff_ne_top.2 htop, ?_⟩
    obtain ⟨J, hJ⟩ := T.case_fin hν hK h0 hsc hc (lt_top_iff_ne_top.2 htop)
    refine ⟨J, fun j hj => ?_⟩
    have := hJ (max j (firstStage T.recSeq k ())) (le_trans hj (le_max_left _ _))
    rw [hst j] at this
    exact Option.some.inj this

theorem Traj.limEntry_eq (hν : CycGood ν) (hK : 0 < P.K) (h0 : T.S 0 = CycScheme.init P)
    (hsc : sc = ⊤) {k : ℕ} (hc : P.Cont (rule P ν) k) :
    limEntry junk (T.hext hν hK h0) k () = P.E (rule P ν) k := by
  have hk := (T.lt_numLim_iff_cont hν hK h0 hsc k).2 hc
  have hg := T.limGood junk hν hK h0 hsc hc
  have hchain := stagePath_isChain (T.hext hν hK h0) junk () hk
  have hgood' := LimGood.nnreal junk hg
  have hconv := T.stage_conv junk hν hK h0 hsc hc
  unfold limEntry
  rw [dite_eq_left ⟨hk, hg⟩]
  obtain ⟨ρ0, -, hρ0⟩ := T.stage_form junk hν hK h0 hsc hc 0
  rw [E_eq]
  refine Prod.ext (by
    show (stageEntry T.recSeq junk k 0 ()).data = dat P ν k
    rw [hρ0]; rfl) (Subtype.ext (CPath.ext' ?_ (funext fun t => ?_)))
  · -- lengths
    show (hchain.limPath hgood').len = ((pth P ν k).1.cut (sInf (cand P ν k))).len
    rw [CPath.IsChain.limPath_len, CPath.cut_len]
    refine le_antisymm (iSup_le fun j => ?_) ?_
    · obtain ⟨ρ', hρ', hj⟩ := T.stage_form junk hν hK h0 hsc hc j
      show (stageEntry T.recSeq junk k j ()).len ≤ _
      rw [hj]
      exact (CPath.cut_len _ _).le.trans hρ'
    · rcases hconv with ⟨htop, hM⟩ | ⟨hfin, J, hJ⟩
      · rw [htop]
        refine ENNReal.le_of_forall_nnreal_lt fun M hM' => ?_
        obtain ⟨J, hJ⟩ := hM M
        obtain ⟨ρ'', hMρ, hρ''⟩ := hJ J le_rfl
        refine hMρ.le.trans (le_iSup_of_le J ?_)
        show _ ≤ (stageEntry T.recSeq junk k J ()).len
        rw [hρ'']
        exact (CPath.cut_len _ _).ge
      · refine le_iSup_of_le J ?_
        show _ ≤ (stageEntry T.recSeq junk k J ()).len
        rw [hJ J le_rfl, E_eq]
        exact (CPath.cut_len _ _).ge
  · show (hchain.limPath hgood').fn t = ((pth P ν k).1.cut (sInf (cand P ν k))).fn t
    rw [CPath.IsChain.limPath_fn]
    obtain ⟨J, hJ⟩ := hchain.limFn_spec hgood' t
    rcases hconv with ⟨htop, hM⟩ | ⟨hfin, J1, hJ1⟩
    · obtain ⟨J2, hJ2⟩ := hM t
      obtain ⟨ρ'', hρ'', hj⟩ := hJ2 (max J J2) (le_max_right _ _)
      rw [hJ (max J J2) (le_max_left _ _) t le_rfl]
      show (stageEntry T.recSeq junk k (max J J2) ()).path.fn t = _
      rw [hj, htop]
      show ((pth P ν k).1.cut ρ'').fn t = ((pth P ν k).1.cut ⊤).fn t
      rw [CPath.cut_fn, CPath.cut_fn]
      have : min (t : ℝ≥0∞) ρ'' = t := min_eq_left hρ''.le
      simp [this]
    · rw [hJ (max J J1) (le_max_left _ _) t le_rfl]
      show (stageEntry T.recSeq junk k (max J J1) ()).path.fn t = _
      rw [hJ1 _ (le_max_right _ _), E_eq]
      rfl

omit [MeasurableSpace I] [Countable I] [MeasurableSingletonClass I] in
theorem CycRec.ext_nth' {ρ ρ' : CycRec I d} (h : ∀ k, ρ.nth k = ρ'.nth k) : ρ = ρ' := by
  rcases ρ with ⟨n, f⟩ | f <;> rcases ρ' with ⟨n', f'⟩ | f'
  · have hn : n = n' := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hlt
      · have := h n
        simp [CycRec.nth, hlt] at this
      · have := h n'
        simp [CycRec.nth, hlt] at this
    subst hn
    congr
    funext i
    have := h i
    simp [CycRec.nth, i.2] at this
    exact this
  · have := h n
    simp [CycRec.nth] at this
  · have := h n'
    simp [CycRec.nth] at this
  · congr
    funext k
    have := h k
    simpa [CycRec.nth] using this

theorem Traj.thetaZero (hν : CycGood ν) (hK : 0 < P.K) (h0 : T.S 0 = CycScheme.init P)
    (hsc : sc = ⊤) : () ∈ thetaZero T.recSeq junk := fun k hk =>
  T.limGood junk hν hK h0 hsc ((T.lt_numLim_iff_cont hν hK h0 hsc k).1 hk)

/-- The environment scheme (b) (`s_∘ = ∞`): the limit `Φ` of the records of the scheme is the
environment final record `ρ^𝒫(N)`, coordinatewise. -/
theorem Traj.recLim_nth (hν : CycGood ν) (hK : 0 < P.K) (h0 : T.S 0 = CycScheme.init P)
    (hsc : sc = ⊤) (k : ℕ) :
    (recLim junk (T.hext hν hK h0) ()).nth k = (P.envFinal ν).nth k := by
  classical
  have hth := T.thetaZero junk hν hK h0 hsc
  have hnum := num_recLim (ρ := T.recSeq) junk (T.hext hν hK h0) ()
  rw [ite_eq_left hth] at hnum
  show (recLim junk (T.hext hν hK h0) ()).nth k = (P.cycFinal (rule P ν)).nth k
  rw [CycPlan.cycFinal_nth_gen P (rule P ν) k]
  by_cases hc : P.Cont (rule P ν) k
  · rw [ite_eq_left hc]
    have hk := (T.lt_numLim_iff_cont hν hK h0 hsc k).2 hc
    rw [ElboimSly.Cyclic.recLim_nth junk (T.hext hν hK h0) hth hk, T.limEntry_eq junk hν hK h0 hsc hc]
  · rw [ite_eq_right hc]
    rcases h : (recLim junk (T.hext hν hK h0) ()).nth k with _ | e
    · rfl
    · exfalso
      have := lt_num_of_nth h
      rw [hnum] at this
      exact hc ((T.lt_numLim_iff_cont hν hK h0 hsc k).1 this)

/-- The environment scheme (b) (`s_∘ = ∞`): the limit `Φ` of the records of the scheme is the
environment final record `ρ^𝒫(N)`. -/
theorem Traj.recLim_eq (hν : CycGood ν) (hK : 0 < P.K) (h0 : T.S 0 = CycScheme.init P)
    (hsc : sc = ⊤) :
    recLim junk (T.hext hν hK h0) () = P.envFinal ν :=
  CycRec.ext_nth' fun k => T.recLim_nth junk hν hK h0 hsc k

end CycSchemeEnv
end ElboimSly.Cyclic

end
