/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycSchemeGenConv
public import ElboimSly.Foundations.Cyclic.CycSchemeEnvLim
public import Mathlib

/-!
# Generic limit of the records (port of `CycSchemeEnvLim`)

The environment scheme (b), the driving scheme (c).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic
namespace CycSchemeGen
open ElboimSly.Cyclic.CycSchemeEnv (candAbs unbounded_of_marked lt_jt_cnt_succ)
variable {I : Type*} [MeasurableSpace I] [Countable I] [MeasurableSingletonClass I] {d : ℕ} {β : ℝ}
  [Fact (0 < β)] {P : CycPlan I d β} {rl : PathRule I d} {sc : ℝ≥0∞}

variable (T : GTraj P sc rl)

/-- The sequence of records of a trajectory, as a sequence over the one-point space. -/
def GTraj.recSeq : ℕ → Unit → CycRec I d := fun j _ => (T.S j).1

theorem GTraj.hext (hK : 0 < P.K) (h0 : T.S 0 = CycScheme.init P) :
    ∀ j (ϑ : Unit), (T.recSeq j ϑ).Extends (T.recSeq (j + 1) ϑ) := fun j _ =>
  T.extends hK h0 j

theorem GTraj.lt_numLim_iff_cont (hK : 0 < P.K) (h0 : T.S 0 = CycScheme.init P)
    (hsc : sc = ⊤) (k : ℕ) :
    (k : ℕ∞) < numLim T.recSeq () ↔ P.Cont rl k := by
  rw [lt_numLim_iff]
  constructor
  · rintro ⟨j, hj⟩
    obtain ⟨k', r, hrec, hall, hlt, -⟩ := (T.inv hK h0 j).rec_form
    have hnum : (T.recSeq j ()).num = ((k' + 1 : ℕ) : ℕ∞) := by
      show (T.S j).1.num = _
      rw [hrec]; rfl
    rw [hnum] at hj
    have : k ≤ k' := by exact_mod_cast Nat.lt_succ_iff.1 (by exact_mod_cast hj)
    exact CycPlan.Cont.anti P rl this ⟨hlt, hall⟩
  · intro hc
    obtain ⟨j, r, h, -⟩ := T.reach hK h0 hsc k hc
    refine ⟨j, ?_⟩
    show (k : ℕ∞) < (T.S j).1.num
    rw [h.rec_eq]
    show (k : ℕ∞) < ((k + 1 : ℕ) : ℕ∞)
    exact_mod_cast Nat.lt_succ_self k

variable (junk : CycEntry I d)

/-- The stage entries of walk `k` are initial pieces of `E k`. -/
theorem GTraj.stage_form (hK : 0 < P.K) (h0 : T.S 0 = CycScheme.init P)
    (hsc : sc = ⊤) {k : ℕ} (hc : P.Cont rl k) (j : ℕ) :
    ∃ ρ' : ℝ≥0∞, ρ' ≤ sInf (gcand P rl k) ∧
      stageEntry T.recSeq junk k j () = (gdat P rl k, (gpth P rl k).cut ρ') := by
  have hk := (T.lt_numLim_iff_cont hK h0 hsc k).2 hc
  have h1 := stageEntry_nth (T.hext hK h0) junk () hk j
  exact nth_of_inv (T.inv hK h0 _) h1

theorem GTraj.limGood (hK : 0 < P.K) (h0 : T.S 0 = CycScheme.init P)
    (hsc : sc = ⊤) {k : ℕ} (hc : P.Cont rl k) : LimGood T.recSeq junk k () := by
  intro M
  refine ⟨(gpth P rl k).1.cnt (M : ℝ≥0) + 1, ?_⟩
  have h1 : ((M : ℝ≥0) : ℝ≥0∞) < (gpth P rl k).1.jt ((gpth P rl k).1.cnt (M : ℝ≥0) + 1) :=
    lt_jt_cnt_succ _ _
  refine lt_of_lt_of_le (by simpa using h1) (le_iInf fun j => ?_)
  obtain ⟨ρ', -, hρ⟩ := T.stage_form junk hK h0 hsc hc j
  show _ ≤ (stageEntry T.recSeq junk k j ()).path.jt _
  rw [hρ]
  show _ ≤ ((gpth P rl k).1.cut ρ').jt _
  rw [CPath.jt_cut]
  split_ifs
  · exact le_rfl
  · exact le_top

theorem GTraj.stage_conv (hK : 0 < P.K) (h0 : T.S 0 = CycScheme.init P)
    (hsc : sc = ⊤) {k : ℕ} (hc : P.Cont rl k) :
    (sInf (gcand P rl k) = ⊤ ∧ ∀ M : ℝ≥0, ∃ J, ∀ j, J ≤ j → ∃ ρ'' : ℝ≥0∞, (M : ℝ≥0∞) < ρ'' ∧
        stageEntry T.recSeq junk k j () = (gdat P rl k, (gpth P rl k).cut ρ'')) ∨
    (sInf (gcand P rl k) < ⊤ ∧ ∃ J, ∀ j, J ≤ j →
        stageEntry T.recSeq junk k j () = P.E rl k) := by
  have hk := (T.lt_numLim_iff_cont hK h0 hsc k).2 hc
  have hst : ∀ j, (T.S (max j (firstStage T.recSeq k ()))).1.nth k =
      some (stageEntry T.recSeq junk k j ()) := fun j =>
    stageEntry_nth (T.hext hK h0) junk () hk j
  by_cases htop : sInf (gcand P rl k) = ⊤
  · left
    refine ⟨htop, fun M => ?_⟩
    obtain ⟨J, hJ⟩ := T.case_top hK h0 hsc hc htop M
    refine ⟨J, fun j hj => ?_⟩
    obtain ⟨r, hMr, hr⟩ := hJ (max j (firstStage T.recSeq k ())) (le_trans hj (le_max_left _ _))
    rw [hst j] at hr
    exact ⟨r, by exact_mod_cast hMr, Option.some.inj hr⟩
  · right
    refine ⟨lt_top_iff_ne_top.2 htop, ?_⟩
    obtain ⟨J, hJ⟩ := T.case_fin hK h0 hsc hc (lt_top_iff_ne_top.2 htop)
    refine ⟨J, fun j hj => ?_⟩
    have := hJ (max j (firstStage T.recSeq k ())) (le_trans hj (le_max_left _ _))
    rw [hst j] at this
    exact Option.some.inj this

theorem GTraj.limEntry_eq (hK : 0 < P.K) (h0 : T.S 0 = CycScheme.init P)
    (hsc : sc = ⊤) {k : ℕ} (hc : P.Cont rl k) :
    limEntry junk (T.hext hK h0) k () = P.E rl k := by
  have hk := (T.lt_numLim_iff_cont hK h0 hsc k).2 hc
  have hg := T.limGood junk hK h0 hsc hc
  have hchain := stagePath_isChain (T.hext hK h0) junk () hk
  have hgood' := LimGood.nnreal junk hg
  have hconv := T.stage_conv junk hK h0 hsc hc
  unfold limEntry
  rw [dite_eq_left ⟨hk, hg⟩]
  obtain ⟨ρ0, -, hρ0⟩ := T.stage_form junk hK h0 hsc hc 0
  rw [E_eq']
  refine Prod.ext (by
    show (stageEntry T.recSeq junk k 0 ()).data = gdat P rl k
    rw [hρ0]; rfl) (Subtype.ext (CPath.ext' ?_ (funext fun t => ?_)))
  · -- lengths
    show (hchain.limPath hgood').len = ((gpth P rl k).1.cut (sInf (gcand P rl k))).len
    rw [CPath.IsChain.limPath_len, CPath.cut_len]
    refine le_antisymm (iSup_le fun j => ?_) ?_
    · obtain ⟨ρ', hρ', hj⟩ := T.stage_form junk hK h0 hsc hc j
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
        rw [hJ J le_rfl, E_eq']
        exact (CPath.cut_len _ _).ge
  · show (hchain.limPath hgood').fn t = ((gpth P rl k).1.cut (sInf (gcand P rl k))).fn t
    rw [CPath.IsChain.limPath_fn]
    obtain ⟨J, hJ⟩ := hchain.limFn_spec hgood' t
    rcases hconv with ⟨htop, hM⟩ | ⟨hfin, J1, hJ1⟩
    · obtain ⟨J2, hJ2⟩ := hM t
      obtain ⟨ρ'', hρ'', hj⟩ := hJ2 (max J J2) (le_max_right _ _)
      rw [hJ (max J J2) (le_max_left _ _) t le_rfl]
      show (stageEntry T.recSeq junk k (max J J2) ()).path.fn t = _
      rw [hj, htop]
      show ((gpth P rl k).1.cut ρ'').fn t = ((gpth P rl k).1.cut ⊤).fn t
      rw [CPath.cut_fn, CPath.cut_fn]
      have : min (t : ℝ≥0∞) ρ'' = t := min_eq_left hρ''.le
      simp [this]
    · rw [hJ (max J J1) (le_max_left _ _) t le_rfl]
      show (stageEntry T.recSeq junk k (max J J1) ()).path.fn t = _
      rw [hJ1 _ (le_max_right _ _), E_eq']
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

theorem GTraj.thetaZero (hK : 0 < P.K) (h0 : T.S 0 = CycScheme.init P)
    (hsc : sc = ⊤) : () ∈ thetaZero T.recSeq junk := fun k hk =>
  T.limGood junk hK h0 hsc ((T.lt_numLim_iff_cont hK h0 hsc k).1 hk)

/-- The environment scheme (b) (`s_∘ = ∞`): the limit `Φ` of the records of the scheme is the
environment final record `ρ^𝒫(N)`, coordinatewise. -/
theorem GTraj.recLim_nth (hK : 0 < P.K) (h0 : T.S 0 = CycScheme.init P)
    (hsc : sc = ⊤) (k : ℕ) :
    (recLim junk (T.hext hK h0) ()).nth k = (P.cycFinal rl).nth k := by
  classical
  have hth := T.thetaZero junk hK h0 hsc
  have hnum := num_recLim (ρ := T.recSeq) junk (T.hext hK h0) ()
  rw [ite_eq_left hth] at hnum
  show (recLim junk (T.hext hK h0) ()).nth k = (P.cycFinal rl).nth k
  rw [CycPlan.cycFinal_nth_gen P rl k]
  by_cases hc : P.Cont rl k
  · rw [ite_eq_left hc]
    have hk := (T.lt_numLim_iff_cont hK h0 hsc k).2 hc
    rw [ElboimSly.Cyclic.recLim_nth junk (T.hext hK h0) hth hk, T.limEntry_eq junk hK h0 hsc hc]
  · rw [ite_eq_right hc]
    rcases h : (recLim junk (T.hext hK h0) ()).nth k with _ | e
    · rfl
    · exfalso
      have := lt_num_of_nth h
      rw [hnum] at this
      exact hc ((T.lt_numLim_iff_cont hK h0 hsc k).1 this)

/-- The environment scheme (b) (`s_∘ = ∞`): the limit `Φ` of the records of the scheme is the
environment final record `ρ^𝒫(N)`. -/
theorem GTraj.recLim_eq (hK : 0 < P.K) (h0 : T.S 0 = CycScheme.init P)
    (hsc : sc = ⊤) :
    recLim junk (T.hext hK h0) () = P.cycFinal rl :=
  CycRec.ext_nth' fun k => T.recLim_nth junk hK h0 hsc k


end CycSchemeGen
end ElboimSly.Cyclic

end
