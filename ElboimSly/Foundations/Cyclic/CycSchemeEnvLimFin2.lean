/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycSchemeEnvLimFin
public import Mathlib

/-!
# The environment scheme (b), finite horizon: the limit entries are those of the truncation

The environment scheme (b), convergence for finite `s_∘`.

* `Traj.lt_numLim_iff_fin`: entry `k` occurs in the limit iff `Cont k` and `Λ_k ≤ s_∘`.
* `tgt`: entry `k` of `Trunc_s(ρ^𝒫(ν))`, namely `E k` if `Λ_k + ℓ_k ≤ s` and `E k` cut at `s - Λ_k`
  otherwise.
* `Traj.limEntry_fin`: the limit entry `k` of the records is `tgt`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic
namespace CycSchemeEnv
variable {I : Type*} [MeasurableSpace I] [Countable I] [MeasurableSingletonClass I] {d : ℕ} {β : ℝ}
  [Fact (0 < β)] {P : CycPlan I d β} {ν : Measure (I × RingSpace d β)} {sc : ℝ≥0∞}

open scoped Classical in
/-- Entry `k` of `Trunc_s(ρ^𝒫(ν))`: `E k` if the walk ends before `s`, and `E k` cut at `s - Λ_k`
otherwise. -/
noncomputable def tgt (P : CycPlan I d β) (ν : Measure (I × RingSpace d β)) (s : ℝ≥0) (k : ℕ) :
    CycEntry I d :=
  if lam P ν k + (P.E (rule P ν) k).len ≤ (s : ℝ≥0∞) then P.E (rule P ν) k
  else (P.E (rule P ν) k).cut ((s : ℝ≥0∞) - lam P ν k)

variable (T : Traj P sc ν)

theorem Traj.lt_numLim_iff_fin (hν : CycGood ν) (hK : 0 < P.K) (h0 : T.S 0 = CycScheme.init P)
    (k : ℕ) : (k : ℕ∞) < numLim T.recSeq () ↔ P.Cont (rule P ν) k ∧ lam P ν k ≤ sc := by
  rw [lt_numLim_iff]
  constructor
  · rintro ⟨j, hj⟩
    obtain ⟨e, he⟩ := nth_of_lt_num hj
    exact T.cont_of_nth hν hK h0 he
  · rintro ⟨hc, hl⟩
    obtain ⟨j, r, h, -⟩ := T.reach_fin hν hK h0 k hc hl
    refine ⟨j, ?_⟩
    show (k : ℕ∞) < (T.S j).1.num
    rw [h.eq_shape]
    show (k : ℕ∞) < ((k + 1 : ℕ) : ℕ∞)
    exact_mod_cast Nat.lt_succ_self k

variable (junk : CycEntry I d)

theorem Traj.stage_form' (hν : CycGood ν) (hK : 0 < P.K) (h0 : T.S 0 = CycScheme.init P) {k : ℕ}
    (hk : (k : ℕ∞) < numLim T.recSeq ()) (j : ℕ) :
    ∃ ρ' : ℝ≥0∞, ρ' ≤ sInf (cand P ν k) ∧
      stageEntry T.recSeq junk k j () = (dat P ν k, (pth P ν k).cut ρ') :=
  nth_of_inv (T.inv hν hK h0 _) (stageEntry_nth (T.hext hν hK h0) junk () hk j)

theorem Traj.limGood' (hν : CycGood ν) (hK : 0 < P.K) (h0 : T.S 0 = CycScheme.init P) {k : ℕ}
    (hk : (k : ℕ∞) < numLim T.recSeq ()) : LimGood T.recSeq junk k () := by
  intro M
  refine ⟨(pth P ν k).1.cnt (M : ℝ≥0) + 1, ?_⟩
  have h1 : ((M : ℝ≥0) : ℝ≥0∞) < (pth P ν k).1.jt ((pth P ν k).1.cnt (M : ℝ≥0) + 1) :=
    lt_jt_cnt_succ _ _
  refine lt_of_lt_of_le (by simpa using h1) (le_iInf fun j => ?_)
  obtain ⟨ρ', -, hρ⟩ := T.stage_form' junk hν hK h0 hk j
  show _ ≤ (stageEntry T.recSeq junk k j ()).path.jt _
  rw [hρ]
  show _ ≤ ((pth P ν k).1.cut ρ').jt _
  rw [CPath.jt_cut]
  split_ifs
  · exact le_rfl
  · exact le_top

theorem Traj.limEntry_fin (hν : CycGood ν) (hK : 0 < P.K) (h0 : T.S 0 = CycScheme.init P)
    (hsc : sc ≠ ⊤) {k : ℕ} (hc : P.Cont (rule P ν) k) (hl : lam P ν k ≤ sc) :
    limEntry junk (T.hext hν hK h0) k () = tgt P ν sc.toNNReal k := by
  have hk := (T.lt_numLim_iff_fin hν hK h0 k).2 ⟨hc, hl⟩
  have hg := T.limGood' junk hν hK h0 hk
  have hst : ∀ j, (T.S (max j (firstStage T.recSeq k ()))).1.nth k =
      some (stageEntry T.recSeq junk k j ()) := fun j =>
    stageEntry_nth (T.hext hν hK h0) junk () hk j
  have hlamfin : lam P ν k ≠ ⊤ := lam_ne_top hc.2
  unfold tgt
  rw [ENNReal.coe_toNNReal hsc]
  by_cases hbud : lam P ν k + (P.E (rule P ν) k).len ≤ sc
  · rw [ite_eq_left hbud]
    have hfin : sInf (cand P ν k) < ⊤ := by
      rw [← E_len']
      exact lt_of_le_of_lt (le_add_self.trans hbud) (lt_top_iff_ne_top.2 hsc)
    obtain ⟨J, hJ⟩ := T.nth_eventually_stop hν hK h0 hc hl hfin (by rwa [← E_len'])
    refine limEntry_of_const junk _ hk hg _ J fun j hj => ?_
    have := hst j
    rw [hJ _ (le_trans hj (le_max_left _ _))] at this
    exact (Option.some.inj this).symm
  · rw [ite_eq_right hbud]
    have hbad : sc < lam P ν k + sInf (cand P ν k) := by
      rw [E_len'] at hbud; exact not_le.1 hbud
    obtain ⟨r, hr, J, hJ⟩ := T.nth_eventually_cut hν hK h0 hc hl hbad
    have hrle : (r : ℝ≥0∞) ≤ sInf (cand P ν k) := by
      have : lam P ν k + (r : ℝ≥0∞) ≤ lam P ν k + sInf (cand P ν k) := by
        rw [hr]; exact hbad.le
      exact (ENNReal.add_le_add_iff_left hlamfin).1 this
    have hsub : sc - lam P ν k = (r : ℝ≥0∞) := by
      rw [← hr, ENNReal.add_sub_cancel_left hlamfin]
    rw [hsub, E_cut_eq k hrle]
    refine limEntry_of_const junk _ hk hg _ J fun j hj => ?_
    have := hst j
    rw [hJ _ (le_trans hj (le_max_left _ _))] at this
    exact (Option.some.inj this).symm

end CycSchemeEnv
end ElboimSly.Cyclic

end
