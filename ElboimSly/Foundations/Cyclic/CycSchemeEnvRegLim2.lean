/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycSchemeEnvRegLim
public import ElboimSly.Foundations.Cyclic.CycSchemeEnvFinalFin
public import Mathlib

/-!
# The environment scheme (c): the region of the limit record is the union of the regions

The environment scheme (c). `Traj.region_recLim_eq`: for a trajectory of the scheme
(good `ν`, `K ≥ 1`, any horizon `s_∘`), the region of the limit record `Φ` is `⋃_j R(ρ_j)`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic
namespace CycSchemeEnv
variable {I : Type*} [MeasurableSpace I] [Countable I] [MeasurableSingletonClass I] {d : ℕ} {β : ℝ}
  [Fact (0 < β)] {P : CycPlan I d β} {ν : Measure (I × RingSpace d β)} {sc : ℝ≥0∞}
variable (T : Traj P sc ν) (junk : CycEntry I d)

/-- For a finite horizon, the entry `tgt` of the truncation is an entry of some record. -/
theorem Traj.exists_nth_tgt_fin (hν : CycGood ν) (hK : 0 < P.K) (h0 : T.S 0 = CycScheme.init P)
    (hsc : sc ≠ ⊤) {k : ℕ} (hc : P.Cont (rule P ν) k) (hl : lam P ν k ≤ sc) :
    ∃ j, (T.S j).1.nth k = some (tgt P ν sc.toNNReal k) := by
  have hlamfin : lam P ν k ≠ ⊤ := lam_ne_top hc.2
  unfold tgt
  rw [ENNReal.coe_toNNReal hsc]
  by_cases hbud : lam P ν k + (P.E (rule P ν) k).len ≤ sc
  · rw [ite_eq_left hbud]
    have hfin : sInf (cand P ν k) < ⊤ := by
      rw [← E_len']
      exact lt_of_le_of_lt (le_add_self.trans hbud) (lt_top_iff_ne_top.2 hsc)
    obtain ⟨J, hJ⟩ := T.nth_eventually_stop hν hK h0 hc hl hfin (by rwa [← E_len'])
    exact ⟨J, hJ J le_rfl⟩
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
    exact ⟨J, hJ J le_rfl⟩

theorem Traj.region_recLim_subset (hν : CycGood ν) (hK : 0 < P.K) (h0 : T.S 0 = CycScheme.init P) :
    (recLim junk (T.hext hν hK h0) ()).region β ⊆ ⋃ j, (T.S j).1.region β := by
  classical
  rintro x ⟨e, ⟨k, hk⟩, hx⟩
  have hth := T.thetaZero_fin junk hν hK h0
  have hnum := num_recLim (ρ := T.recSeq) junk (T.hext hν hK h0) ()
  rw [ite_eq_left hth] at hnum
  have hkl : (k : ℕ∞) < numLim T.recSeq () := by
    have := lt_num_of_nth hk
    rwa [hnum] at this
  have he : e = limEntry junk (T.hext hν hK h0) k () := by
    have := ElboimSly.Cyclic.recLim_nth junk (T.hext hν hK h0) hth hkl
    rw [hk] at this
    exact Option.some.inj this
  subst he
  by_cases hsc : sc = ⊤
  · have hc : P.Cont (rule P ν) k := (T.lt_numLim_iff_cont hν hK h0 hsc k).1 hkl
    have hst : ∀ j, (T.S (max j (firstStage T.recSeq k ()))).1.nth k =
        some (stageEntry T.recSeq junk k j ()) := fun j =>
      stageEntry_nth (T.hext hν hK h0) junk () hkl j
    rw [T.limEntry_eq junk hν hK h0 hsc hc] at hx
    rcases T.stage_conv junk hν hK h0 hsc hc with ⟨htop, hM⟩ | ⟨hfin, J, hJ⟩
    · rw [E_eq, htop] at hx
      obtain ⟨r, hr0, -, h1, h2, h3⟩ := (mem_region_cut_iff _ _ _ _).1 hx
      obtain ⟨J, hJ⟩ := hM r
      obtain ⟨ρ'', hρ'', hent⟩ := hJ J le_rfl
      refine mem_iUnion.2 ⟨max J (firstStage T.recSeq k ()), ⟨_, ⟨k, hst J⟩, ?_⟩⟩
      rw [hent]
      exact (mem_region_cut_iff _ _ _ _).2 ⟨r, hr0, hρ''.le, h1, h2, h3⟩
    · refine mem_iUnion.2 ⟨max J (firstStage T.recSeq k ()), ⟨_, ⟨k, hst J⟩, ?_⟩⟩
      rw [hJ J le_rfl]
      exact hx
  · obtain ⟨hc, hl⟩ := (T.lt_numLim_iff_fin hν hK h0 k).1 hkl
    rw [T.limEntry_fin junk hν hK h0 hsc hc hl] at hx
    obtain ⟨j, hj⟩ := T.exists_nth_tgt_fin hν hK h0 hsc hc hl
    exact mem_iUnion.2 ⟨j, _, ⟨k, hj⟩, hx⟩

theorem Traj.region_recLim_eq (hν : CycGood ν) (hK : 0 < P.K) (h0 : T.S 0 = CycScheme.init P) :
    (recLim junk (T.hext hν hK h0) ()).region β = ⋃ j, (T.S j).1.region β := by
  refine Subset.antisymm (T.region_recLim_subset junk hν hK h0) (iUnion_subset fun j => ?_)
  exact CycRec.region_mono_of_extends
    (extends_recLim junk (T.hext hν hK h0) (T.thetaZero_fin junk hν hK h0) j)

end CycSchemeEnv
end ElboimSly.Cyclic

end
