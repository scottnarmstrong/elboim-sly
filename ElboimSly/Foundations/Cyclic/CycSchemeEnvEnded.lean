/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycSchemeEnvRegLim2
public import Mathlib

/-!
# The environment scheme (c): the limit record after the scheme has ended

The environment scheme (c). `Traj.recLim_eq_of_ended`: if the state `j` of a trajectory is
ended, the limit of the records is the record `ρ_j` (the states do not change after the end).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic
namespace CycSchemeEnv
variable {I : Type*} [MeasurableSpace I] [Countable I] [MeasurableSingletonClass I] {d : ℕ} {β : ℝ}
  [Fact (0 < β)] {P : CycPlan I d β} {ν : Measure (I × RingSpace d β)} {sc : ℝ≥0∞}
variable (T : Traj P sc ν) (junk : CycEntry I d)

theorem Traj.recLim_eq_of_ended (hν : CycGood ν) (hK : 0 < P.K) (h0 : T.S 0 = CycScheme.init P)
    {j : ℕ} (hf : (T.S j).2 = true) :
    recLim junk (T.hext hν hK h0) () = (T.S j).1 := by
  classical
  have hth := T.thetaZero_fin junk hν hK h0
  have hnum := num_recLim (ρ := T.recSeq) junk (T.hext hν hK h0) ()
  rw [ite_eq_left hth] at hnum
  refine CycRec.ext_nth' fun k => ?_
  by_cases hkj : (k : ℕ∞) < (T.S j).1.num
  · obtain ⟨e, he⟩ := nth_of_lt_num hkj
    have hkl : (k : ℕ∞) < numLim T.recSeq () := lt_numLim_iff.2 ⟨j, hkj⟩
    rw [he, ElboimSly.Cyclic.recLim_nth junk (T.hext hν hK h0) hth hkl]
    congr 1
    refine limEntry_of_const junk _ hkl (T.limGood' junk hν hK h0 hkl) e j fun j' hj' => ?_
    have h1 := stageEntry_nth (T.hext hν hK h0) junk () hkl j'
    have h2 : (T.recSeq (max j' (firstStage T.recSeq k ())) ()) = (T.S j).1 := by
      show (T.S (max j' (firstStage T.recSeq k ()))).1 = _
      rw [T.stay_finished hf _ (le_trans hj' (le_max_left _ _))]
    rw [h2, he] at h1
    exact (Option.some.inj h1).symm
  · have hn : (T.S j).1.nth k = none := by
      by_contra hne
      obtain ⟨e, he⟩ := Option.ne_none_iff_exists'.1 hne
      exact hkj (lt_num_of_nth he)
    rw [hn]
    by_contra hne
    obtain ⟨e, he⟩ := Option.ne_none_iff_exists'.1 hne
    have hlt := lt_num_of_nth he
    rw [hnum] at hlt
    obtain ⟨j', hj'⟩ := lt_numLim_iff.1 hlt
    rcases le_total j' j with hjj | hjj
    · exact hkj (lt_num_of_le (T.hext hν hK h0) () hjj hj')
    · rw [show (T.recSeq j' ()) = (T.S j').1 from rfl, T.stay_finished hf j' hjj] at hj'
      exact hkj hj'

end CycSchemeEnv
end ElboimSly.Cyclic

end
