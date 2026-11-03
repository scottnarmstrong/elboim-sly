/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Avoid.Setting
public import ElboimSly.Paper.Avoid.Lem41Meas
public import ElboimSly.Paper.Heavy.RegenCyclic
public import ElboimSly.Paper.Heavy.MeasStop
public import ElboimSly.Foundations.Cyclic.CycMultiGood
public import ElboimSly.Foundations.Cyclic.CycMultiRecStop
public import Mathlib

/-!
# The regenerated walk is adapted to the joint exploration filtration

ES22 Lemma 2.1 (a), used in ES22 Lemma 6.2 Step 0.

In an `Es4Setting` the regenerated walk of the good version `cycNgood N` of the environment
(which equals `N` almost surely) is a family of cyclic paths adapted to `avoidFilt`:
`avoidWalk_cycNgood_adapted : AdaptedCyclic (avoidFilt 𝒢₀ S.space) (avoidWalk (cycNgood N))`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Heavy

open ElboimSly ElboimSly.Paper ElboimSly.Cyclic

variable {d : ℕ} {β : ℝ} [Fact (0 < β)] {n₀ n : ℕ} {t₀ : ℝ}
  {Ω : Type} {𝒢₀ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {Pr : Measure Ω}
  {N N' : Ω → Measure (CycS ℕ d β)}

omit mΩ in
theorem avoidWalk_cycNgood_eq_recWalkAt (N : Ω → Measure (CycS ℕ d β)) (T : Ω → WithTop ℝ≥0)
    (ω : Ω) {x : ℝ≥0} (hx : x ≤ ElboimSly.SRW.stopReal T ω) :
    avoidWalk (cycNgood N) ω (x : ℝ) = recWalkAt (regPlan d β).junk x
      (cycRecStop (regPlan d β) (cycNgood N) T ω) := by
  have hgood := cycGood_cycNgood N ω
  simp only [cycRecStop]
  rw [recWalkAt_trunc_regPlan hgood _ _ hx, regW_eq_regenWalk hgood]
  simp only [avoidWalk, avoidEnv_eq_cycSlice]

/-- The record at a stopping time is `ℱ_T`-measurable. -/
theorem measurable_rec_stop' (S : Es4Setting d β n₀ n t₀ 𝒢₀ Pr N N') {T : Ω → WithTop ℝ≥0}
    (hT : IsStoppingTime (avoidFilt 𝒢₀ S.space) T) :
    Measurable[hT.measurableSpace] (cycRecStop (regPlan d β) (cycNgood N) T) :=
  measurable_cycRecStop (measurable_trunc_multiFilt (regPlan d β) 𝒢₀ S.space.le Pr
    (measurable_envFinal_cycNgood (regPlan d β) S.space.ppp.measurable)) hT

/-- ES22 Lemma 2.1 (a): `W(s)` is `ℱ_s`-measurable. -/
theorem avoidWalk_cycNgood_measurable (S : Es4Setting d β n₀ n t₀ 𝒢₀ Pr N N') (s : ℝ≥0) :
    Measurable[avoidFilt 𝒢₀ S.space s] (fun ω => avoidWalk (cycNgood N) ω (s : ℝ)) := by
  have hT := isStoppingTime_const (avoidFilt 𝒢₀ S.space) s
  have h := measurable_rec_stop' S hT
  rw [IsStoppingTime.measurableSpace_const] at h
  have e : (fun ω => avoidWalk (cycNgood N) ω (s : ℝ)) = fun ω => recWalkAt (regPlan d β).junk s
      (cycRecStop (regPlan d β) (cycNgood N) (fun _ => (s : WithTop ℝ≥0)) ω) := by
    funext ω
    exact avoidWalk_cycNgood_eq_recWalkAt N _ ω le_rfl
  rw [e]
  exact (measurable_recWalkAt _ s).comp h

/-- ES22 Lemma 2.1 (a): the regenerated walk of the good version is an
adapted family of cyclic paths. -/
theorem avoidWalk_cycNgood_adapted (S : Es4Setting d β n₀ n t₀ 𝒢₀ Pr N N') :
    AdaptedCyclic (avoidFilt 𝒢₀ S.space) (avoidWalk (cycNgood N)) where
  path ω := by
    have hg : ∀ k, Good (avoidEnv (cycNgood N) ω k) := by
      intro k; rw [avoidEnv_eq_cycSlice]; exact cycGood_cycNgood N ω k
    exact isCyclicPath_regenWalk hg
  adapted s := avoidWalk_cycNgood_measurable S s

end ElboimSly.Paper.Heavy
