/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Avoid.Lem41
public import ElboimSly.Paper.Escape.C56Glue
public import ElboimSly.Foundations.Cyclic.CPathStop
public import Mathlib

/-!
# The regenerated walk as an adapted `CPath` process (for ES22 Claim 5.6)

* `escW N`: the regenerated walk of the good version `cycNgood N`, as a path on `ℝ≥0`.
* `escCPath N ω`: the same as a `CPath` (right-continuous, finitely many jumps).
* `escW_adapted`: `W(s)` is `avoidFilt s`-measurable.
* `escW_hist`: for a stopping time `T` and an `ℱ_T`-measurable `0 ≤ a ≤ T`, the history
  `(ω, s) ↦ W(min(a + max s 0, T))` is jointly `ℱ_T ⊗ Borel`-measurable.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Escape

open ElboimSly.Cyclic ElboimSly.Paper

variable {d : ℕ} {β : ℝ} [Fact (0 < β)] {n₀ n : ℕ} {t₀ : ℝ}
  {Ω : Type} {𝒢₀ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {Pr : Measure Ω}
  {N N' : Ω → Measure (CycS ℕ d β)}

/-- The regenerated walk of the good version of the environment, on `ℝ≥0`. -/
noncomputable def escW (N : Ω → Measure (CycS ℕ d β)) (ω : Ω) : ℝ≥0 → Fin d → ℤ :=
  avoidPath (cycNgood N) ω

omit mΩ in
theorem isRegPath_escW (N : Ω → Measure (CycS ℕ d β)) (ω : Ω) : IsRegPath (escW N ω) := by
  have h := isRegPath_regenWalk (cycGood_cycNgood N ω)
  have e : escW N ω = fun t : ℝ≥0 => ElboimSly.regenWalk (fun k => cycSlice k (cycNgood N ω))
      (t : ℝ) := by
    funext t
    simp only [escW, avoidPath, avoidWalk, avoidEnv_eq_cycSlice]
  rw [e]; exact h

/-- The regenerated walk as a `CPath`. -/
noncomputable def escCPath (N : Ω → Measure (CycS ℕ d β)) (ω : Ω) : CPath (Fin d → ℤ) :=
  mkCPath (escW N ω) (isRegPath_escW N ω)

omit mΩ in
@[simp] theorem escCPath_fn (N : Ω → Measure (CycS ℕ d β)) (ω : Ω) :
    (escCPath N ω).fn = escW N ω := rfl

omit mΩ in
/-- The walk up to `T` is read off the stopped record. -/
theorem escW_eq_recWalkAt (N : Ω → Measure (CycS ℕ d β)) (T : Ω → WithTop ℝ≥0) (ω : Ω)
    {x : ℝ≥0} (hx : x ≤ ElboimSly.SRW.stopReal T ω) :
    escW N ω x = recWalkAt (regPlan d β).junk x
      (cycRecStop (regPlan d β) (cycNgood N) T ω) := by
  have hgood := cycGood_cycNgood N ω
  simp only [cycRecStop]
  rw [recWalkAt_trunc_regPlan hgood _ _ hx, regW_eq_regenWalk hgood]
  simp only [escW, avoidPath, avoidWalk, avoidEnv_eq_cycSlice]

variable (S : Es4Setting d β n₀ n t₀ 𝒢₀ Pr N N')

include S in
/-- The record at a stopping time is `ℱ_T`-measurable. -/
theorem measurable_rec_stop {T : Ω → WithTop ℝ≥0} (hT : IsStoppingTime (avoidFilt 𝒢₀ S.space) T) :
    Measurable[hT.measurableSpace] (cycRecStop (regPlan d β) (cycNgood N) T) :=
  measurable_cycRecStop (measurable_trunc_multiFilt (regPlan d β) 𝒢₀ S.space.le Pr
    (measurable_envFinal_cycNgood (regPlan d β) S.space.ppp.measurable)) hT

include S in
/-- **Adaptedness.** `W(s)` is `ℱ_s`-measurable. -/
theorem escW_adapted (s : ℝ≥0) : Measurable[avoidFilt 𝒢₀ S.space s] (fun ω => escW N ω s) := by
  have hT := isStoppingTime_const (avoidFilt 𝒢₀ S.space) s
  have h := measurable_rec_stop S hT
  rw [IsStoppingTime.measurableSpace_const] at h
  have e : (fun ω => escW N ω s) = fun ω => recWalkAt (regPlan d β).junk s
      (cycRecStop (regPlan d β) (cycNgood N) (fun _ => (s : WithTop ℝ≥0)) ω) := by
    funext ω
    refine escW_eq_recWalkAt N _ ω ?_
    exact le_of_eq rfl
  rw [e]
  exact (measurable_recWalkAt _ s).comp h

include S in
/-- The history of the walk up to a stopping time is jointly measurable. -/
theorem escW_hist {T : Ω → WithTop ℝ≥0} (hT : IsStoppingTime (avoidFilt 𝒢₀ S.space) T)
    {a : Ω → ℝ} (ha : Measurable[hT.measurableSpace] a) (ha0 : ∀ ω, 0 ≤ a ω)
    (haT : ∀ ω, a ω ≤ ((ElboimSly.SRW.stopReal T ω : ℝ≥0) : ℝ)) :
    Measurable[hT.measurableSpace.prod inferInstance] (fun p : Ω × ℝ =>
      escW N p.1 (min (a p.1 + max p.2 0) ((ElboimSly.SRW.stopReal T p.1 : ℝ≥0) : ℝ)).toNNReal) := by
  have hρ := measurable_rec_stop S hT
  have hTrm : Measurable[hT.measurableSpace]
      (fun ω => ((ElboimSly.SRW.stopReal T ω : ℝ≥0) : ℝ)) :=
    (measurable_stopReal_stop hT).coe_nnreal_real
  have := measurable_hist_rec hT.measurableSpace (regPlan d β).junk _ hρ a _ ha hTrm
  have e : (fun p : Ω × ℝ => escW N p.1
      (min (a p.1 + max p.2 0) ((ElboimSly.SRW.stopReal T p.1 : ℝ≥0) : ℝ)).toNNReal) =
      fun p => recWalkAt (regPlan d β).junk
        (min (a p.1 + max p.2 0) ((ElboimSly.SRW.stopReal T p.1 : ℝ≥0) : ℝ)).toNNReal
        (cycRecStop (regPlan d β) (cycNgood N) T p.1) := by
    funext p
    refine escW_eq_recWalkAt N T p.1 ?_
    rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ (le_min (by linarith [ha0 p.1, le_max_right p.2 0])
      ((ha0 p.1).trans (haT p.1)))]
    exact min_le_right _ _
  rw [e]
  exact this

end ElboimSly.Paper.Escape

end
