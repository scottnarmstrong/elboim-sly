/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycRegenLaw
public import ElboimSly.Frozen.Defs.CopyEnv
public import ElboimSly.Frozen.Defs.RegenWalk
public import Mathlib

/-!
# Almost-sure measurability of the regenerated path

For a Poisson environment sequence `N` the path `ω ↦ (t ↦ W_reg(ω, t))` of the regenerated walk of the
copies `copyEnv (N ω) k` is almost-everywhere measurable into the path space `ℝ≥0 → ℤ^d` (product
σ-algebra), and so is its restriction to any set of times. It agrees almost surely with the walk
`regRecProc` of the environment final record of the regenerated plan, which is measurable.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal ENNReal

namespace ElboimSly.Paper

variable {d : ℕ} {β : ℝ} [Fact (0 < β)]

omit [Fact (0 < β)] in
/-- The copies `copyEnv (N ω) k` are the slices `cycSlice k (N ω)`. -/
theorem copyEnv_eq_cycSlice (ν : Measure (ℕ × RingSpace d β)) (k : ℕ) :
    copyEnv ν k = Cyclic.cycSlice k ν :=
  (Cyclic.cycSlice_eq_map_restrict k ν).symm

/-- The regenerated path of a Poisson environment sequence is almost-everywhere measurable. -/
theorem aemeasurable_regenWalk_path {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {N : Ω → Measure (ℕ × RingSpace d β)}
    (hN : IsPoissonPointProcess N ((Measure.count : Measure ℕ).prod (ringIntensity d β)) P) :
    AEMeasurable (fun ω (t : ℝ≥0) => regenWalk (fun k => copyEnv (N ω) k) (t : ℝ)) P := by
  have : Nonempty (Cyclic.CycEntry ℕ d) := ⟨(Cyclic.regPlan d β).junk⟩
  have hm : Measurable fun ω => Cyclic.regRecProc
      ((Cyclic.regPlan d β).envFinalOr Cyclic.CycRec.empty (N ω)) :=
    Cyclic.measurable_regRecProc.comp
      (((Cyclic.regPlan d β).measurable_envFinalOr Cyclic.CycRec.empty).comp hN.1)
  refine hm.aemeasurable.congr ?_
  filter_upwards [Cyclic.regen_env_ae hN] with ω h
  simpa only [copyEnv_eq_cycSlice] using h.symm

/-- Restriction of the regenerated path to the times `[0, T]`: the hypothesis `hFae` of
`step_second_moment_of_ae`. -/
theorem aemeasurable_regenWalk_Icc {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {N : Ω → Measure (ℕ × RingSpace d β)}
    (hN : IsPoissonPointProcess N ((Measure.count : Measure ℕ).prod (ringIntensity d β)) P)
    (T : ℝ≥0) :
    AEMeasurable (fun ω (t : Set.Icc (0 : ℝ≥0) T) =>
      regenWalk (fun k => copyEnv (N ω) k) ((t : ℝ≥0) : ℝ)) P :=
  (measurable_pi_iff.2 fun t : Set.Icc (0 : ℝ≥0) T => measurable_pi_apply (t : ℝ≥0)).comp_aemeasurable
    (aemeasurable_regenWalk_path hN)

end ElboimSly.Paper
