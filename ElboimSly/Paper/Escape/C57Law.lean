/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Escape.PlanFreeze
public import ElboimSly.Paper.Avoid.Claim2Final
public import ElboimSly.Paper.Avoid.Claim3Final
public import ElboimSly.Paper.Avoid.Hyp
public import ElboimSly.Paper.Avoid.CoupleAux
public import Mathlib

/-!
# The regenerated walk of `N''` and the walk of the setting

ES22 Claim 5.7 ("Events"), independence tools.

* `regenW_eq_avoidPath`: `regenW N''` is `avoidPath N''`;
* `map_avoidPath_cycNgood_eq`: the regenerated walks of two PPPs of the same intensity have the same
  law on path space;
* `ae_regenW_eq`: `regenW N''` is a.s. the right-continuous process `avoidPath (cycNgood N'')`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Escape

open ElboimSly.Cyclic ElboimSly.Paper

set_option linter.unusedSectionVars false

variable {d : ℕ} {β : ℝ} [Fact (0 < β)] {Ω : Type*} [MeasurableSpace Ω] {Pr : Measure Ω}
  {N N'' : Ω → Measure (CycS ℕ d β)}

theorem regenW_eq_avoidPath (N'' : Ω → Measure (CycS ℕ d β)) (ω : Ω) :
    regenW N'' ω = avoidPath N'' ω := by
  funext t
  show regenWalk (fun k => cycSlice k (N'' ω)) (t : ℝ) = regenWalk (avoidEnv N'' ω) (t : ℝ)
  rw [avoidEnv_eq_cycSlice]

/-- The path functional `ν ↦ regW (ν or 0)`. -/
noncomputable def regWood : Measure (CycS ℕ d β) → ℝ≥0 → Fin d → ℤ :=
  fun ν => regW (cycNgood (fun ν : Measure (CycS ℕ d β) => ν) ν)

theorem measurable_regWood : Measurable (regWood (d := d) (β := β)) :=
  measurable_regW.comp (measurable_cycNgood measurable_id)

theorem avoidPath_cycNgood_eq (M : Ω → Measure (CycS ℕ d β)) :
    avoidPath (cycNgood M) = fun ω => regWood (M ω) := by
  funext ω
  exact avoidPath_eq_regW (cycGood_cycNgood M ω)

theorem map_avoidPath_cycNgood_eq (hN : IsPoissonPointProcess N (cycIntensity ℕ d β) Pr)
    (hN'' : IsPoissonPointProcess N'' (cycIntensity ℕ d β) Pr) :
    Pr.map (avoidPath (cycNgood N'')) = Pr.map (avoidPath N) := by
  have h1 : Pr.map N'' = Pr.map N := hN.map_eq_map hN''
  rw [avoidPath_cycNgood_eq]
  have h2 : Pr.map (fun ω => regWood (N'' ω)) = Pr.map (fun ω => regWood (N ω)) := by
    have e1 : Pr.map (fun ω => regWood (N'' ω)) = (Pr.map N'').map regWood :=
      (Measure.map_map measurable_regWood hN''.measurable).symm
    have e2 : Pr.map (fun ω => regWood (N ω)) = (Pr.map N).map regWood :=
      (Measure.map_map measurable_regWood hN.measurable).symm
    rw [e1, e2, h1]
  rw [h2, ← avoidPath_cycNgood_eq]
  exact Measure.map_congr ((ae_avoidPath_cycNgood hN).mono fun ω h => h.1.trans h.2.symm)

theorem ae_regenW_eq (hN'' : IsPoissonPointProcess N'' (cycIntensity ℕ d β) Pr) :
    ∀ᵐ ω ∂Pr, regenW N'' ω = avoidPath (cycNgood N'') ω := by
  filter_upwards [ae_avoidPath_cycNgood hN''] with ω h
  rw [regenW_eq_avoidPath]
  exact h.2.trans h.1.symm

end ElboimSly.Paper.Escape
