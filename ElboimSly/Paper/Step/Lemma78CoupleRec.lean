/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Step.Lemma78CouplePlan
public import ElboimSly.Foundations.Cyclic.CycSchemeEnvFinalNth
public import ElboimSly.Foundations.Cyclic.CycRecCoords
public import Mathlib

/-!
# The environment record of the plan `𝔭₈`

Setting of Lemma 7.8 (Exploration): the environment world-lines of `𝔭₈` are
`W₁|_{[0,t'_n]}` and `W₂`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Step

open ElboimSly.Cyclic ElboimSly.Paper

set_option linter.unusedSectionVars false

theorem step78_cut_fn_coe {V : Type*} (p : CPath V) (L s : ℝ≥0) :
    (p.cut (L : ℝ≥0∞)).fn s = p.fn (min s L) := by
  rw [CPath.cut_fn]
  congr 1

variable {d : ℕ} {β : ℝ} [Fact (0 < β)] (u : Fin d → ℤ) (q : ℝ) (Tn : ℝ≥0)

theorem step78_E_zero_len (path : PathRule Unit d) :
    ((step78Plan d β u q Tn).E path 0).len = Tn := by
  unfold CycPlan.E CycPlan.nextEntry
  simp only [CycEntry.len, CycPath.cut]
  rw [step78Plan_stopLen_zero]
  exact CPath.cut_len _ _

theorem step78_E_zero_fn (path : PathRule Unit d) (s : ℝ≥0) :
    ((step78Plan d β u q Tn).E path 0).path.fn s =
      (path 0 ((step78Plan d β u q Tn).ideal path 0)).1.fn (min s Tn) := by
  unfold CycPlan.E CycPlan.nextEntry
  simp only [CycEntry.path, CycPath.cut]
  rw [step78Plan_stopLen_zero]
  exact step78_cut_fn_coe _ _ _

theorem step78_E_one_len (path : PathRule Unit d) :
    ((step78Plan d β u q Tn).E path 1).len = ⊤ := by
  unfold CycPlan.E CycPlan.nextEntry
  simp only [CycEntry.len, CycPath.cut]
  rw [step78Plan_stopLen_succ, CPath.cut_len]

theorem step78_E_one_fn (path : PathRule Unit d) (s : ℝ≥0) :
    ((step78Plan d β u q Tn).E path 1).path.fn s =
      (path 1 ((step78Plan d β u q Tn).ideal path 1)).1.fn s := by
  unfold CycPlan.E CycPlan.nextEntry
  simp only [CycEntry.path, CycPath.cut]
  rw [step78Plan_stopLen_succ, CPath.cut_fn]
  simp


theorem step78_envFn_fwd (ν : Measure (Unit × RingSpace d β)) (δ : CycData Unit d)
    (hf : δ.fwd = true) (s : ℝ≥0) :
    envFn ν δ s = ElboimSly.cycWalk (cycSlice () ν) δ.start δ.phase (s : ℝ) := by
  unfold envFn ElboimSly.cycWalk
  have h0 : (0 : ℝ) ≤ s := s.2
  simp only [h0, ↓reduceIte]
  rw [Real.toNNReal_coe]
  simp [envMeasure, hf, CycData.copy, CycData.sgn]

section rec

variable {ν : Measure (Unit × RingSpace d β)} (hν : CycGood ν) (junk : CycEntry Unit d)

include hν in
/-- The environment record, walk 1. -/
theorem step78_E_zero_path_fn (s : ℝ≥0) :
    ((step78Plan d β u q Tn).E (fun k ρ => envPath ν ((step78Plan d β u q Tn).start k ρ)) 0).path.fn s =
      ElboimSly.cycWalk (cycSlice () ν) 0 0 ((min s Tn : ℝ≥0) : ℝ) := by
  rw [step78_E_zero_fn]
  have := (envPath_len (δ := (step78Plan d β u q Tn).start 0
    ((step78Plan d β u q Tn).ideal (fun k ρ => envPath ν ((step78Plan d β u q Tn).start k ρ)) 0))
    (hν ())).2
  show (envPath ν _).1.fn _ = _
  rw [this, step78_envFn_fwd]
  · rfl
  · rfl

include hν in
theorem step78_E_one_path_fn (s : ℝ≥0) :
    ((step78Plan d β u q Tn).E (fun k ρ => envPath ν ((step78Plan d β u q Tn).start k ρ)) 1).path.fn s =
      ElboimSly.cycWalk (cycSlice () ν) u q (s : ℝ) := by
  rw [step78_E_one_fn]
  have := (envPath_len (δ := (step78Plan d β u q Tn).start 1
    ((step78Plan d β u q Tn).ideal (fun k ρ => envPath ν ((step78Plan d β u q Tn).start k ρ)) 1))
    (hν ())).2
  show (envPath ν _).1.fn _ = _
  rw [this, step78_envFn_fwd]
  · rfl
  · rfl

end rec

end ElboimSly.Paper.Step

end
