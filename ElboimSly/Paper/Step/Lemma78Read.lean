/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Step.Lemma78CoupleRegion
public import ElboimSly.Foundations.Cyclic.CycSchemeEnvTruncTrunc
public import ElboimSly.Foundations.Cyclic.CycRegionMeas
public import ElboimSly.Foundations.Cyclic.CPathJump
public import Mathlib

/-!
# Reading the two walks of Lemma 7.8 off the truncated record

Setting of Lemma 7.8 (Exploration): `W₁|_{[0,t'_n]}` is `ℱ⁺_0 = ℱ_{t'_n}`-measurable and
`W₂(r)` is `ℱ⁺_t = ℱ_{t'_n + t}`-measurable for `r ≤ t`. For a good configuration,
`Trunc_{t'_n + t}` of the environment record of `𝔭₈` has coordinate `1` equal to `W₂|_{[0,t]}`
(`step78_trunc_coord_one`) and `Trunc_{t'_n}` has coordinate `0` equal to `W₁|_{[0,t'_n]}`
(`step78_trunc_coord_zero`).
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Step

open ElboimSly.Cyclic ElboimSly.Paper

set_option linter.unusedSectionVars false

variable {d : ℕ} {β : ℝ} [Fact (0 < β)] (u : Fin d → ℤ) (q : ℝ) (Tn : ℝ≥0)
  {ν : Measure (Unit × RingSpace d β)}

theorem step78_cum_two (junk : CycEntry Unit d) (ν : Measure (Unit × RingSpace d β)) :
    ((step78Plan d β u q Tn).envFinal ν).cum 2 = ⊤ := by
  have h : ((step78Plan d β u q Tn).envFinal ν).cum 2 =
      ((step78Plan d β u q Tn).envFinal ν).cum 1 +
        ((step78Plan d β u q Tn).envFinal ν).lenAt 1 := by
    simp only [CycRec.cum, Finset.sum_range_succ]
  rw [h, CycRec.lenAt_eq junk, ite_eq_left (by rw [step78_num_envFinal]; norm_num),
    step78_coord_eq_E junk ν (by norm_num)]
  have : (((step78Plan d β u q Tn).E (step78Rule u q Tn ν) 1).len) = ⊤ :=
    step78_E_one_len u q Tn _
  rw [this, add_top]

include ν in
/-- Coordinate `1` of `Trunc_{t'_n + t}` of the environment record reads `W₂|_{[0,t]}`. -/
theorem step78_trunc_coord_one (hν : CycGood ν) (junk : CycEntry Unit d) (t : ℝ≥0) :
    ((CycRec.trunc (Tn + t) ((step78Plan d β u q Tn).envFinal ν)).coord junk 1).path.fn t =
      ElboimSly.cycWalk (cycSlice () ν) u q (t : ℝ) := by
  set ρ := (step78Plan d β u q Tn).envFinal ν with hρ
  have hs : (1 : ℕ) ∈ ρ.surv (Tn + t) := by
    refine ⟨by rw [hρ, step78_num_envFinal]; norm_num, ?_⟩
    rw [hρ, step78_cum_one junk ν]
    exact_mod_cast le_self_add
  have hn := CycRec.trunc_nth junk (Tn + t) ρ 1
  rw [ite_eq_left hs] at hn
  have hc : (CycRec.trunc (Tn + t) ρ).coord junk 1 =
      CycRec.truncEntry (Tn + t) ρ 1 (ρ.coord junk 1) := by
    unfold CycRec.coord
    rw [hn]; rfl
  rw [hc]
  have h2 : ¬ (ρ.cum (1 + 1) ≤ ((Tn + t : ℝ≥0) : ℝ≥0∞)) := by
    rw [hρ, show (1 + 1 : ℕ) = 2 from rfl, step78_cum_two u q Tn junk ν]
    exact fun h => absurd (top_le_iff.1 h) ENNReal.coe_ne_top
  unfold CycRec.truncEntry
  rw [ite_eq_right h2, hρ, step78_cum_one junk ν, step78_coord_eq_E junk ν (by norm_num)]
  have hsub : ((Tn + t : ℝ≥0) : ℝ≥0∞) - (Tn : ℝ≥0∞) = (t : ℝ≥0∞) := by
    rw [ENNReal.coe_add, ENNReal.add_sub_cancel_left ENNReal.coe_ne_top]
  rw [hsub]
  simp only [CycEntry.cut, CycEntry.path, CycPath.cut]
  rw [step78_cut_fn_coe, min_self]
  exact step78_E_one_path_fn u q Tn hν t

include ν in
/-- Coordinate `0` of `Trunc_{t'_n}` of the environment record reads `W₁|_{[0,t'_n]}`. -/
theorem step78_trunc_coord_zero (hν : CycGood ν) (junk : CycEntry Unit d) {s : ℝ≥0}
    (hs : s ≤ Tn) :
    ((CycRec.trunc Tn ((step78Plan d β u q Tn).envFinal ν)).coord junk 0).path.fn s =
      ElboimSly.cycWalk (cycSlice () ν) 0 0 (s : ℝ) := by
  set ρ := (step78Plan d β u q Tn).envFinal ν with hρ
  have hsv : (0 : ℕ) ∈ ρ.surv Tn := by
    refine ⟨by rw [hρ, step78_num_envFinal]; norm_num, ?_⟩
    rw [hρ, step78_cum_zero]
    exact bot_le
  have hn := CycRec.trunc_nth junk Tn ρ 0
  rw [ite_eq_left hsv] at hn
  have hc : (CycRec.trunc Tn ρ).coord junk 0 = CycRec.truncEntry Tn ρ 0 (ρ.coord junk 0) := by
    unfold CycRec.coord
    rw [hn]; rfl
  rw [hc]
  have h2 : ρ.cum (0 + 1) ≤ (Tn : ℝ≥0∞) := by
    rw [hρ, show (0 + 1 : ℕ) = 1 from rfl, step78_cum_one junk ν]
  unfold CycRec.truncEntry
  rw [ite_eq_left h2, hρ, step78_coord_eq_E junk ν (by norm_num)]
  have := step78_E_zero_path_fn u q Tn hν s
  rw [min_eq_left hs] at this
  exact this

end ElboimSly.Paper.Step

end
