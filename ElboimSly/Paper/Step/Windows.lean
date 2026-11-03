/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.SRW.AdmissibleSRW
public import ElboimSly.Foundations.SRW.MarkovIndep
public import Mathlib

/-!
# Independent windows of an SRW

Laws in the natural coupling (b), the independence of the windows
`u ↦ (θ_{t_j} X)(u ∧ s_j)` for `t_j + s_j ≤ t_{j+1}`, from `IsSRW.indep_stop_theta`, by induction.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set ElboimSly.SRW
open scoped NNReal

namespace ElboimSly.Paper

variable {d : ℕ}

/-- The window `u ↦ (θ_t γ)(u ∧ s)`. -/
def stepWin (t s : ℝ≥0) (γ : PathSpace d) : PathSpace d := SRW.stopPath s (SRW.theta t γ)

theorem measurable_stepWin (t s : ℝ≥0) : Measurable (stepWin (d := d) t s) :=
  (measurable_stopPath s).comp (measurable_theta t)

theorem stepWin_stopPath {t s T : ℝ≥0} (h : t + s ≤ T) (γ : PathSpace d) :
    stepWin t s (SRW.stopPath T γ) = stepWin t s γ := by
  funext u
  have h1 : min (t + min u s) T = t + min u s :=
    min_eq_left (le_trans (add_le_add le_rfl (min_le_right _ _)) h)
  have h2 : min t T = t := min_eq_left (le_trans le_self_add h)
  simp only [stepWin, SRW.stopPath, SRW.theta]
  rw [h1, h2]

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {Z : Ω → PathSpace d}

/-- The window has the law of the stopped process. -/
theorem map_stepWin (hZ : IsSRW P Z) (t s : ℝ≥0) :
    P.map (fun ω => stepWin t s (Z ω)) = P.map (fun ω => SRW.stopPath s (Z ω)) := by
  have h1 : P.map (fun ω => stepWin t s (Z ω)) =
      (P.map (fun ω => SRW.theta t (Z ω))).map (SRW.stopPath s) := by
    exact (Measure.map_map (measurable_stopPath s) ((measurable_theta t).comp hZ.1)).symm
  rw [h1, hZ.map_theta t, Measure.map_map (measurable_stopPath s) hZ.1]
  rfl

/-- **Independent windows.** If `t_j + s_j ≤ t_{j+1}`, the windows `u ↦ (θ_{t_j} Z)(u ∧ s_j)` of
an SRW are independent. -/
theorem iIndepFun_stepWin (hZ : IsSRW P Z) (t s : ℕ → ℝ≥0) (ht : ∀ j, t j + s j ≤ t (j + 1)) :
    iIndepFun (fun j ω => stepWin (t j) (s j) (Z ω)) P := by
  have := hZ.isProbabilityMeasure
  have hmono : Monotone t := monotone_nat_of_le_succ fun j => le_trans le_self_add (ht j)
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
  intro S
  induction S using Finset.induction_on_max with
  | empty => intro sets hS; simp
  | insert a S hlt ih =>
    intro sets hS
    have haS : a ∉ S := fun h => lt_irrefl _ (hlt a h)
    have hSm : ∀ i ∈ S, MeasurableSet (sets i) := fun i hi => hS i (Finset.mem_insert_of_mem hi)
    have hB : MeasurableSet (⋂ i ∈ S, stepWin (t i) (s i) ⁻¹' sets i) :=
      Finset.measurableSet_biInter S fun i hi => measurable_stepWin _ _ (hSm i hi)
    have hC : MeasurableSet (SRW.stopPath (s a) ⁻¹' sets a) :=
      measurable_stopPath (s a) (hS a (Finset.mem_insert_self _ _))
    have key1 : (⋂ i ∈ S, (fun ω => stepWin (t i) (s i) (Z ω)) ⁻¹' sets i) =
        (fun ω => SRW.stopPath (t a) (Z ω)) ⁻¹' (⋂ i ∈ S, stepWin (t i) (s i) ⁻¹' sets i) := by
      ext ω
      simp only [mem_iInter, mem_preimage]
      refine forall_congr' fun i => forall_congr' fun hi => ?_
      have hle : t i + s i ≤ t a := (ht i).trans (hmono (Nat.succ_le_of_lt (hlt i hi)))
      rw [stepWin_stopPath hle]
    have key2 : (fun ω => stepWin (t a) (s a) (Z ω)) ⁻¹' sets a =
        (fun ω => SRW.theta (t a) (Z ω)) ⁻¹' (SRW.stopPath (s a) ⁻¹' sets a) := rfl
    rw [Finset.set_biInter_insert, Finset.prod_insert haS, inter_comm, key1, key2,
      (hZ.indep_stop_theta (t a)).measure_inter_preimage_eq_mul _ _ hB hC, ← key1, ← key2,
      ih hSm, mul_comm]

end ElboimSly.Paper
