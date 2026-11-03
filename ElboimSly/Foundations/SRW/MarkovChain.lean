/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.SRW.KernelBasic
public import Mathlib

/-!
# Independent consecutive windows

A generic product formula for events living in consecutive time windows of an SRW, obtained by
iterating the Markov property at the deterministic times `ρ_0`, `ρ_0 + ρ_1`,...
Used in escape from the boundary.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal

namespace ElboimSly
namespace SRW

variable {d : ℕ}

/-- The set of paths whose consecutive windows `k, k+1,..., k+n-1` (of lengths `ρ k,...`) lie in
the sets `S k,...` (each applied to the stopped shifted path). -/
def Gfrom (ρ : ℕ → ℝ≥0) (S : ℕ → Set (PathSpace d)) : ℕ → ℕ → Set (PathSpace d)
  | _, 0 => univ
  | k, n + 1 => {β | stopPath (ρ k) β ∈ S k ∧ theta (ρ k) β ∈ Gfrom ρ S (k + 1) n}

theorem measurable_Gfrom {ρ : ℕ → ℝ≥0} {S : ℕ → Set (PathSpace d)}
    (hS : ∀ k, MeasurableSet (S k)) : ∀ n k, MeasurableSet (Gfrom ρ S k n)
  | 0, _ => MeasurableSet.univ
  | n + 1, k => by
    have h1 : MeasurableSet {β : PathSpace d | stopPath (ρ k) β ∈ S k} :=
      (measurable_stopPath (ρ k)) (hS k)
    have h2 : MeasurableSet {β : PathSpace d | theta (ρ k) β ∈ Gfrom ρ S (k + 1) n} :=
      (measurable_theta (ρ k)) (measurable_Gfrom hS n (k + 1))
    exact h1.inter h2

/-- Product formula for consecutive windows. -/
theorem IsSRW.real_Gfrom {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {Y : Ω → PathSpace d}
    (hY : IsSRW P Y) {ρ : ℕ → ℝ≥0} {S : ℕ → Set (PathSpace d)} (hS : ∀ k, MeasurableSet (S k)) :
    ∀ n k, P.real {ω | Y ω ∈ Gfrom ρ S k n} =
      ∏ i ∈ Finset.range n, P.real {ω | stopPath (ρ (k + i)) (Y ω) ∈ S (k + i)}
  | 0, k => by
    have := hY.isProbabilityMeasure
    simp [Gfrom]
  | n + 1, k => by
    have := hY.isProbabilityMeasure
    have hind := hY.indep_stop_theta (ρ k)
    have e : {ω | Y ω ∈ Gfrom ρ S k (n + 1)} =
        (fun ω => stopPath (ρ k) (Y ω)) ⁻¹' S k ∩
          (fun ω => SRW.theta (ρ k) (Y ω)) ⁻¹' Gfrom ρ S (k + 1) n := by
      ext ω; simp [Gfrom]
    rw [e, measureReal_def, (indepFun_iff_measure_inter_preimage_eq_mul.1 hind) _ _ (hS k)
      (measurable_Gfrom hS n (k + 1)), ENNReal.toReal_mul, Finset.prod_range_succ']
    have h2 : P ((fun ω => SRW.theta (ρ k) (Y ω)) ⁻¹' Gfrom ρ S (k + 1) n) =
        P (Y ⁻¹' Gfrom ρ S (k + 1) n) := by
      have hG := measurable_Gfrom (ρ := ρ) hS n (k + 1)
      calc P ((fun ω => SRW.theta (ρ k) (Y ω)) ⁻¹' Gfrom ρ S (k + 1) n)
          = (P.map fun ω => SRW.theta (ρ k) (Y ω)) (Gfrom ρ S (k + 1) n) :=
            (Measure.map_apply ((measurable_theta (ρ k)).comp hY.1) hG).symm
        _ = (P.map Y) (Gfrom ρ S (k + 1) n) := by rw [hY.map_theta]
        _ = _ := Measure.map_apply hY.1 hG
    rw [h2, mul_comm]
    congr 1
    · have := hY.real_Gfrom (ρ := ρ) hS n (k + 1)
      rw [measureReal_def] at this
      refine this.trans (Finset.prod_congr rfl fun i _ => ?_)
      rw [show k + 1 + i = k + (i + 1) by omega]

end SRW
end ElboimSly
