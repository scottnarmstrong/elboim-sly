/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.SRW.AdmissibleSRW
public import ElboimSly.Foundations.SRW.Law1dFormula
public import Mathlib

/-!
# The reflection step of Lévy's maximal inequality

L'evy's maximal inequality (the discrete step: events decided at a time `τ`, independence of the
future increment from the past by the Markov property at fixed times, and `P(increment ∈ C) ≥ 1/2`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ElboimSly
namespace SRW

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- The discrete Lévy step.  Pairwise disjoint events `B i`, decided at time `τ i`, with a future
increment set `C i` of probability at least `1/2` that completes them into `E` at time `T`. -/
theorem IsSRW.levy_step {Y : Ω → PathSpace 1} (hY : IsSRW P Y) {T : ℝ≥0} {ι : Type*}
    (I : Finset ι) (τ : ι → ℝ≥0) (hτ : ∀ i ∈ I, τ i ≤ T) (B : ι → Set (PathSpace 1))
    (hB : ∀ i, MeasurableSet (B i)) (hBstop : ∀ i γ, γ ∈ B i ↔ stopPath (τ i) γ ∈ B i)
    (hdisj : (I : Set ι).PairwiseDisjoint B) (C : ι → Set ℤ)
    (hC : ∀ i ∈ I, 1 ≤ 2 * P {ω | Y ω (T - τ i) 0 ∈ C i}) (E : Set ℤ)
    (hE : ∀ i ∈ I, ∀ γ ∈ B i, ∀ x ∈ C i, γ (τ i) 0 + x ∈ E) :
    P (Y ⁻¹' ⋃ i ∈ I, B i) ≤ 2 * P {ω | Y ω T 0 ∈ E} := by
  have := hY.isProbabilityMeasure
  have hYm : ∀ i, MeasurableSet (Y ⁻¹' B i) := fun i => hY.1 (hB i)
  have hCm : ∀ i, MeasurableSet {γ : PathSpace 1 | γ (T - τ i) 0 ∈ C i} := fun i =>
    ((measurable_pi_apply (0 : Fin 1)).comp (measurable_pi_apply (T - τ i)))
      (Set.to_countable (C i)).measurableSet
  -- the future events
  set D : ι → Set Ω := fun i => (fun ω => theta (τ i) (Y ω)) ⁻¹' {γ | γ (T - τ i) 0 ∈ C i} with hD
  have hDm : ∀ i, MeasurableSet (D i) := fun i =>
    ((measurable_theta (τ i)).comp hY.1) (hCm i)
  have hDP : ∀ i, P (D i) = P {ω | Y ω (T - τ i) 0 ∈ C i} := by
    intro i
    have h1 : P (D i) = (P.map fun ω => theta (τ i) (Y ω)) {γ | γ (T - τ i) 0 ∈ C i} := by
      rw [Measure.map_apply (f := fun ω => theta (τ i) (Y ω))
        ((measurable_theta (τ i)).comp hY.1) (hCm i)]
    rw [h1, hY.map_theta, Measure.map_apply hY.1 (hCm i)]; rfl
  have hind : ∀ i, P (Y ⁻¹' B i ∩ D i) = P (Y ⁻¹' B i) * P (D i) := by
    intro i
    have hi := hY.indep_stop_theta (τ i)
    have e : Y ⁻¹' B i = (fun ω => stopPath (τ i) (Y ω)) ⁻¹' B i := by
      ext ω; exact hBstop i (Y ω)
    rw [e]
    exact hi.measure_inter_preimage_eq_mul _ _ (hB i) (hCm i)
  have hsub : (⋃ i ∈ I, (Y ⁻¹' B i ∩ D i)) ⊆ {ω | Y ω T 0 ∈ E} := by
    intro ω hω
    simp only [mem_iUnion] at hω
    obtain ⟨i, hi, hb, hd⟩ := hω
    have hxe := hE i hi (Y ω) hb _ hd
    have : Y ω T 0 = Y ω (τ i) 0 + theta (τ i) (Y ω) (T - τ i) 0 := by
      simp only [theta, Pi.sub_apply, add_tsub_cancel_of_le (hτ i hi)]
      ring
    simpa [this] using hxe
  have hdisj1 : (I : Set ι).PairwiseDisjoint fun i => Y ⁻¹' B i :=
    fun i hi j hj hij => (hdisj hi hj hij).preimage Y
  have hdisj2 : (I : Set ι).PairwiseDisjoint fun i => Y ⁻¹' B i ∩ D i :=
    fun i hi j hj hij => (hdisj1 hi hj hij).mono inter_subset_left inter_subset_left
  have e1 : Y ⁻¹' ⋃ i ∈ I, B i = ⋃ i ∈ I, Y ⁻¹' B i := by simp [preimage_iUnion]
  rw [e1, measure_biUnion_finset hdisj1 (fun i _ => hYm i)]
  calc ∑ i ∈ I, P (Y ⁻¹' B i)
      ≤ ∑ i ∈ I, 2 * P (Y ⁻¹' B i ∩ D i) := by
        refine Finset.sum_le_sum fun i hi => ?_
        rw [hind i, hDP i, mul_left_comm]
        calc P (Y ⁻¹' B i) = P (Y ⁻¹' B i) * 1 := (mul_one _).symm
          _ ≤ P (Y ⁻¹' B i) * (2 * P {ω | Y ω (T - τ i) 0 ∈ C i}) := by gcongr; exact hC i hi
    _ = 2 * ∑ i ∈ I, P (Y ⁻¹' B i ∩ D i) := by rw [Finset.mul_sum]
    _ = 2 * P (⋃ i ∈ I, (Y ⁻¹' B i ∩ D i)) := by
        rw [measure_biUnion_finset hdisj2 (fun i _ => (hYm i).inter (hDm i))]
    _ ≤ 2 * P {ω | Y ω T 0 ∈ E} := by gcongr

end SRW
end ElboimSly
