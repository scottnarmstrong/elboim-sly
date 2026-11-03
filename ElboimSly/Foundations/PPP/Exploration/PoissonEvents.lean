/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.PPP.Exploration.Probe
public import ElboimSly.Foundations.PPP.PoissonFacts
public import ElboimSly.Foundations.PPP.Law
public import ElboimSly.Foundations.PPP.Finite
import Mathlib

/-!
# Probabilities of count events

Elementary consequences of (PPP1)-(PPP2) used in the proof of first-point law of a deterministic probe:
`P(N A = 0) = e^{-μ A}`, `P(N A ≥ 2) ≤ μ(A)²/2`, and the probability that three disjoint sets carry
`0`, `1`, `0` points.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace ElboimSly

variable {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S] {N : Ω → Measure S}
  {μ : Measure S} {P : Measure Ω}

namespace IsPoissonPointProcess

/-- `P(N A = c)` for a finite-mass set `A`. -/
theorem measure_count_eq_natCast_zero (h : IsPoissonPointProcess N μ P) {A : Set S}
    (hA : MeasurableSet A) (hfin : μ A < ∞) : P {ω | N ω A = 0} = expNeg (μ A) := by
  have hm := h.measurable_count hA
  have : {ω | N ω A = 0} = (fun ω => N ω A) ⁻¹' {0} := rfl
  rw [this, ← Measure.map_apply hm (measurableSet_singleton _), h.map_count hA]
  lift μ A to ℝ≥0 using hfin.ne with r hr
  rw [extPoissonMeasure_zero_singleton]
  simp [expNeg]

/-- `P(N A ≥ 2) ≤ μ(A)² / 2`. -/
theorem measure_two_le_count_le (h : IsPoissonPointProcess N μ P) {A : Set S}
    (hA : MeasurableSet A) (hfin : μ A < ∞) :
    P {ω | 2 ≤ N ω A} ≤ ENNReal.ofReal ((μ A).toReal ^ 2 / 2) := by
  have hm := h.measurable_count hA
  have : {ω | 2 ≤ N ω A} = (fun ω => N ω A) ⁻¹' Set.Ici 2 := rfl
  rw [this, ← Measure.map_apply hm measurableSet_Ici, h.map_count hA]
  lift μ A to ℝ≥0 using hfin.ne with r hr
  simpa using extPoissonMeasure_Ici_two_le r

/-- The joint law of the counts of disjoint sets, evaluated on a point. -/
theorem measure_counts_eq (h : IsPoissonPointProcess N μ P) {ι : Type*} [Fintype ι]
    {A : ι → Set S} (hA : ∀ i, MeasurableSet (A i)) (hd : Pairwise (Function.onFun Disjoint A))
    (c : ι → ℝ≥0∞) :
    P {ω | ∀ i, N ω (A i) = c i} = ∏ i, extPoissonMeasure (μ (A i)) {c i} := by
  have hm : Measurable fun ω i => N ω (A i) :=
    Measurable.of_eval fun i => h.measurable_count (hA i)
  have e : {ω | ∀ i, N ω (A i) = c i} =
      (fun ω i => N ω (A i)) ⁻¹' Set.pi Set.univ (fun i => {c i}) := by
    ext ω; simp
  rw [e, ← Measure.map_apply hm (MeasurableSet.univ_pi fun i => measurableSet_singleton _),
    h.map_counts_fintype hA hd, Measure.pi_pi]

/-- Three disjoint finite-mass sets carrying `0`, `1`, `0` points. -/
theorem measure_zero_one_zero (h : IsPoissonPointProcess N μ P) {A₀ A₁ A₂ : Set S}
    (h₀ : MeasurableSet A₀) (h₁ : MeasurableSet A₁) (h₂ : MeasurableSet A₂)
    (d₀₁ : Disjoint A₀ A₁) (d₀₂ : Disjoint A₀ A₂) (d₁₂ : Disjoint A₁ A₂)
    (f₀ : μ A₀ < ∞) (f₁ : μ A₁ < ∞) (f₂ : μ A₂ < ∞) :
    P {ω | N ω A₀ = 0 ∧ N ω A₁ = 1 ∧ N ω A₂ = 0} = μ A₁ * expNeg (μ A₀ + μ A₁ + μ A₂) := by
  let A : Fin 3 → Set S := ![A₀, A₁, A₂]
  let c : Fin 3 → ℝ≥0∞ := ![0, 1, 0]
  have hA : ∀ i, MeasurableSet (A i) := by
    intro i; fin_cases i <;> assumption
  have hd : Pairwise (Function.onFun Disjoint A) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [A, Function.onFun, Disjoint.symm]
  have e : {ω | N ω A₀ = 0 ∧ N ω A₁ = 1 ∧ N ω A₂ = 0} = {ω | ∀ i, N ω (A i) = c i} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Fin.forall_fin_succ]
    simp [A, c]
  rw [e, h.measure_counts_eq hA hd c, Fin.prod_univ_three]
  show extPoissonMeasure (μ A₀) {0} * extPoissonMeasure (μ A₁) {1} *
    extPoissonMeasure (μ A₂) {0} = _
  lift μ A₀ to ℝ≥0 using f₀.ne with a ha
  lift μ A₁ to ℝ≥0 using f₁.ne with b hb
  lift μ A₂ to ℝ≥0 using f₂.ne with c' hc
  rw [extPoissonMeasure_zero_singleton, extPoissonMeasure_one_singleton,
    extPoissonMeasure_zero_singleton]
  have hsum : (a : ℝ≥0∞) + b + c' = ((a + b + c' : ℝ≥0) : ℝ≥0∞) := by push_cast; rfl
  rw [hsum]
  simp only [expNeg, ENNReal.coe_toReal]
  rw [← ENNReal.ofReal_coe_nnreal (p := b), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  have : Real.exp (-((a + b + c' : ℝ≥0) : ℝ)) =
      Real.exp (-a) * Real.exp (-b) * Real.exp (-c') := by
    rw [← Real.exp_add, ← Real.exp_add]; congr 1; push_cast; ring
  rw [this]; ring

end IsPoissonPointProcess

end ElboimSly
