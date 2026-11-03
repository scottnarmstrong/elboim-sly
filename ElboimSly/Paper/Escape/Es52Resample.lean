/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Escape.ResampleTower
public import Mathlib

/-!
# Elementary facts on the resampling probabilities `Φ_X(RM, R)`

* `resPhi_loc`: `Φ_X` depends only on the ring measure and the explored region
  (resampling formula (c)), also for different plans and times;
* `resampleProb_sum_le_lintegral`: for pairwise disjoint measurable `X_i` on which a function is
  at least `1`, `Σ_i Φ_{X_i} ≤ ∫ f(RM + ν|_{R^c}) dΛ`;
* `resampleProb_biUnion_le`, `resampleProb_compl`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Escape

open ElboimSly.Cyclic ElboimSly.Paper

section generic

variable {I : Type*} [MeasurableSpace I] [Countable I] [MeasurableSingletonClass I] {d : ℕ}
  {β : ℝ} [Fact (0 < β)]

omit [Countable I] [MeasurableSingletonClass I] [Fact (0 < β)] in
/-- The resampling map `ν ↦ RM + ν|_{R^c}` is measurable. -/
theorem measurable_resampleMap (M : Measure (CycS I d β)) {R : Set (CycS I d β)}
    (hR : MeasurableSet R) :
    Measurable fun ν : Measure (CycS I d β) => M + ν.restrict Rᶜ :=
  measurable_add_measure.comp (measurable_const.prodMk (measurable_restrict_set hR.compl))

omit [Countable I] [MeasurableSingletonClass I] [Fact (0 < β)] in
theorem resampleProb_biUnion_le (Λ : Measure (Measure (CycS I d β))) (M : Measure (CycS I d β))
    (R : Set (CycS I d β)) {ι : Type*} (S : Finset ι) (X : ι → Set (Measure (CycS I d β))) :
    resampleProb Λ M R (⋃ i ∈ S, X i) ≤ ∑ i ∈ S, resampleProb Λ M R (X i) := by
  unfold resampleProb
  have : {ν : Measure (CycS I d β) | M + ν.restrict Rᶜ ∈ ⋃ i ∈ S, X i} =
      ⋃ i ∈ S, {ν | M + ν.restrict Rᶜ ∈ X i} := by
    ext ν; simp
  rw [this]
  exact measure_biUnion_finset_le S _

omit [Countable I] [MeasurableSingletonClass I] [Fact (0 < β)] in
theorem resampleProb_compl (Λ : Measure (Measure (CycS I d β))) [IsProbabilityMeasure Λ]
    (M : Measure (CycS I d β)) {R : Set (CycS I d β)} (hR : MeasurableSet R)
    {X : Set (Measure (CycS I d β))} (hX : MeasurableSet X) :
    resampleProb Λ M R Xᶜ = 1 - resampleProb Λ M R X := by
  unfold resampleProb
  have h := measurable_resampleMap M hR
  have : {ν : Measure (CycS I d β) | M + ν.restrict Rᶜ ∈ Xᶜ} =
      {ν | M + ν.restrict Rᶜ ∈ X}ᶜ := by ext ν; simp
  rw [this]
  exact prob_compl_eq_one_sub (h hX)

omit [Countable I] [MeasurableSingletonClass I] [Fact (0 < β)] in
theorem resampleProb_sum_le_lintegral (Λ : Measure (Measure (CycS I d β)))
    (M : Measure (CycS I d β)) {R : Set (CycS I d β)} (hR : MeasurableSet R) {ι : Type*}
    (S : Finset ι) (X : ι → Set (Measure (CycS I d β))) (hX : ∀ i ∈ S, MeasurableSet (X i))
    (hdisj : (S : Set ι).PairwiseDisjoint X) (f : Measure (CycS I d β) → ℝ≥0∞)
    (hf : ∀ i ∈ S, ∀ μ ∈ X i, 1 ≤ f μ) :
    ∑ i ∈ S, resampleProb Λ M R (X i) ≤ ∫⁻ ν, f (M + ν.restrict Rᶜ) ∂Λ := by
  have h := measurable_resampleMap M hR
  set ρ : Measure (CycS I d β) → Measure (CycS I d β) := fun ν => M + ν.restrict Rᶜ with hρ
  have hm : ∀ i ∈ S, MeasurableSet (ρ ⁻¹' X i) := fun i hi => h (hX i hi)
  have hd : (S : Set ι).PairwiseDisjoint fun i => ρ ⁻¹' X i := fun i hi j hj hij =>
    (hdisj hi hj hij).preimage ρ
  have e : ∑ i ∈ S, resampleProb Λ M R (X i) = Λ (⋃ i ∈ S, ρ ⁻¹' X i) := by
    rw [measure_biUnion_finset hd hm]; rfl
  rw [e, ← lintegral_indicator_one₀ ?_]
  · refine lintegral_mono fun ν => ?_
    by_cases hν : ν ∈ ⋃ i ∈ S, ρ ⁻¹' X i
    · rw [Set.indicator_of_mem hν]
      simp only [mem_iUnion] at hν
      obtain ⟨i, hi, hν⟩ := hν
      exact hf i hi _ hν
    · rw [Set.indicator_of_notMem hν]; exact zero_le
  · exact (Finset.measurableSet_biUnion S hm).nullMeasurableSet

omit [Countable I] [MeasurableSingletonClass I] [Fact (0 < β)] in
/-- `Φ_X` of two records with the same ring measure and the same explored region agree
(different plans and stopping times). -/
theorem resPhi_loc {Ω : Type*} [MeasurableSpace Ω] {P Q : CycPlan I d β}
    {N : Ω → Measure (CycS I d β)} {Pr : Measure Ω} {T T' : Ω → WithTop ℝ≥0} {ω : Ω}
    (hT : T ω ≠ ⊤) (hT' : T' ω ≠ ⊤)
    (hrm : (cycRecStop P (cycNgood N) T ω).rm β = (cycRecStop Q (cycNgood N) T' ω).rm β)
    (hreg : (cycRecStop P (cycNgood N) T ω).region β = (cycRecStop Q (cycNgood N) T' ω).region β)
    (X : Set (Measure (CycS I d β))) :
    resPhi P Pr N T X ω = resPhi Q Pr N T' X ω := by
  unfold resPhi
  refine es4_resample_c hrm ?_ X
  ext x
  rw [mem_cycRegionStop_iff, mem_cycRegionStop_iff, hreg]
  simp [hT, hT']

end generic

end ElboimSly.Paper.Escape
