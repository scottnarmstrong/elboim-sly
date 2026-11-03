/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.SRW.KernelDef
public import ElboimSly.Foundations.SRW.Symmetry
public import ElboimSly.Foundations.SRW.StoppedPosition
public import ElboimSly.Foundations.SRW.Modulus
public import Mathlib

/-!
# Confined kernels: monotonicity, invariance, mass, Chapman--Kolmogorov

Properties of confined kernels (b), (d), (e), (f).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal

namespace ElboimSly
namespace SRW

variable {d : ℕ}

theorem IsSRW.measurableSet_event {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {Z : Ω → PathSpace d} (hZ : IsSRW P Z) {Γ : Set (PathSpace d)} (hΓ : IsRegSet Γ) :
    MeasurableSet {ω | Z ω ∈ Γ} := by
  obtain ⟨Γ', h1, h2⟩ := hΓ
  have : {ω | Z ω ∈ Γ} = Z ⁻¹' Γ' := by
    ext ω; exact h2 _ (hZ.2.1 ω)
  rw [this]; exact hZ.1 h1

theorem kernel_nonneg (Q : Set (Fin d → ℤ)) (r : ℝ≥0) (x z : Fin d → ℤ) :
    0 ≤ kernel Q r x z := ENNReal.toReal_nonneg

/-- Properties of confined kernels (d): monotonicity in the set. -/
theorem kernel_mono {Q Q' : Set (Fin d → ℤ)} (h : Q ⊆ Q') (r : ℝ≥0) (x z : Fin d → ℤ) :
    kernel Q r x z ≤ kernel Q' r x z := by
  have := (srwZ_isSRW d).isProbabilityMeasure
  refine ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono fun ω hω => ?_)
  exact ⟨hω.1, fun s hs => h (hω.2 s hs)⟩

/-- Properties of confined kernels (e), translation. -/
theorem kernel_translate (Q : Set (Fin d → ℤ)) (y : Fin d → ℤ) (r : ℝ≥0) (x z : Fin d → ℤ) :
    kernel ((fun q => q + y) '' Q) r (x + y) (z + y) = kernel Q r x z := by
  have h : kerSet ((fun q => q + y) '' Q) r (x + y) (z + y) = kerSet Q r x z := by
    ext γ
    simp only [kerSet, mem_ofPred_eq]
    refine and_congr ?_ ?_
    · constructor
      · intro h; simpa [add_assoc, add_comm, add_left_comm] using h
      · intro h; rw [← h]; abel
    · refine forall₂_congr fun s _ => ?_
      constructor
      · rintro ⟨q, hq, e⟩
        have : q = x + γ s := by
          have : q + y = x + γ s + y := by
            have e' : q + y = x + y + γ s := e
            rw [e']; abel
          exact add_right_cancel this
        rwa [← this]
      · intro h; exact ⟨_, h, by abel⟩
  unfold kernel
  rw [h]

/-- Properties of confined kernels (f), in the form of a sum: for any SRW, the kernel sums to the
probability of staying in `Q`. -/
theorem IsSRW.tsum_kernel {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {Z : Ω → PathSpace d}
    (hZ : IsSRW P Z) (Q : Set (Fin d → ℤ)) (r : ℝ≥0) (x : Fin d → ℤ) :
    ∑' z, ENNReal.ofReal (kernel Q r x z) = P {ω | ∀ s : ℝ≥0, s ≤ r → x + Z ω s ∈ Q} := by
  have e : {ω | ∀ s : ℝ≥0, s ≤ r → x + Z ω s ∈ Q} =
      ⋃ z, {ω | Z ω ∈ kerSet Q r x z} := by
    ext ω
    simp only [mem_ofPred_eq, mem_iUnion, kerSet]
    exact ⟨fun h => ⟨_, rfl, h⟩, fun ⟨_, _, h⟩ => h⟩
  rw [e, measure_iUnion]
  · exact tsum_congr fun z => (hZ.prob_kerSet Q r x z).symm
  · intro z z' hzz'
    refine Set.disjoint_left.2 fun ω h1 h2 => hzz' ?_
    exact h1.1.symm.trans h2.1
  · exact fun z => hZ.measurableSet_event (isRegSet_kerSet Q r x z)

theorem kernel_tsum_real (Q : Set (Fin d → ℤ)) (r : ℝ≥0) (x : Fin d → ℤ) :
    ∑' z, kernel Q r x z =
      ((srwP d) {ω | ∀ s : ℝ≥0, s ≤ r → x + srwZ d ω s ∈ Q}).toReal ∧
    Summable fun z => kernel Q r x z := by
  have := (srwZ_isSRW d).isProbabilityMeasure
  have h := (srwZ_isSRW d).tsum_kernel Q r x
  have hne : ∑' z, ENNReal.ofReal (kernel Q r x z) ≠ ⊤ := by
    rw [h]; exact measure_ne_top _ _
  have hs : Summable fun z => kernel Q r x z := by
    have := ENNReal.summable_toReal hne
    simpa [ENNReal.toReal_ofReal (kernel_nonneg _ _ _ _)] using this
  refine ⟨?_, hs⟩
  rw [← h, ENNReal.tsum_toReal_eq (fun _ => ENNReal.ofReal_ne_top)]
  exact tsum_congr fun z => (ENNReal.toReal_ofReal (kernel_nonneg _ _ _ _)).symm

/-- Properties of confined kernels (f). -/
theorem kernel_tsum (Q : Set (Fin d → ℤ)) (r : ℝ≥0) (x : Fin d → ℤ) :
    ∑' z, kernel Q r x z =
      ((srwP d) {ω | ∀ s : ℝ≥0, s ≤ r → x + srwZ d ω s ∈ Q}).toReal :=
  (kernel_tsum_real Q r x).1

theorem summable_kernel (Q : Set (Fin d → ℤ)) (r : ℝ≥0) (x : Fin d → ℤ) :
    Summable fun z => kernel Q r x z := (kernel_tsum_real Q r x).2

/-! ### Chapman--Kolmogorov -/

theorem kerSet_stop_iff {γ : PathSpace d} (hγ : IsRegularPath γ) {Q : Set (Fin d → ℤ)} {r : ℝ≥0}
    {x z : Fin d → ℤ} {V : Set (PathSpace d)}
    (hV : ∀ β, IsRegularPath β → (β ∈ kerSet Q r x z ↔ β ∈ V)) :
    γ ∈ kerSet Q r x z ↔ stopPath r γ ∈ V := by
  have hs : IsRegularPath (stopPath r γ) := hγ.stop r
  refine Iff.trans ?_ (hV _ hs)
  simp only [kerSet, stopPath, mem_ofPred_eq, min_self]
  refine and_congr Iff.rfl (forall₂_congr fun s hs => ?_)
  rw [min_eq_left hs]

theorem kerSet_add_iff {γ : PathSpace d} (Q : Set (Fin d → ℤ)) (r₁ r₂ : ℝ≥0) (x z : Fin d → ℤ) :
    γ ∈ kerSet Q (r₁ + r₂) x z ↔
      ∃ w, γ ∈ kerSet Q r₁ x w ∧ theta r₁ γ ∈ kerSet Q r₂ w z := by
  simp only [kerSet, mem_ofPred_eq, theta]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨x + γ r₁, ⟨rfl, fun s hs => h2 s (hs.trans le_self_add)⟩, ?_, fun u hu => ?_⟩
    · rw [← h1]; abel
    · have := h2 (r₁ + u) (by gcongr)
      convert this using 1; abel
  · rintro ⟨w, ⟨h1, h2⟩, h3, h4⟩
    refine ⟨?_, fun s hs => ?_⟩
    · rw [← h3, ← h1]; abel
    · rcases le_or_gt s r₁ with h | h
      · exact h2 s h
      · have hu : s - r₁ ≤ r₂ := by
          rw [tsub_le_iff_left]; exact hs
        have := h4 (s - r₁) hu
        rw [add_tsub_cancel_of_le h.le, ← h1] at this
        convert this using 1; abel

/-- Properties of confined kernels (b), in `ℝ≥0∞`: Chapman--Kolmogorov. -/
theorem ofReal_kernel_add (Q : Set (Fin d → ℤ)) (r₁ r₂ : ℝ≥0) (x z : Fin d → ℤ) :
    ENNReal.ofReal (kernel Q (r₁ + r₂) x z) =
      ∑' w, ENNReal.ofReal (kernel Q r₁ x w) * ENNReal.ofReal (kernel Q r₂ w z) := by
  have hZ := srwZ_isSRW d
  have := hZ.isProbabilityMeasure
  choose V hVm hV using fun w => isRegSet_kerSet Q r₁ x w
  choose U hUm hU using fun w => isRegSet_kerSet Q r₂ w z
  have hind := hZ.indep_stop_theta r₁
  have e : {ω | srwZ d ω ∈ kerSet Q (r₁ + r₂) x z} =
      ⋃ w, ((fun ω => stopPath r₁ (srwZ d ω)) ⁻¹' V w ∩
        (fun ω => theta r₁ (srwZ d ω)) ⁻¹' U w) := by
    ext ω
    have hγ := hZ.2.1 ω
    simp only [mem_ofPred_eq, mem_iUnion, mem_inter_iff, mem_preimage]
    rw [kerSet_add_iff]
    refine exists_congr fun w => and_congr ?_ ?_
    · exact kerSet_stop_iff hγ (hV w)
    · exact hU w _ (hγ.theta r₁)
  rw [← (hZ.prob_kerSet Q (r₁ + r₂) x z)]
  rw [e, measure_iUnion]
  · refine tsum_congr fun w => ?_
    rw [(indepFun_iff_measure_inter_preimage_eq_mul.1 hind) _ _
      (hVm w) (hUm w)]
    congr 1
    · rw [← hZ.prob_kerSet Q r₁ x w]
      congr 1
      ext ω
      exact (kerSet_stop_iff (hZ.2.1 ω) (hV w)).symm
    · rw [← (hZ.theta r₁).prob_kerSet Q r₂ w z]
      congr 1
      ext ω
      exact (hU w _ ((hZ.2.1 ω).theta r₁)).symm
  · intro w w' hww'
    refine Set.disjoint_left.2 fun ω h1 h2 => hww' ?_
    have a := (kerSet_stop_iff (hZ.2.1 ω) (hV w)).2 h1.1
    have b := (kerSet_stop_iff (hZ.2.1 ω) (hV w')).2 h2.1
    exact a.1.symm.trans b.1
  · intro w
    refine MeasurableSet.inter ?_ ?_
    · exact ((measurable_stopPath r₁).comp hZ.1) (hVm w)
    · exact ((measurable_theta r₁).comp hZ.1) (hUm w)

/-- Properties of confined kernels (b): Chapman--Kolmogorov. -/
theorem kernel_add (Q : Set (Fin d → ℤ)) (r₁ r₂ : ℝ≥0) (x z : Fin d → ℤ) :
    kernel Q (r₁ + r₂) x z = ∑' w, kernel Q r₁ x w * kernel Q r₂ w z := by
  have h := ofReal_kernel_add Q r₁ r₂ x z
  have hne : ∀ w, ENNReal.ofReal (kernel Q r₁ x w) * ENNReal.ofReal (kernel Q r₂ w z) ≠ ⊤ :=
    fun w => ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  have h2 := congrArg ENNReal.toReal h
  rw [ENNReal.toReal_ofReal (kernel_nonneg _ _ _ _), ENNReal.tsum_toReal_eq hne] at h2
  rw [h2]
  refine tsum_congr fun w => ?_
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (kernel_nonneg _ _ _ _),
    ENNReal.toReal_ofReal (kernel_nonneg _ _ _ _)]

theorem summable_kernel_mul (Q : Set (Fin d → ℤ)) (r₁ r₂ : ℝ≥0) (x z : Fin d → ℤ) :
    Summable fun w => kernel Q r₁ x w * kernel Q r₂ w z := by
  have h := ofReal_kernel_add Q r₁ r₂ x z
  have hne : ∑' w, ENNReal.ofReal (kernel Q r₁ x w) * ENNReal.ofReal (kernel Q r₂ w z) ≠ ⊤ := by
    rw [← h]; exact ENNReal.ofReal_ne_top
  have := ENNReal.summable_toReal hne
  refine this.congr fun w => ?_
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (kernel_nonneg _ _ _ _),
    ENNReal.toReal_ofReal (kernel_nonneg _ _ _ _)]

/-- Chapman--Kolmogorov: the left side is at least any single term. -/
theorem kernel_add_ge (Q : Set (Fin d → ℤ)) (r₁ r₂ : ℝ≥0) (x z w : Fin d → ℤ) :
    kernel Q r₁ x w * kernel Q r₂ w z ≤ kernel Q (r₁ + r₂) x z := by
  rw [kernel_add]
  exact (summable_kernel_mul Q r₁ r₂ x z).le_tsum w (fun j _ =>
    mul_nonneg (kernel_nonneg _ _ _ _) (kernel_nonneg _ _ _ _))

end SRW
end ElboimSly
