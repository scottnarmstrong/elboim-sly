/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.SRW.KernelBasic
public import ElboimSly.Foundations.SRW.ReversalMain
public import ElboimSly.Foundations.SRW.Increments
public import Mathlib

/-!
# Confined kernels: symmetry

Properties of confined kernels (c), by time reversal.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal

namespace ElboimSly
namespace SRW

variable {d : ℕ}

theorem IsRegularPath.neg {γ : PathSpace d} (h : IsRegularPath γ) :
    IsRegularPath fun s => -γ s := by
  intro t
  obtain ⟨δ, hδ, hc⟩ := h t
  exact ⟨δ, hδ, fun s hs1 hs2 => by simp only [hc s hs1 hs2]⟩

/-- For the canonical walk of a Poisson process: the kernel event for `(x,z)` agrees a.s. with
the kernel event for `(z,x)` of the negated time reversal. -/
theorem ae_kerSet_rev {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {N : Ω → Measure (Dir d × ℝ)}
    (hN : IsPoissonPointProcess N (clockIntensity (Dir d)) P) (Q : Set (Fin d → ℤ)) {r : ℝ≥0}
    (hr : 0 < r) (x z : Fin d → ℤ) :
    ∀ᵐ ω ∂P, (canonical d N ω ∈ kerSet Q r x z ↔
      (fun u => -revPath r (canonical d N ω) u) ∈ kerSet Q r z x) := by
  filter_upwards [ae_range_revPath_canonical hN hr] with ω hω
  set X := canonical d N ω with hX
  have hrev : revPath r X r = X r := by simp [revPath]
  simp only [kerSet, mem_ofPred_eq, hrev]
  have e1 : (z + -X r = x) ↔ (x + X r = z) := by
    constructor <;> intro h <;> [rw [← h]; rw [← h]] <;> abel
  constructor
  · rintro ⟨hA, hB⟩
    refine ⟨e1.2 hA, fun u hu => ?_⟩
    have hm : X r - revPath r X u ∈ X '' Icc 0 r := by
      rw [hω]; exact ⟨u, ⟨bot_le, hu⟩, rfl⟩
    obtain ⟨s, ⟨-, hs⟩, hse⟩ := hm
    have := hB s hs
    rw [hse] at this
    rw [← hA]
    convert this using 1; abel
  · rintro ⟨hA, hB⟩
    have hA' := e1.1 hA
    refine ⟨hA', fun s hs => ?_⟩
    have hm : X s ∈ (fun u => X r - revPath r X u) '' Icc 0 r := by
      rw [← hω]; exact ⟨s, ⟨bot_le, hs⟩, rfl⟩
    obtain ⟨u, ⟨-, hu⟩, hue⟩ := hm
    have := hB u hu
    rw [← hue]
    rw [← hA'] at this
    convert this using 1; abel

theorem measurable_negPath : Measurable fun γ : PathSpace d => fun u => -γ u :=
  measurable_pi_iff.2 fun u => (measurable_pi_apply u).neg

/-- Properties of confined kernels (c): symmetry. -/
theorem kernel_symm (Q : Set (Fin d → ℤ)) (r : ℝ≥0) (x z : Fin d → ℤ) :
    kernel Q r x z = kernel Q r z x := by
  obtain ⟨Ω, mΩ, P, N, hP, hN, -⟩ := exists_isPoissonPointProcess_clockIntensity (Dir d)
  have hZ := canonical_isSRW hN
  suffices h : P {ω | canonical d N ω ∈ kerSet Q r x z} =
      P {ω | canonical d N ω ∈ kerSet Q r z x} by
    rw [hZ.prob_kerSet, hZ.prob_kerSet] at h
    exact (ENNReal.ofReal_eq_ofReal_iff (kernel_nonneg _ _ _ _) (kernel_nonneg _ _ _ _)).1 h
  rcases eq_zero_or_pos (a := r) with h0 | hr
  · subst h0
    congr 1
    ext ω
    have h00 : canonical d N ω 0 = 0 := by simp [canonical, walk_zero]
    simp only [kerSet, mem_ofPred_eq, h00, add_zero]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h1.symm, fun s hs => ?_⟩
      have := h2 0 le_rfl
      rw [le_zero_iff.1 hs, h00, add_zero, ← h1]
      rwa [h00, add_zero] at this
    · rintro ⟨h1, h2⟩
      refine ⟨h1.symm, fun s hs => ?_⟩
      have := h2 0 le_rfl
      rw [le_zero_iff.1 hs, h00, add_zero, ← h1]
      rwa [h00, add_zero] at this
  · obtain ⟨V, hVm, hV⟩ := isRegSet_kerSet Q r z x
    have hae := ae_kerSet_rev hN Q hr x z
    obtain ⟨hmeas, -, hneg⟩ := reversal_law hN r
    have hg : AEMeasurable (fun ω u => -stopPath r (revPath r (canonical d N ω)) u) P :=
      measurable_negPath.comp_aemeasurable hmeas
    calc P {ω | canonical d N ω ∈ kerSet Q r x z}
        = P {ω | (fun u => -revPath r (canonical d N ω) u) ∈ kerSet Q r z x} :=
          measure_congr (hae.mono fun ω h => propext h)
      _ = P ((fun ω u => -stopPath r (revPath r (canonical d N ω)) u) ⁻¹' V) := by
          congr 1
          ext ω
          have hreg : IsRegularPath fun u => -revPath r (canonical d N ω) u :=
            (isRegularPath_revPath_canonical N r ω).neg
          exact kerSet_stop_iff hreg hV
      _ = P.map (fun ω u => -stopPath r (revPath r (canonical d N ω)) u) V :=
          (Measure.map_apply_of_aemeasurable hg hVm).symm
      _ = P.map (fun ω => stopPath r (canonical d N ω)) V := by rw [hneg]
      _ = P {ω | canonical d N ω ∈ kerSet Q r z x} := by
          rw [Measure.map_apply (f := fun ω => stopPath r (canonical d N ω))
            ((measurable_stopPath r).comp hZ.1) hVm]
          congr 1
          ext ω
          exact (kerSet_stop_iff (isRegularPath_canonical N ω) hV).symm

end SRW
end ElboimSly
