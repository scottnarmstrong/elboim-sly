/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.SRW.KernelSym
public import ElboimSly.Foundations.SRW.Coords
public import Mathlib

/-!
# Confined kernels: product structure

Properties of confined kernels (a).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal

namespace ElboimSly
namespace SRW

/-- The one-dimensional confined kernel on an interval (or any set) `J ⊆ ℤ`. -/
noncomputable def kernel1 (J : Set ℤ) (r : ℝ≥0) (a b : ℤ) : ℝ :=
  kernel (d := 1) {v | v 0 ∈ J} r (fun _ => a) (fun _ => b)

/-- Properties of confined kernels (a): product structure. -/
theorem kernel_pi {d : ℕ} (J : Fin d → Set ℤ) (r : ℝ≥0) (x z : Fin d → ℤ) :
    kernel {v : Fin d → ℤ | ∀ i, v i ∈ J i} r x z = ∏ i, kernel1 (J i) r (x i) (z i) := by
  obtain ⟨Ω, mΩ, P, N, hP, hN, -⟩ := exists_isPoissonPointProcess_clockIntensity (Dir d)
  have hZ := canonical_isSRW hN
  have hind := (iIndepFun_coordinates hN).comp
    (fun (_ : Fin d) (β : ℝ≥0 → ℤ) => (fun s _ => β s : PathSpace 1))
    (fun _ => measurable_pi_iff.2 fun s => measurable_pi_iff.2 fun _ => measurable_pi_apply s)
  choose V hVm hV using fun i => isRegSet_kerSet (d := 1) {v | v 0 ∈ J i} r (fun _ => x i)
    (fun _ => z i)
  have hY : ∀ i, IsSRW P (fun ω s => fun _ : Fin 1 => walk d (N ω) (s : ℝ) i) :=
    fun i => isSRW_coordinate hN i
  have hset : {ω | canonical d N ω ∈ kerSet {v : Fin d → ℤ | ∀ i, v i ∈ J i} r x z} =
      ⋂ i ∈ (Finset.univ : Finset (Fin d)),
        ((fun i (ω : Ω) => (fun s _ => walk d (N ω) (s : ℝ) i : PathSpace 1)) i) ⁻¹' V i := by
    ext ω
    simp only [mem_ofPred_eq, mem_iInter, Finset.mem_univ, forall_true_left, mem_preimage]
    have key : ∀ i, (fun s (_ : Fin 1) => walk d (N ω) (s : ℝ) i : PathSpace 1) ∈
        V i ↔ (x i + walk d (N ω) (r : ℝ) i = z i ∧
          ∀ s : ℝ≥0, s ≤ r → x i + walk d (N ω) (s : ℝ) i ∈ J i) := by
      intro i
      rw [← hV i _ ((hY i).2.1 ω)]
      simp only [kerSet, mem_ofPred_eq]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨congrFun h1 0, fun s hs => h2 s hs⟩
      · rintro ⟨h1, h2⟩; exact ⟨funext fun _ => h1, fun s hs => h2 s hs⟩
    simp only [key, kerSet, mem_ofPred_eq, canonical]
    constructor
    · rintro ⟨h1, h2⟩ i
      exact ⟨congrFun h1 i, fun s hs => h2 s hs i⟩
    · intro h
      exact ⟨funext fun i => (h i).1, fun s hs i => (h i).2 s hs⟩
  have h1 : ENNReal.ofReal (kernel {v : Fin d → ℤ | ∀ i, v i ∈ J i} r x z) =
      ∏ i, ENNReal.ofReal (kernel1 (J i) r (x i) (z i)) := by
    rw [← hZ.prob_kerSet, hset]
    refine (hind.measure_inter_preimage_eq_mul Finset.univ (fun i _ => hVm i)).trans ?_
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [kernel1, ← (hY i).prob_kerSet]
    congr 1
    ext ω
    exact (hV i _ ((hY i).2.1 ω)).symm
  have h2 := congrArg ENNReal.toReal h1
  rw [ENNReal.toReal_ofReal (kernel_nonneg _ _ _ _), ENNReal.toReal_prod] at h2
  rw [h2]
  exact Finset.prod_congr rfl fun i _ => ENNReal.toReal_ofReal (kernel_nonneg _ _ _ _)

end SRW
end ElboimSly
