/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.SRW.KernelProd
public import Mathlib

/-!
# One-dimensional confined kernels

Properties of confined kernels in `d = 1`, in terms of `kernel1`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal

namespace ElboimSly
namespace SRW

theorem kernel1_nonneg (J : Set ℤ) (r : ℝ≥0) (a b : ℤ) : 0 ≤ kernel1 J r a b :=
  kernel_nonneg _ _ _ _

theorem kernel1_mono {J J' : Set ℤ} (h : J ⊆ J') (r : ℝ≥0) (a b : ℤ) :
    kernel1 J r a b ≤ kernel1 J' r a b :=
  kernel_mono (fun _ hv => h hv) r _ _

theorem kernel1_symm (J : Set ℤ) (r : ℝ≥0) (a b : ℤ) : kernel1 J r a b = kernel1 J r b a :=
  kernel_symm _ r _ _

theorem tsum_fin1 (f : (Fin 1 → ℤ) → ℝ) : ∑' z, f z = ∑' b : ℤ, f (fun _ => b) :=
  ((Equiv.funUnique (Fin 1) ℤ).symm.tsum_eq f).symm

theorem summable_fin1 {f : (Fin 1 → ℤ) → ℝ} (h : Summable f) :
    Summable fun b : ℤ => f (fun _ => b) :=
  (Equiv.funUnique (Fin 1) ℤ).symm.summable_iff.2 h

theorem summable_kernel1 (J : Set ℤ) (r : ℝ≥0) (a : ℤ) : Summable fun b => kernel1 J r a b :=
  summable_fin1 (f := fun z => kernel {v : Fin 1 → ℤ | v 0 ∈ J} r (fun _ => a) z)
    (summable_kernel _ r _)

/-- Mass of the one-dimensional kernel. -/
theorem kernel1_tsum (J : Set ℤ) (r : ℝ≥0) (a : ℤ) :
    ∑' b, kernel1 J r a b =
      ((srwP 1) {ω | ∀ s : ℝ≥0, s ≤ r → a + srwZ 1 ω s 0 ∈ J}).toReal := by
  have := kernel_tsum {v : Fin 1 → ℤ | v 0 ∈ J} r (fun _ => a)
  rw [tsum_fin1] at this
  unfold kernel1
  exact this

theorem kernel1_add (J : Set ℤ) (r₁ r₂ : ℝ≥0) (a c : ℤ) :
    kernel1 J (r₁ + r₂) a c = ∑' b, kernel1 J r₁ a b * kernel1 J r₂ b c := by
  have := kernel_add {v : Fin 1 → ℤ | v 0 ∈ J} r₁ r₂ (fun _ => a) (fun _ => c)
  rw [tsum_fin1] at this
  exact this

theorem summable_kernel1_mul (J : Set ℤ) (r₁ r₂ : ℝ≥0) (a c : ℤ) :
    Summable fun b => kernel1 J r₁ a b * kernel1 J r₂ b c :=
  summable_fin1 (f := fun w => kernel {v : Fin 1 → ℤ | v 0 ∈ J} r₁ (fun _ => a) w *
    kernel {v : Fin 1 → ℤ | v 0 ∈ J} r₂ w (fun _ => c)) (summable_kernel_mul _ r₁ r₂ _ _)

theorem kernel1_add_ge (J : Set ℤ) (r₁ r₂ : ℝ≥0) (a c b : ℤ) :
    kernel1 J r₁ a b * kernel1 J r₂ b c ≤ kernel1 J (r₁ + r₂) a c :=
  kernel_add_ge _ r₁ r₂ _ _ _

theorem kernel1_translate (J : Set ℤ) (y : ℤ) (r : ℝ≥0) (a b : ℤ) :
    kernel1 ((fun q => q + y) '' J) r (a + y) (b + y) = kernel1 J r a b := by
  have := kernel_translate {v : Fin 1 → ℤ | v 0 ∈ J} (fun _ => y) r (fun _ => a) (fun _ => b)
  unfold kernel1
  have e : {v : Fin 1 → ℤ | v 0 ∈ (fun q => q + y) '' J} =
      (fun q => q + fun _ => y) '' {v : Fin 1 → ℤ | v 0 ∈ J} := by
    ext v
    simp only [mem_ofPred_eq, mem_image]
    constructor
    · rintro ⟨q, hq, hv⟩
      exact ⟨fun _ => q, hq, funext fun i => by
        rw [Subsingleton.elim i 0]; exact hv⟩
    · rintro ⟨q, hq, rfl⟩
      exact ⟨q 0, hq, rfl⟩
  rw [e]
  exact this

end SRW
end ElboimSly
