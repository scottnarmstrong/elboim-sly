/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Escape.Es52Refl5
public import ElboimSly.Paper.Escape.Es52StopT
public import Mathlib

/-!
# ES22 Proposition 5.2, Step 2: `π_{B̃}(h_*N) ≤ π_B(N)`

ES22 Proposition 5.2 Step 2, "`π_{B̃}(h_*N) = π_B(N)` (`Φ` is computed with the `h_*`-invariant
`Π_μ`)".  Only the inequality `≤` (all that is needed) is proved: the region of
`ρ^{reg}(h_*N)` at `T_B` is the preimage under `Ψ` of that of `ρ^{reg}(N)`, the ring measures are
`N|_R`, so the resampled environment is the `h_*`-image, and `Y_{B̃}(h_*ν) = Y_B(ν)`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Escape

open ElboimSly ElboimSly.Cyclic ElboimSly.Interchange ElboimSly.Paper

variable {k : ℕ} {β : ℝ} [Fact (0 < β)] {n₀ n : ℕ} {t₀ : ℝ} {Ω : Type}
  {𝒢₀ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {Pr : Measure Ω}
  {N N' : Ω → Measure (CycS ℕ (k + 2) β)}

theorem envMap_eq_map (ν : Measure (ℕ × RingSpace (k + 2) β)) :
    envMap (reflAut k) ν = ν.map (psiE k β) := rfl

theorem envMap_restrict (ν : Measure (ℕ × RingSpace (k + 2) β)) (R : Set (ℕ × RingSpace (k + 2) β)) :
    envMap (reflAut k) (ν.restrict R) = (envMap (reflAut k) ν).restrict (psiE k β ⁻¹' R) := by
  rw [envMap_eq_map, envMap_eq_map, MeasurableEquiv.restrict_map]
  congr 2
  ext x
  simp [psiE_invol]

omit [Fact (0 < β)] in
theorem envMap_add (ν₁ ν₂ : Measure (ℕ × RingSpace (k + 2) β)) :
    envMap (reflAut k) (ν₁ + ν₂) = envMap (reflAut k) ν₁ + envMap (reflAut k) ν₂ :=
  Measure.map_add _ _ (measurable_envMapFn _)

/-- The integrals compare: the `Ψ`-pushed integrand is the `Ψ`-image of the original. -/
theorem key_integral (n : ℕ) (tn : ℝ) (u : Fin (k + 2) → ℤ) (ν₀ : Measure (ℕ × RingSpace (k + 2) β))
    (R : Set (ℕ × RingSpace (k + 2) β)) (Λ : Measure (Measure (ℕ × RingSpace (k + 2) β))) :
    ∫⁻ ν', escYg n tn (reflU (escJ n) u) ((envMap (reflAut k) ν₀).restrict (psiE k β ⁻¹' R) +
        ν'.restrict (psiE k β ⁻¹' R)ᶜ) ∂(Λ.map (envMap (reflAut k))) ≤
      ∫⁻ ν, escYg n tn u (ν₀.restrict R + ν.restrict Rᶜ) ∂Λ := by
  refine (lintegral_map_le _ measurable_envMap_refl.aemeasurable).trans (le_of_eq ?_)
  refine lintegral_congr fun ν => ?_
  rw [← escYg_envMap (n := n) (tn := tn) (u := u), envMap_add, envMap_restrict, envMap_restrict,
    Set.preimage_compl]

end ElboimSly.Paper.Escape
