/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Interchange.SymmDef
import Mathlib

/-!
# Symmetries preserve (G1) and (G2)

Symmetries preserve good configurations (first paragraph of the proof).

Conditions (G1), (G2) and the counting-measure property are statements about masses of single
points and of the sets `{e} × 𝕋`; they are preserved by every `(e, θ) ↦ (σ e, τ θ)`.
(G3) is treated separately for each symmetry.
-/

@[expose] public section

open MeasureTheory

namespace ElboimSly.Interchange

variable {d : ℕ} {β : ℝ} [Fact (0 < β)] {ν : Measure (RingSpace d β)}

/-- The condition (G3) of `Good`, stated for a configuration. -/
def GoodG3 (ν : Measure (RingSpace d β)) : Prop :=
  ∀ (y : Fin d → ℤ) (j : ℤ), ∃ n : ℕ,
    (¬ ∃ (v : Fin (n + 1) → (Fin d → ℤ)) (t : Fin n → ℝ),
        v 0 = y ∧ IsRingPath ν (ringWindow β j) n v t) ∧
    (¬ ∃ (v : Fin (n + 1) → (Fin d → ℤ)) (t : Fin n → ℝ),
        v (Fin.last n) = y ∧ IsRingPath ν (ringWindow β j) n v t)

omit [Fact (0 < β)] in
theorem isRingConfig_ringPush (σ : Edge d ≃ Edge d) (τ : AddCircle β ≃ᵐ AddCircle β)
    (h : IsRingConfig ν) : IsRingConfig (ringPush σ τ ν) := fun A hA => by
  rw [ringPush_apply]
  exact h _ ((ringMapEquiv σ τ).measurable hA)

omit [Fact (0 < β)] in
/-- (G1), (G2) and the counting-measure property are preserved. -/
theorem good_ringPush_of_g3 (σ : Edge d ≃ Edge d) (τ : AddCircle β ≃ᵐ AddCircle β)
    (hν : Good ν) (h3 : GoodG3 (ringPush σ τ ν)) : Good (ringPush σ τ ν) := by
  obtain ⟨h0, h1, ⟨h2a, h2b⟩, -⟩ := hν
  refine ⟨isRingConfig_ringPush σ τ h0, fun e => ?_, ⟨fun e θ => ?_, fun e f hef => ?_⟩, h3⟩
  · rw [ringPush_edge_univ]; exact h1 _
  · rw [ringPush_singleton]; exact h2a _ _
  · rw [Set.disjoint_left]
    intro θ hθ hθ'
    rw [mem_ringSet_ringPush] at hθ hθ'
    exact Set.disjoint_left.mp (h2b _ _ (fun h => hef (σ.symm.injective h))) hθ hθ'

end ElboimSly.Interchange
