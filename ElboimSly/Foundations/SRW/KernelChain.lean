/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.SRW.MarkovChain
public import ElboimSly.Foundations.SRW.KernelBasic
public import ElboimSly.Foundations.SRW.EscapeParams
public import Mathlib

/-!
# A chain of confined kernel events in consecutive windows

If window `k` (of length `ρ k`) asks to go from `x k` to `z k` inside `Q k`, the events are
independent and have probabilities `kernel (Q k) (ρ k) (x k) (z k)`.  Used for Claim 5.6 (`𝓑_0`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Real

namespace ElboimSly
namespace SRW

variable {d : ℕ}

/-- The generic pathwise extraction for `Gfrom`. -/
theorem mem_Gfrom_regular_gen {ρ : ℕ → ℝ≥0} {S Γ : ℕ → Set (PathSpace d)}
    (hSΓ : ∀ k (β : PathSpace d), IsRegularPath β → (stopPath (ρ k) β ∈ S k ↔ β ∈ Γ k)) :
    ∀ (m k : ℕ) {γ : PathSpace d}, IsRegularPath γ → γ ∈ Gfrom ρ S k (m + 1) →
      γ ∈ Γ k ∧ ∀ i < m, SRW.theta (∑ j ∈ Finset.range (i + 1), ρ (k + j)) γ ∈ Γ (k + i + 1)
  | 0, k, γ, hγ, h => by
    refine ⟨?_, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
    exact (hSΓ k γ hγ).1 h.1
  | m + 1, k, γ, hγ, h => by
    obtain ⟨h1, h2⟩ := h
    have hβ : IsRegularPath (SRW.theta (ρ k) γ) := hγ.theta _
    obtain ⟨ih1, ih2⟩ := mem_Gfrom_regular_gen hSΓ m (k + 1) hβ h2
    refine ⟨(hSΓ k γ hγ).1 h1, fun i hi => ?_⟩
    rcases i with _ | i
    · simpa using ih1
    · have := ih2 i (by omega)
      rw [theta_theta] at this
      have e : ρ k + ∑ j ∈ Finset.range (i + 1), ρ (k + 1 + j) =
          ∑ j ∈ Finset.range (i + 1 + 1), ρ (k + j) := by
        rw [Finset.sum_range_succ' (fun j => ρ (k + j)) (i + 1)]
        rw [add_comm]
        simp only [add_zero]
        refine congrArg (· + ρ k) (Finset.sum_congr rfl fun j _ => ?_)
        rw [show k + 1 + j = k + (j + 1) by omega]
      rw [e] at this
      rw [show k + (i + 1) + 1 = k + 1 + i + 1 by omega]
      exact this

/-- Chosen measurable versions of the kernel events. -/
noncomputable def kerV (Q : ℕ → Set (Fin d → ℤ)) (ρ : ℕ → ℝ≥0) (x z : ℕ → Fin d → ℤ) (k : ℕ) :
    Set (PathSpace d) := (isRegSet_kerSet (Q k) (ρ k) (x k) (z k)).choose

theorem measurableSet_kerV (Q : ℕ → Set (Fin d → ℤ)) (ρ : ℕ → ℝ≥0) (x z : ℕ → Fin d → ℤ) (k : ℕ) :
    MeasurableSet (kerV Q ρ x z k) := (isRegSet_kerSet (Q k) (ρ k) (x k) (z k)).choose_spec.1

theorem kerV_stop (Q : ℕ → Set (Fin d → ℤ)) (ρ : ℕ → ℝ≥0) (x z : ℕ → Fin d → ℤ) (k : ℕ)
    {β : PathSpace d} (hβ : IsRegularPath β) :
    stopPath (ρ k) β ∈ kerV Q ρ x z k ↔ β ∈ kerSet (Q k) (ρ k) (x k) (z k) := by
  exact (kerSet_stop_iff hβ (isRegSet_kerSet (Q k) (ρ k) (x k) (z k)).choose_spec.2).symm

theorem IsSRW.real_chain {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {Y : Ω → PathSpace d}
    (hY : IsSRW P Y) (Q : ℕ → Set (Fin d → ℤ)) (ρ : ℕ → ℝ≥0) (x z : ℕ → Fin d → ℤ) (n : ℕ)
    (c : ℕ → ℝ) (hc0 : ∀ k, 0 ≤ c k) (hc : ∀ k, c k ≤ kernel (Q k) (ρ k) (x k) (z k)) :
    ∏ k ∈ Finset.range n, c k ≤ P.real {ω | Y ω ∈ Gfrom ρ (kerV Q ρ x z) 0 n} := by
  have := hY.isProbabilityMeasure
  rw [hY.real_Gfrom (measurableSet_kerV Q ρ x z) n 0]
  refine Finset.prod_le_prod₀ (fun k _ => hc0 k) (fun k _ => ?_)
  refine (hc k).trans (le_of_eq ?_)
  simp only [zero_add]
  have e : {ω | stopPath (ρ k) (Y ω) ∈ kerV Q ρ x z k} =
      {ω | Y ω ∈ kerSet (Q k) (ρ k) (x k) (z k)} := by
    ext ω; exact kerV_stop Q ρ x z k (hY.2.1 ω)
  rw [e, measureReal_def, hY.prob_kerSet, ENNReal.toReal_ofReal (kernel_nonneg _ _ _ _)]

end SRW
end ElboimSly
