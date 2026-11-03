/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.StrongApprox.BasePPP
public import ElboimSly.Foundations.SRW.Increments
public import Mathlib

/-!
# The walk of the base coupling at integer times

ES22 (8.3): base coupling with precision n^10, `eq:sa-walk-int` and `eq:sa-int-diff`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ElboimSly
namespace StrongApprox

open SRW

/-- If all points of the block `k` lie in its cell, `N'(S_k) = K_k`. -/
theorem cellProc_apply_cell {S 𝒦 Ω' : Type*} [MeasurableSpace S] (Q : 𝒦 → Set S)
    (hQm : ∀ k, MeasurableSet (Q k)) (hQd : Pairwise (Function.onFun Disjoint Q))
    (K : 𝒦 → Ω' → ℕ) (Y : 𝒦 → ℕ → Ω' → S) (ω : Ω') (k : 𝒦)
    (hY : ∀ i, Y k i ω ∈ Q k) : cellProc Q K Y ω (Q k) = (K k ω : ℝ≥0∞) := by
  unfold cellProc
  rw [Measure.sum_apply _ (hQm k), tsum_eq_single k]
  · rw [Measure.restrict_apply (hQm k), Set.inter_self, blockProc, mixedBinomial_apply _ _ _ (hQm k)]
    unfold mbCount
    have : ∀ i ∈ Finset.range (K k ω), (Q k).indicator (fun _ => (1 : ℝ)) (Y k i ω) = 1 :=
      fun i _ => Set.indicator_of_mem (hY i) _
    rw [Finset.sum_congr rfl this]
    simp
  · intro k' hk'
    rw [Measure.restrict_apply (hQm k), (hQd hk'.symm).inter_eq]
    simp

end StrongApprox
end ElboimSly
