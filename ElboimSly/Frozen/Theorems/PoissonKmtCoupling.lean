/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Provider.PoissonKmtCoupling
public import Mathlib.Probability.Distributions.Poisson.Basic
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# PoissonKmtCoupling

A1: KMT coupling for Poisson increments.
-/

public section

open MeasureTheory ProbabilityTheory

namespace ElboimSly

-- FROZEN_ANCHOR_PREFIX_BEGIN
/-- A1: KMT coupling for Poisson increments. A1: KMT coupling for Poisson increments.
`Q` is a probability measure on `ℝᴺ × ℝᴺ` with marginals `Poisson(1)^{⊗N}` and `𝒩(0,1)^{⊗N}`;
the maximum over `j ≤ N` is written as an existential over `j : Fin N` (indices are `i ≤ j`). -/
theorem poisson_kmt_coupling :
    ∃ C K lam : ℝ, 0 < C ∧ 0 < K ∧ 0 < lam ∧ ∀ N : ℕ,
      ∃ Q : Measure ((Fin N → ℝ) × (Fin N → ℝ)), IsProbabilityMeasure Q ∧
        Q.map Prod.fst = Measure.pi (fun _ : Fin N => (poissonMeasure 1).map (Nat.cast : ℕ → ℝ)) ∧
        Q.map Prod.snd = Measure.pi (fun _ : Fin N => gaussianReal 0 1) ∧
        ∀ x : ℝ, 0 ≤ x →
          Q.real {p | ∃ j : Fin N,
              C * Real.log N + x ≤ |∑ i ∈ Finset.univ.filter (· ≤ j), (p.1 i - 1 - p.2 i)|}
            ≤ K * Real.exp (-lam * x) :=
-- FROZEN_ANCHOR_PROOF_BEGIN
  by exact ElboimSly.Provider.poissonKmtCoupling
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end ElboimSly

end
-- FROZEN_ANCHOR_SUFFIX_END
