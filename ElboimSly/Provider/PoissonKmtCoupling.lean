/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.StrongApprox.PoissonKMT
public import Mathlib.Probability.Distributions.Poisson.Basic
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Provider for `PoissonKmtCoupling`

Proof of the main theorem `ElboimSly.Frozen.Theorems.PoissonKmtCoupling` (A1: KMT coupling for Poisson increments). The proof is the dyadic coupling of `ElboimSly/Foundations/StrongApprox/`
(`DyadicTree`, `TreeLaw`, `TreeSplit`, `TreeError`, `PathMoment`, `Dyadic`, `PoissonKMT`).
-/

public section

open MeasureTheory ProbabilityTheory

namespace ElboimSly.Provider

/-- A1: KMT coupling for Poisson increments. A1: KMT coupling for Poisson increments. -/
theorem poissonKmtCoupling :
    ∃ C K lam : ℝ, 0 < C ∧ 0 < K ∧ 0 < lam ∧ ∀ N : ℕ,
      ∃ Q : Measure ((Fin N → ℝ) × (Fin N → ℝ)), IsProbabilityMeasure Q ∧
        Q.map Prod.fst = Measure.pi (fun _ : Fin N => (poissonMeasure 1).map (Nat.cast : ℕ → ℝ)) ∧
        Q.map Prod.snd = Measure.pi (fun _ : Fin N => gaussianReal 0 1) ∧
        ∀ x : ℝ, 0 ≤ x →
          Q.real {p | ∃ j : Fin N,
              C * Real.log N + x ≤ |∑ i ∈ Finset.univ.filter (· ≤ j), (p.1 i - 1 - p.2 i)|}
            ≤ K * Real.exp (-lam * x) :=
  ElboimSly.StrongApprox.poisson_kmt_coupling_aux

end ElboimSly.Provider

end
