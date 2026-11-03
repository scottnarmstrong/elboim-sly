/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Frozen.Defs.ExtPoissonMeasure
public import Mathlib.Probability.Distributions.Poisson.Basic
public import Mathlib.MeasureTheory.Measure.GiryMonad

/-!
# IsPoissonPointProcess

Poisson point process.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace ElboimSly

/-- `N` is a Poisson point process with intensity `μ` on the probability space `(Ω, P)`.
Poisson point process (with random measures for measurability in the Giry
`σ`-algebra `Measure.instMeasurableSpace`).
* `Measurable N`: `N` is a random measure.
* (PPP1) every count `N(A)` has the extended Poisson law of mean `μ A`
  (so `N A = ∞` almost surely when `μ A = ∞`).
* (PPP2) for pairwise disjoint measurable `A 0, …, A (n-1)` the joint law of the counts is the
  product of the extended Poisson laws (equivalently, the counts are independent).
Taking `n = 0` in (PPP2) forces `P` to be a probability measure. -/
@[expose] def IsPoissonPointProcess {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
    (N : Ω → Measure S) (μ : Measure S) (P : Measure Ω) : Prop :=
  Measurable N ∧
  (∀ A : Set S, MeasurableSet A → P.map (fun ω => N ω A) = extPoissonMeasure (μ A)) ∧
  (∀ (n : ℕ) (A : Fin n → Set S), (∀ j, MeasurableSet (A j)) →
    Pairwise (Function.onFun Disjoint A) →
    P.map (fun ω j => N ω (A j)) = Measure.pi (fun j => extPoissonMeasure (μ (A j))))

end ElboimSly

end
