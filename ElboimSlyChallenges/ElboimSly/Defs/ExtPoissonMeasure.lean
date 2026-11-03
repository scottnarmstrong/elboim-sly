/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import Mathlib.Probability.Distributions.Poisson.Basic
public import Mathlib.MeasureTheory.Measure.GiryMonad

/-!
# ExtPoissonMeasure

Extended Poisson law.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace ElboimSly

/-- The extended Poisson law on `[0, ∞]`. Extended Poisson law.
For `a < ∞` it is the image of `poissonMeasure a` under `ℕ → [0, ∞]`; for `a = ∞` it is `δ_∞`.
(The case split is the definition in the source, not a fallback.) -/
@[expose] noncomputable def extPoissonMeasure (a : ℝ≥0∞) : Measure ℝ≥0∞ :=
  if a = ∞ then Measure.dirac ∞
  else (poissonMeasure a.toNNReal).map (Nat.cast : ℕ → ℝ≥0∞)

end ElboimSly

end
