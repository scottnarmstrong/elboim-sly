/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import Mathlib.Probability.BrownianMotion.Basic
public import Mathlib.Probability.Independence.Basic

/-!
# Standard `d`-dimensional Brownian motion

Standard d-dimensional Brownian motion.

A standard `d`-dimensional Brownian motion on a probability space `(Ω, P)` is a map
`B : ℝ≥0 → Ω → (Fin d → ℝ)` such that (BM0) each `B t` is measurable, (BM1) every path is
continuous and starts at `0`, (BM2) each coordinate process is pre-Brownian
(Mathlib's `IsPreBrownianReal`), and (BM3) the coordinate processes are mutually independent,
as random elements of `ℝ≥0 → ℝ` with the product `σ`-algebra.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace ElboimSly

/-- Standard d-dimensional Brownian motion. `B` is a standard `d`-dimensional Brownian motion under `P`.

* `measurable` is (BM0);
* `continuous_zero` is (BM1);
* `isPreBrownianReal` is (BM2);
* `iIndepFun` is (BM3). -/
structure IsStandardBrownianMotion {Ω : Type*} [MeasurableSpace Ω] (d : ℕ)
    (B : ℝ≥0 → Ω → (Fin d → ℝ)) (P : Measure Ω) : Prop where
  /-- (BM0): each `B t` is measurable. -/
  measurable : ∀ t, Measurable (B t)
  /-- (BM1): every path is continuous and `B 0 = 0`. -/
  continuous_zero : ∀ ω, Continuous (fun t => B t ω) ∧ B 0 ω = 0
  /-- (BM2): each coordinate process is pre-Brownian. -/
  isPreBrownianReal : ∀ i, IsPreBrownianReal (fun t ω => B t ω i) P
  /-- (BM3): the coordinate processes are mutually independent. -/
  iIndepFun : iIndepFun (fun i ω t => B t ω i) P

end ElboimSly
