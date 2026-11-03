/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Interchange.PiBij
import Mathlib

/-!
# Provider for `InterchangePiBijective`

Proof of the main theorem `ElboimSly.Frozen.Theorems.InterchangePiBijective` (pi_s is a permutation). The proof is `ElboimSly.Interchange.interchangePi_bijective`.
-/

public section

open MeasureTheory
open scoped NNReal

namespace ElboimSly.Provider

/-- For good `ν` and `s ≥ 0`, `π_s` is a bijection of `ℤᵈ`. pi_s is a permutation. -/
theorem interchangePiBijective {d : ℕ} {β : ℝ} [Fact (0 < β)] {ν : Measure (RingSpace d β)}
    (hν : Good ν := by assumption) {s : ℝ≥0} :
    Function.Bijective (interchangePi ν s) :=
  ElboimSly.Interchange.interchangePi_bijective hν s

end ElboimSly.Provider

end
