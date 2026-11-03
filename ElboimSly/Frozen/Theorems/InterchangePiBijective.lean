/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Provider.InterchangePiBijective
import Mathlib

/-!
# Bijectivity of `π_s`

pi_s is a permutation.
-/

public section

open MeasureTheory
open scoped NNReal

namespace ElboimSly

variable {d : ℕ} {β : ℝ} [Fact (0 < β)]

-- FROZEN_ANCHOR_PREFIX_BEGIN
/-- For good `ν` and `s ≥ 0`, `π_s` is a bijection of `ℤᵈ`. pi_s is a permutation
(the formula for the inverse, `y ↦ η_{y,s}(0)`, is not part of this statement). -/
theorem interchangePi_bijective (ν : Measure (RingSpace d β)) (hν : Good ν) (s : ℝ≥0) :
    Function.Bijective (interchangePi ν s) :=
-- FROZEN_ANCHOR_PROOF_BEGIN
  by exact ElboimSly.Provider.interchangePiBijective
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end ElboimSly

end
-- FROZEN_ANCHOR_SUFFIX_END
