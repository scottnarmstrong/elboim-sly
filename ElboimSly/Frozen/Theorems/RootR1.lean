/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Provider.RootR1
public import ElboimSly.Frozen.Defs.FinZeroEvent
public import ElboimSly.Frozen.Defs.IsPoissonPointProcess
public import ElboimSly.Frozen.Defs.RingIntensity
import Mathlib

/-!
# Root R1

R1: the origin is rarely in a finite cycle.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace ElboimSly

universe u

-- FROZEN_ANCHOR_PREFIX_BEGIN
/-- R1: the origin lies in a finite `π_β`-cycle with probability less than `2/β`. R1: the origin is rarely in a finite cycle. For `d ≥ 5` there is `β₀ > 0` such that for every `β ≥ β₀` and every Poisson point
process `N` of intensity `ringIntensity d β` on a probability space `(Ω, P)`,
`P(N ∈ Fin₀) < 2/β`. -/
theorem root_R1 (d : ℕ) (hd : 5 ≤ d) :
    ∃ β₀ : ℝ, 0 < β₀ ∧ ∀ β : ℝ, β₀ ≤ β → ∀ [Fact (0 < β)],
      ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (N : Ω → Measure (RingSpace d β)),
        IsPoissonPointProcess N (ringIntensity d β) P →
          P {ω | N ω ∈ finZeroEvent d β} < ENNReal.ofReal (2 / β) :=
-- FROZEN_ANCHOR_PROOF_BEGIN
  by exact ElboimSly.Provider.rootR1
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end ElboimSly

end
-- FROZEN_ANCHOR_SUFFIX_END
