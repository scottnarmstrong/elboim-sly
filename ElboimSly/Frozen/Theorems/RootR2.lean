/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Provider.RootR2
public import ElboimSly.Frozen.Defs.InfEvent
public import ElboimSly.Frozen.Defs.IsPoissonPointProcess
public import ElboimSly.Frozen.Defs.RingIntensity
import Mathlib

/-!
# Root R2

R2: Theorem 1.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace ElboimSly

universe u

-- FROZEN_ANCHOR_PREFIX_BEGIN
/-- R2 (ES22 Theorem 1): almost surely the interchange permutation `π_β` has an infinite cycle.
R2: Theorem 1. For `d ≥ 5` there is `β₀ > 0` such that for every `β ≥ β₀` and every
Poisson point process `N` of intensity `ringIntensity d β` on a probability space `(Ω, P)`,
`N ∈ Inf` holds `P`-almost surely. -/
theorem root_R2 (d : ℕ) (hd : 5 ≤ d) :
    ∃ β₀ : ℝ, 0 < β₀ ∧ ∀ β : ℝ, β₀ ≤ β → ∀ [Fact (0 < β)],
      ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (N : Ω → Measure (RingSpace d β)),
        IsPoissonPointProcess N (ringIntensity d β) P →
          ∀ᵐ ω ∂P, N ω ∈ infEvent d β :=
-- FROZEN_ANCHOR_PROOF_BEGIN
  by exact ElboimSly.Provider.rootR2
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end ElboimSly

end
-- FROZEN_ANCHOR_SUFFIX_END
