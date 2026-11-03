/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Roots.RootR1OfIndMain
public import ElboimSly.Paper.Induction.MainOfClaimJ
public import ElboimSly.Paper.Step.Lemma78ClaimJ
import Mathlib

/-!
# Provider for `RootR1`

Proof of the main theorem `ElboimSly.Frozen.Theorems.RootR1` (R1: the origin is rarely in a finite cycle). The
proof is `ElboimSly.Roots.root_R1_of_indMain` (Theorem 3.2 ⇒ R1) applied to Theorem 3.2, which is
`ElboimSly.Paper.Induction.ind_main_of_claimJ` with Lemma 7.8's excursion claim. Providers do not
import one another (quarantine), so Theorem 3.2 is supplied here directly.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace ElboimSly.Provider

universe u

/-- R1: for `d ≥ 5` and `β` large, the probability that the cycle of the origin is finite is less
than `2/β`. R1: the origin is rarely in a finite cycle. -/
theorem rootR1 {d : ℕ} (hd : 5 ≤ d := by assumption) :
    ∃ β₀ : ℝ, 0 < β₀ ∧ ∀ β : ℝ, β₀ ≤ β → ∀ [Fact (0 < β)],
      ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (N : Ω → Measure (RingSpace d β)),
        IsPoissonPointProcess N (ringIntensity d β) P →
          P {ω | N ω ∈ finZeroEvent d β} < ENNReal.ofReal (2 / β) :=
  ElboimSly.Roots.root_R1_of_indMain.{u}
    (fun d hd => ElboimSly.Paper.Induction.ind_main_of_claimJ d hd
      (ElboimSly.Paper.Step.step78_claimJ hd)) d hd

end ElboimSly.Provider

end
