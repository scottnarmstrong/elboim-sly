/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Roots.RootR1OfIndMain
public import ElboimSly.Paper.Roots.RootR2OfR1
public import ElboimSly.Paper.Induction.MainOfClaimJ
public import ElboimSly.Paper.Step.Lemma78ClaimJ
import Mathlib

/-!
# Provider for `RootR2`

Proof of the main theorem `ElboimSly.Frozen.Theorems.RootR2` (R2: Theorem 1). The
proof is `ElboimSly.Roots.root_R2_of_R1` (R1 ⇒ R2, by the zero-one law) applied to R1, which is
`ElboimSly.Roots.root_R1_of_indMain` applied to Theorem 3.2
(`ElboimSly.Paper.Induction.ind_main_of_claimJ` with Lemma 7.8's excursion claim).
-/

public section

open MeasureTheory
open scoped ENNReal

namespace ElboimSly.Provider

universe u

/-- R2: for `d ≥ 5` and `β` large, the interchange process almost surely has an infinite cycle.
R2: Theorem 1. -/
theorem rootR2 {d : ℕ} (hd : 5 ≤ d := by assumption) :
    ∃ β₀ : ℝ, 0 < β₀ ∧ ∀ β : ℝ, β₀ ≤ β → ∀ [Fact (0 < β)],
      ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (N : Ω → Measure (RingSpace d β)),
        IsPoissonPointProcess N (ringIntensity d β) P →
          ∀ᵐ ω ∂P, N ω ∈ infEvent d β :=
  ElboimSly.Roots.root_R2_of_R1.{u}
    (ElboimSly.Roots.root_R1_of_indMain.{u}
      (fun d hd => ElboimSly.Paper.Induction.ind_main_of_claimJ d hd
        (ElboimSly.Paper.Step.step78_claimJ hd))) d hd

end ElboimSly.Provider

end
