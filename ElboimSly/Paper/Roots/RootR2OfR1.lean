/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Roots.ShiftInfEvent
public import ElboimSly.Foundations.Interchange.GoodAs
public import ElboimSly.Frozen.Defs.IsPoissonPointProcess
import Mathlib

/-!
# R2 from R1 (conditional helper)

R2: Theorem 1 (proof).

`RootR1Stmt` and `RootR2Stmt` restate, verbatim, the propositions of `root_R1` and `root_R2`
(`ElboimSly/Frozen/Theorems/Root{R1,R2}.lean`), over all `d ≥ 5`, so that this file does not import
the statement files. `root_R2_of_R1` is the implication R1 ⇒ R2; `ElboimSly.Provider.rootR2` applies
it.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace ElboimSly.Roots

universe u

/-- The proposition of the frozen `root_R1`, for all `d ≥ 5`. -/
def RootR1Stmt : Prop :=
  ∀ (d : ℕ), 5 ≤ d →
    ∃ β₀ : ℝ, 0 < β₀ ∧ ∀ β : ℝ, β₀ ≤ β → ∀ [Fact (0 < β)],
      ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (N : Ω → Measure (RingSpace d β)),
        IsPoissonPointProcess N (ringIntensity d β) P →
          P {ω | N ω ∈ finZeroEvent d β} < ENNReal.ofReal (2 / β)

/-- The proposition of the frozen `root_R2`, for all `d ≥ 5`. -/
def RootR2Stmt : Prop :=
  ∀ (d : ℕ), 5 ≤ d →
    ∃ β₀ : ℝ, 0 < β₀ ∧ ∀ β : ℝ, β₀ ≤ β → ∀ [Fact (0 < β)],
      ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (N : Ω → Measure (RingSpace d β)),
        IsPoissonPointProcess N (ringIntensity d β) P →
          ∀ᵐ ω ∂P, N ω ∈ infEvent d β

/-- Conditional helper. R2: Theorem 1 (proof): R1, the zero-one law, translation
invariance and measurability of `Inf`. -/
theorem root_R2_of_R1 : RootR1Stmt.{u} → RootR2Stmt.{u} := by
  intro h1 d hd
  obtain ⟨β₀, hβ₀, h⟩ := h1 d hd
  refine ⟨max β₀ 2, lt_max_of_lt_left hβ₀, fun β hβ _ Ω _ P N hN => ?_⟩
  have : NeZero d := ⟨by omega⟩
  have := hN.isProbabilityMeasure
  have hβ2 : 2 ≤ β := le_trans (le_max_right _ _) hβ
  have hR1 := h β (le_trans (le_max_left _ _) hβ) Ω P N hN
  have hlt : P {ω | N ω ∈ finZeroEvent d β} < 1 := by
    refine lt_of_lt_of_le hR1 ?_
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal ((div_le_one (by linarith)).2 hβ2)
  have hzo := prob_mem_eq_zero_or_one hN Roots.measurableSet_infEvent
    Roots.isShiftInvariant_infEvent
  have hgood := Interchange.ae_good hN
  have hsub : (N ⁻¹' (infEvent d β)ᶜ) ⊆ (N ⁻¹' finZeroEvent d β) ∪ {ω | ¬ Good (N ω)} := by
    intro ω hω
    by_cases hg : Good (N ω)
    · exact Or.inl (Roots.mem_finZeroEvent_of_good_not_mem_infEvent hg hω)
    · exact Or.inr hg
  have hnull : P {ω | ¬ Good (N ω)} = 0 := ae_iff.1 hgood
  have hcompl : P (N ⁻¹' (infEvent d β)ᶜ) < 1 := by
    calc P (N ⁻¹' (infEvent d β)ᶜ)
        ≤ P ((N ⁻¹' finZeroEvent d β) ∪ {ω | ¬ Good (N ω)}) := measure_mono hsub
      _ ≤ P (N ⁻¹' finZeroEvent d β) + P {ω | ¬ Good (N ω)} := measure_union_le _ _
      _ < 1 := by rw [hnull, add_zero]; exact hlt
  have hmeasN : MeasurableSet (N ⁻¹' infEvent d β) :=
    hN.measurable Roots.measurableSet_infEvent
  have hone : P (N ⁻¹' infEvent d β) = 1 := by
    rcases hzo with h0 | h1'
    · exfalso
      have : P (N ⁻¹' (infEvent d β)ᶜ) = 1 := by
        rw [Set.preimage_compl, prob_compl_eq_one_sub hmeasN, h0]; simp
      exact absurd hcompl (by rw [this]; exact lt_irrefl _)
    · exact h1'
  rw [ae_iff]
  have : {ω | ¬ N ω ∈ infEvent d β} = N ⁻¹' (infEvent d β)ᶜ := rfl
  rw [this, Set.preimage_compl, prob_compl_eq_zero_iff hmeasN]
  exact hone

end ElboimSly.Roots

end
