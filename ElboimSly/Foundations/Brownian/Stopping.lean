/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Brownian.Freeze
import Mathlib

/-!
# Random times with countably many values

Random times with countably many values.

A random time is `τ : Ω → [0,∞]` (`ℝ≥0∞`); `B(τ)` and `sh_τ B` are evaluated at `(τ ω).toNNReal`
and only used on `{τ < ∞}`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace ElboimSly.Brownian

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {d : ℕ}

/-- Random times with countably many values. Let `T ⊆ [0,∞)` be countable and `τ` take values in
`T ∪ {∞}` with `{τ = a} ∈ ℱ_a` for `a ∈ T`; let `E` satisfy `E ∩ {τ = a} ∈ ℱ_a`. Then for
`Φ : ℝ^d × W → [0,∞]` measurable and `Ψ(z) = ∫ Φ(z,w) Wiener(dw)`,
`E[1_{E ∩ {τ<∞}} Φ(B(τ), sh_τ B)] = E[1_{E ∩ {τ<∞}} Ψ(B(τ))]`. -/
theorem _root_.ElboimSly.IsStandardBrownianMotion.lintegral_discrete_stopping
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → (Fin d → ℝ)} (hB : IsStandardBrownianMotion d B P)
    {T : Set ℝ≥0} (hT : T.Countable) {τ : Ω → ℝ≥0∞}
    (hτT : ∀ ω, τ ω ≠ ∞ → ∃ a ∈ T, τ ω = a)
    (_hτ : ∀ a ∈ T, MeasurableSet[bmFiltration B a] {ω | τ ω = a})
    {E : Set Ω} (hE : ∀ a ∈ T, MeasurableSet[bmFiltration B a] (E ∩ {ω | τ ω = a}))
    {Φ : (Fin d → ℝ) → (ℝ≥0 → Fin d → ℝ) → ℝ≥0∞} (hΦ : Measurable (Function.uncurry Φ)) :
    ∫⁻ ω, (E ∩ {ω | τ ω < ∞}).indicator
        (fun ω => Φ (B (τ ω).toNNReal ω) (shiftPath B (τ ω).toNNReal ω)) ω ∂P =
      ∫⁻ ω, (E ∩ {ω | τ ω < ∞}).indicator
        (fun ω => ∫⁻ w, Φ (B (τ ω).toNNReal ω) w ∂(wienerMeasure d)) ω ∂P := by
  have : Countable T := hT.to_subtype
  let S : T → Set Ω := fun a => E ∩ {ω | τ ω = ((a.1 : ℝ≥0) : ℝ≥0∞)}
  have hSm : ∀ a, MeasurableSet (S a) := fun a => bmFiltration_le hB.measurable a.1 _ (hE a.1 a.2)
  have hSd : Pairwise (Function.onFun Disjoint S) := by
    intro a b hab
    refine Set.disjoint_left.2 fun ω ha hb => hab ?_
    have : ((a.1 : ℝ≥0) : ℝ≥0∞) = ((b.1 : ℝ≥0) : ℝ≥0∞) := ha.2.symm.trans hb.2
    exact Subtype.ext (by exact_mod_cast this)
  have hU : (E ∩ {ω | τ ω < ∞}) = ⋃ a, S a := by
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_iUnion, S]
    constructor
    · rintro ⟨hE', hlt⟩
      obtain ⟨a, haT, ha⟩ := hτT ω hlt.ne
      exact ⟨⟨a, haT⟩, hE', ha⟩
    · rintro ⟨a, hE', ha⟩
      exact ⟨hE', by rw [ha]; exact ENNReal.coe_lt_top⟩
  have hUm : MeasurableSet (E ∩ {ω | τ ω < ∞}) := hU ▸ MeasurableSet.iUnion hSm
  have key : ∀ f : ℝ≥0 → Ω → ℝ≥0∞, ∫⁻ ω, (E ∩ {ω | τ ω < ∞}).indicator
      (fun ω => f (τ ω).toNNReal ω) ω ∂P = ∑' a : T, ∫⁻ ω, (S a).indicator (f a.1) ω ∂P := by
    intro f
    rw [lintegral_indicator hUm, hU, lintegral_iUnion hSm hSd]
    refine tsum_congr fun a => ?_
    rw [lintegral_indicator (hSm a)]
    refine setLIntegral_congr_fun (hSm a) fun ω hω => ?_
    have h2 : τ ω = ((a.1 : ℝ≥0) : ℝ≥0∞) := hω.2
    rw [h2, ENNReal.toNNReal_coe]
  rw [key (fun a ω => Φ (B a ω) (shiftPath B a ω)),
    key (fun a ω => ∫⁻ w, Φ (B a ω) w ∂(wienerMeasure d))]
  refine tsum_congr fun a => ?_
  exact hB.lintegral_indicator_shift a.1 (measurable_bmFiltration le_rfl) (hE a.1 a.2) hΦ

/-- Random times with countably many values, the bound. If in addition `Ψ ≤ c` on a measurable set
`A`, and `B(τ) ∈ A` on `E ∩ {τ < ∞}`, then the left side is at most `c P(E ∩ {τ<∞})`. -/
theorem _root_.ElboimSly.IsStandardBrownianMotion.lintegral_discrete_stopping_le
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → (Fin d → ℝ)} (hB : IsStandardBrownianMotion d B P)
    {T : Set ℝ≥0} (hT : T.Countable) {τ : Ω → ℝ≥0∞}
    (hτT : ∀ ω, τ ω ≠ ∞ → ∃ a ∈ T, τ ω = a)
    (hτ : ∀ a ∈ T, MeasurableSet[bmFiltration B a] {ω | τ ω = a})
    {E : Set Ω} (hE : ∀ a ∈ T, MeasurableSet[bmFiltration B a] (E ∩ {ω | τ ω = a}))
    {Φ : (Fin d → ℝ) → (ℝ≥0 → Fin d → ℝ) → ℝ≥0∞} (hΦ : Measurable (Function.uncurry Φ))
    {A : Set (Fin d → ℝ)} {c : ℝ≥0∞} (hΨ : ∀ z ∈ A, ∫⁻ w, Φ z w ∂(wienerMeasure d) ≤ c)
    (hA : ∀ ω ∈ E ∩ {ω | τ ω < ∞}, B (τ ω).toNNReal ω ∈ A) :
    ∫⁻ ω, (E ∩ {ω | τ ω < ∞}).indicator
        (fun ω => Φ (B (τ ω).toNNReal ω) (shiftPath B (τ ω).toNNReal ω)) ω ∂P ≤
      c * P (E ∩ {ω | τ ω < ∞}) := by
  have : Countable T := hT.to_subtype
  rw [hB.lintegral_discrete_stopping hT hτT hτ hE hΦ]
  have hUm : MeasurableSet (E ∩ {ω | τ ω < ∞}) := by
    have : (E ∩ {ω | τ ω < ∞}) = ⋃ a : T, E ∩ {ω | τ ω = ((a.1 : ℝ≥0) : ℝ≥0∞)} := by
      ext ω
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_iUnion]
      constructor
      · rintro ⟨hE', hlt⟩
        obtain ⟨a, haT, ha⟩ := hτT ω hlt.ne
        exact ⟨⟨a, haT⟩, hE', ha⟩
      · rintro ⟨a, hE', ha⟩
        exact ⟨hE', by rw [ha]; exact ENNReal.coe_lt_top⟩
    rw [this]
    exact MeasurableSet.iUnion fun a => bmFiltration_le hB.measurable a.1 _ (hE a.1 a.2)
  calc _ ≤ ∫⁻ ω, (E ∩ {ω | τ ω < ∞}).indicator (fun _ => c) ω ∂P := by
        refine lintegral_mono fun ω => ?_
        by_cases h : ω ∈ E ∩ {ω | τ ω < ∞}
        · simp only [Set.indicator_of_mem h]
          exact hΨ _ (hA ω h)
        · simp [Set.indicator_of_notMem h]
    _ = c * P (E ∩ {ω | τ ω < ∞}) := by
        rw [lintegral_indicator_const hUm, mul_comm]

end ElboimSly.Brownian
