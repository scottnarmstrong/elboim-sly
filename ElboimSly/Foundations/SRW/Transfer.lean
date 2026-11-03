/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.SRW.Law1d
public import ElboimSly.Foundations.SRW.CountableReduction
public import ElboimSly.Foundations.SRW.Iid
public import Mathlib

/-!
# Transfer of path events to the canonical walk

Countable reduction of path events (i) applied to SRWs: probabilities of events quantified over all
times are determined by the law, because the paths are regular and the events reduce to countable
ones.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ElboimSly
namespace SRW

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {Z : Ω → PathSpace d}

/-- The countable form of `∃ s ≤ T, γ s ∈ K`. -/
def iccEvent (d : ℕ) (T : ℝ≥0) (K : Set (Fin d → ℤ)) : Set (PathSpace d) :=
  {γ | γ T ∈ K} ∪ ⋃ r : ℚ, {γ | ratNN r < T ∧ γ (ratNN r) ∈ K}

theorem measurableSet_iccEvent (T : ℝ≥0) (K : Set (Fin d → ℤ)) :
    MeasurableSet (iccEvent d T K) := by
  refine MeasurableSet.union ((measurable_pi_apply T) (MeasurableSet.of_discrete (s := K))) ?_
  refine MeasurableSet.iUnion fun r => ?_
  by_cases h : ratNN r < T
  · have : {γ : PathSpace d | ratNN r < T ∧ γ (ratNN r) ∈ K} = {γ | γ (ratNN r) ∈ K} := by
      ext γ; simp [h]
    rw [this]; exact (measurable_pi_apply _) (MeasurableSet.of_discrete (s := K))
  · have : {γ : PathSpace d | ratNN r < T ∧ γ (ratNN r) ∈ K} = ∅ := by
      ext γ; simp [h]
    rw [this]; exact MeasurableSet.empty

theorem exists_eq_iccEvent {Ω₁ : Type*} (W : Ω₁ → PathSpace d) (hW : ∀ ω, IsRegularPath (W ω))
    (T : ℝ≥0) (K : Set (Fin d → ℤ)) :
    {ω | ∃ s, s ≤ T ∧ W ω s ∈ K} = W ⁻¹' iccEvent d T K := by
  ext ω
  have := (hW ω).exists_Icc_iff K (a := 0) (b := T) (by simp)
  simp only [zero_le, true_and] at this
  simp only [iccEvent, mem_preimage, mem_union, mem_iUnion, mem_ofPred_eq]
  exact this

/-- Events `∃ s ≤ T, Z(s) ∈ K` have the probability of the canonical walk. -/
theorem IsSRW.exists_canonical_Icc (hZ : IsSRW P Z) (T : ℝ≥0) (K : Set (Fin d → ℤ)) :
    ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (P' : Measure Ω') (N' : Ω' → Measure (Dir d × ℝ)),
      IsPoissonPointProcess N' (clockIntensity (Dir d)) P' ∧
        P {ω | ∃ s, s ≤ T ∧ Z ω s ∈ K} = P' {ω | ∃ s, s ≤ T ∧ canonical d N' ω s ∈ K} := by
  obtain ⟨Ω', _, P', N', hN', hE⟩ := hZ.exists_canonical
  refine ⟨Ω', inferInstance, P', N', hN', ?_⟩
  rw [exists_eq_iccEvent Z hZ.2.1, exists_eq_iccEvent _ (isRegularPath_canonical N')]
  exact hE _ (measurableSet_iccEvent T K)

/-- The countable form of the pair event. -/
def pairEvent (d : ℕ) (T h : ℝ≥0) (R : (Fin d → ℤ) → (Fin d → ℤ) → Prop) : Set (PathSpace d) :=
  ⋃ q ∈ (range ratNN ∪ {T} : Set ℝ≥0), ⋃ q' ∈ (range ratNN ∪ {T} : Set ℝ≥0),
    {γ | q ≤ q' ∧ q' ≤ T ∧ q' - q ≤ h ∧ R (γ q) (γ q')}

theorem measurableSet_pairEvent (T h : ℝ≥0) (R : (Fin d → ℤ) → (Fin d → ℤ) → Prop) :
    MeasurableSet (pairEvent d T h R) := by
  have hQ : (range ratNN ∪ {T} : Set ℝ≥0).Countable :=
    (countable_range _).union (countable_singleton _)
  refine MeasurableSet.biUnion hQ fun q _ => MeasurableSet.biUnion hQ fun q' _ => ?_
  by_cases hc : q ≤ q' ∧ q' ≤ T ∧ q' - q ≤ h
  · have : {γ : PathSpace d | q ≤ q' ∧ q' ≤ T ∧ q' - q ≤ h ∧ R (γ q) (γ q')} =
        (fun γ : PathSpace d => (γ q, γ q')) ⁻¹' {p | R p.1 p.2} := by
      ext γ; simp [hc.1, hc.2.1, hc.2.2]
    rw [this]
    exact (((measurable_pi_apply q).prodMk (measurable_pi_apply q')))
      (MeasurableSet.of_discrete)
  · have : {γ : PathSpace d | q ≤ q' ∧ q' ≤ T ∧ q' - q ≤ h ∧ R (γ q) (γ q')} = ∅ := by
      ext γ; simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
      exact fun h' => hc ⟨h'.1, h'.2.1, h'.2.2.1⟩
    rw [this]; exact MeasurableSet.empty

theorem exists_eq_pairEvent {Ω₁ : Type*} (W : Ω₁ → PathSpace d) (hW : ∀ ω, IsRegularPath (W ω))
    (T h : ℝ≥0) (R : (Fin d → ℤ) → (Fin d → ℤ) → Prop) :
    {ω | ∃ s s', s ≤ s' ∧ s' ≤ T ∧ s' - s ≤ h ∧ R (W ω s) (W ω s')} =
      W ⁻¹' pairEvent d T h R := by
  ext ω
  have := (hW ω).exists_pair_iff R (a := 0) (b := T) (h := h) (by simp)
  simp only [zero_le, true_and] at this
  rw [mem_ofPred_eq, this]
  simp only [pairEvent, mem_preimage, mem_iUnion, mem_ofPred_eq, mem_union, mem_singleton_iff,
    mem_range, exists_prop]
  constructor
  · rintro ⟨q, q', hq, hq', h1, h2, h3, h4⟩
    exact ⟨q, hq, q', hq', h1, h2, h3, h4⟩
  · rintro ⟨q, hq, q', hq', h1, h2, h3, h4⟩
    exact ⟨q, q', hq, hq', h1, h2, h3, h4⟩

/-- Events `∃ s ≤ s' ≤ T, s' - s ≤ h, R(Z s, Z s')` have the probability of the canonical walk. -/
theorem IsSRW.exists_canonical_pair (hZ : IsSRW P Z) (T h : ℝ≥0)
    (R : (Fin d → ℤ) → (Fin d → ℤ) → Prop) :
    ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (P' : Measure Ω') (N' : Ω' → Measure (Dir d × ℝ)),
      IsPoissonPointProcess N' (clockIntensity (Dir d)) P' ∧
        P {ω | ∃ s s', s ≤ s' ∧ s' ≤ T ∧ s' - s ≤ h ∧ R (Z ω s) (Z ω s')} =
          P' {ω | ∃ s s', s ≤ s' ∧ s' ≤ T ∧ s' - s ≤ h ∧
            R (canonical d N' ω s) (canonical d N' ω s')} := by
  obtain ⟨Ω', _, P', N', hN', hE⟩ := hZ.exists_canonical
  refine ⟨Ω', inferInstance, P', N', hN', ?_⟩
  rw [exists_eq_pairEvent Z hZ.2.1, exists_eq_pairEvent _ (isRegularPath_canonical N')]
  exact hE _ (measurableSet_pairEvent T h R)

end SRW
end ElboimSly
