/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Ergodic.Mixing
import Mathlib

/-!
# The zero-one law for translation-invariant events

Zero-one law for translation-invariant events.

Both parts are proved from mixing.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace ElboimSly

variable {d : ℕ} {β : ℝ}

theorem thetaShift_iterate (z : Fin d → ℤ) (k : ℕ) :
    (thetaShift d β z)^[k] = thetaShift d β (k • z) := by
  induction k with
  | zero => funext ν; simp [thetaShift_zero]
  | succ k ih =>
    funext ν
    rw [Function.iterate_succ_apply', ih, thetaShift_add, succ_nsmul, add_comm]

theorem exists_norm_nsmul_gt {z : Fin d → ℤ} (hz : z ≠ 0) (R : ℝ) :
    ∃ k : ℕ, R < ‖k • z‖ := by
  obtain ⟨i, hi⟩ : ∃ i, z i ≠ 0 := by
    by_contra h
    push Not at h
    exact hz (funext h)
  refine ⟨⌈R⌉₊ + 1, ?_⟩
  have h1 : (1 : ℝ) ≤ ‖z i‖ := by
    rw [Int.norm_eq_abs]
    exact_mod_cast Int.one_le_abs hi
  have h2 : ‖((⌈R⌉₊ + 1) • z) i‖ ≤ ‖(⌈R⌉₊ + 1) • z‖ := norm_le_pi_norm _ i
  have h3 : ‖((⌈R⌉₊ + 1) • z) i‖ = ((⌈R⌉₊ + 1 : ℕ) : ℝ) * ‖z i‖ := by
    simp [Int.norm_eq_abs]
    left; positivity
  have h4 : R < ((⌈R⌉₊ + 1 : ℕ) : ℝ) := by
    push_cast
    linarith [Nat.le_ceil R]
  nlinarith [Nat.cast_nonneg (α := ℝ) (⌈R⌉₊ + 1)]

/-- Zero-one law for translation-invariant events (b), strictly invariant measurable sets: the zero-one law. -/
theorem ringLaw_eq_zero_or_one_of_preimage_eq [Fact (0 < β)]
    {z₀ : Fin d → ℤ} (hz₀ : z₀ ≠ 0) {A : Set (Measure (RingSpace d β))}
    (hA : MeasurableSet A) (hinv : thetaShift d β z₀ ⁻¹' A = A) :
    ringLaw d β A = 0 ∨ ringLaw d β A = 1 := by
  have key : ∀ ε : ℝ, 0 < ε →
      |(ringLaw d β).real A - (ringLaw d β).real A * (ringLaw d β).real A| ≤ ε := by
    intro ε hε
    obtain ⟨R, hR⟩ := ringLaw_mixing hA hA hε
    obtain ⟨k, hk⟩ := exists_norm_nsmul_gt hz₀ R
    have hiter : ∀ k : ℕ, (thetaShift d β z₀)^[k] ⁻¹' A = A := by
      intro k
      induction k with
      | zero => rfl
      | succ k ih => rw [Function.iterate_succ, Set.preimage_comp, ih, hinv]
    have := hR (k • z₀) hk
    rwa [← thetaShift_iterate, hiter k, Set.inter_self] at this
  have h0 : (ringLaw d β).real A - (ringLaw d β).real A * (ringLaw d β).real A = 0 := by
    by_contra hne
    have := key (|(ringLaw d β).real A - (ringLaw d β).real A * (ringLaw d β).real A| / 2)
      (by positivity)
    have hpos := abs_pos.2 hne
    linarith
  have hp : (ringLaw d β).real A = 0 ∨ (ringLaw d β).real A = 1 := by
    have : (ringLaw d β).real A * (1 - (ringLaw d β).real A) = 0 := by linarith
    rcases mul_eq_zero.1 this with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (by linarith)
  simpa [Measure.real, ENNReal.toReal_eq_zero_iff, measure_ne_top,
    ENNReal.toReal_eq_one_iff] using hp

/-- Zero-one law for translation-invariant events (a): every translation-invariant event has probability `0` or
`1` under `Π`. -/
theorem ringLaw_eq_zero_or_one [NeZero d] [Fact (0 < β)]
    {A : Set (Measure (RingSpace d β))} (hA : MeasurableSet A) (hinv : IsShiftInvariant d β A) :
    ringLaw d β A = 0 ∨ ringLaw d β A = 1 := by
  have hz : (Pi.single ⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩ (1 : ℤ) : Fin d → ℤ) ≠ 0 := by
    intro h0
    have := congrFun h0 ⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩
    simp at this
  exact ringLaw_eq_zero_or_one_of_preimage_eq hz hA (hinv _)

/-- Zero-one law for translation-invariant events (a), second sentence: for every PPP `N` with intensity `μ_β`,
`ℙ(N ∈ A) ∈ {0, 1}`. -/
theorem prob_mem_eq_zero_or_one [NeZero d] [Fact (0 < β)]
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {N : Ω → Measure (RingSpace d β)}
    (hN : IsPoissonPointProcess N (ringIntensity d β) P)
    {A : Set (Measure (RingSpace d β))} (hA : MeasurableSet A) (hinv : IsShiftInvariant d β A) :
    P (N ⁻¹' A) = 0 ∨ P (N ⁻¹' A) = 1 := by
  have := ringLaw_eq_zero_or_one hA hinv
  rwa [← map_eq_ringLaw hN, Measure.map_apply hN.measurable hA] at this

end ElboimSly
