/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Step.BlockSpace
public import ElboimSly.Paper.Step.BlockPath
public import ElboimSly.Paper.Step.BlockParams
public import ElboimSly.Paper.Step.Lemma74
public import ElboimSly.Paper.Step.TravelLaw
public import ElboimSly.Foundations.Brownian.Oscillation
public import Mathlib

/-!
# The probabilities of the events `E₁, E₂, E₄` of Lemma 7.6 (Step 3)

ES22 Lemma 7.6, Step 3. On the probability space of `lemma76_space`:

* `E₁`: the natural coupling is not `ℓ t_n^{2ε}`-close to `W` (`StepCor72`), probability at most
  `(ℓ-1) e^{-c_cat n³}`;
* `E₂`: some block leaves `(-K, K)`, `K = n²√T` (`StepTr`, Lemma 7.4 at time `T`), probability at
  most `ℓ e^{-c_tr n³}`;
* `E₄`: the Brownian oscillation over some block is at least `K` (oscillation), probability at
  most `4dℓ e^{-n⁴/16}`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set ElboimSly.Cyclic ElboimSly.SRW
open scoped NNReal ENNReal

namespace ElboimSly.Paper.Step

open ElboimSly.Paper

variable {d : ℕ} {β : ℝ} [Fact (0 < β)]

section Events

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → PathSpace d}
  {Ωe : Type} [MeasurableSpace Ωe] {Pe : Measure Ωe} {N : Ωe → Measure (ℕ × RingSpace d β)}

/-- `P(E₂) ≤ ℓ e^{-c n³}`: some block endpoint is far, from the tail bound of the regenerated
walk at time `T`. -/
theorem measure_blocks_far (hX : IsSRW P X) (hXp : ∀ ω, X ω ∈ StepPath d)
    (hN : IsPoissonPointProcess N ((Measure.count : Measure ℕ).prod (ringIntensity d β)) Pe)
    (T : ℝ≥0) (K : ℝ) (ℓ : ℕ) {p : ℝ}
    (htail : Pe.real {ω | ∃ s : ℝ≥0, (s : ℝ) ≤ T ∧
      K ≤ ‖regenWalk (fun j => copyEnv (N ω) j) (s : ℝ)‖} ≤ p) :
    P (⋃ j ∈ Finset.range ℓ, {ω | stepWj β 0 (fun _ => T) (X ω) j ∈ farSet K T}) ≤
      ℓ * ENNReal.ofReal p := by
  have := hN.isProbabilityMeasure
  refine (measure_biUnion_finset_le _ _).trans ?_
  have h1 : ∀ j ∈ Finset.range ℓ,
      P {ω | stepWj β 0 (fun _ => T) (X ω) j ∈ farSet K T} ≤ ENNReal.ofReal p := by
    intro j _
    rw [measure_stepWj_farSet hX hXp hN 0 T K j]
    refine (ppLaw_tail hN T K).trans ?_
    rw [← ENNReal.ofReal_toReal (measure_ne_top Pe _)]
    exact ENNReal.ofReal_le_ofReal htail
  calc ∑ j ∈ Finset.range ℓ, P {ω | stepWj β 0 (fun _ => T) (X ω) j ∈ farSet K T}
      ≤ ∑ _j ∈ Finset.range ℓ, ENNReal.ofReal p := Finset.sum_le_sum h1
    _ = ℓ * ENNReal.ofReal p := by simp

end Events

/-- The sum over `{i : Fin ℓ | i ≤ j}` is the sum over `range (j+1)`. -/
theorem sum_filter_fin_le {V : Type*} [AddCommMonoid V] {ℓ : ℕ} (f : ℕ → V) (j : Fin ℓ) :
    ∑ i ∈ Finset.univ.filter (· ≤ j), f (i : ℕ) = ∑ i ∈ Finset.range ((j : ℕ) + 1), f i := by
  classical
  rw [Finset.sum_filter]
  have h1 : ∑ i : Fin ℓ, (if i ≤ j then f (i : ℕ) else 0) =
      ∑ i : Fin ℓ, (fun m : ℕ => if m ≤ (j : ℕ) then f m else 0) (i : ℕ) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h : i ≤ j
    · have : (i : ℕ) ≤ (j : ℕ) := h
      simp [h, this]
    · have : ¬ (i : ℕ) ≤ (j : ℕ) := h
      simp [h, this]
  rw [h1, Fin.sum_univ_eq_sum_range (fun m : ℕ => if m ≤ (j : ℕ) then f m else 0) ℓ,
    ← Finset.sum_filter]
  congr 1
  ext m
  simp only [Finset.mem_filter, Finset.mem_range]
  have := j.2
  omega

end ElboimSly.Paper.Step
