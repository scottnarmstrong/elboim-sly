/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Escape.C56Slice
public import ElboimSly.Paper.Escape.C56GProps
public import ElboimSly.Paper.Escape.C56Det3
public import ElboimSly.Paper.Escape.C56Rel
public import ElboimSly.Paper.Avoid.Couple
public import Mathlib

/-!
# ES22 Claim 5.6, phase `i`: the pointwise implication

ES22 Claim 5.6.  For an outcome `ω` at which the coupling `W̃` of ES22 Lemma 2.1 has its
a.s. properties, `G_{i-1} ∩ E^a ∩ E^d ∩ E^b ⊆ ℬ_i`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Escape

open ElboimSly.Cyclic ElboimSly.Paper ElboimSly.Brownian

variable {k : ℕ} {β : ℝ} [Fact (0 < β)] {Ω : Type} [mΩ : MeasurableSpace Ω]

/-- The conclusions of ES22 Lemma 2.1 at the time `t`, for the outcome `ω`. -/
def CoupleFacts (N M : Ω → Measure (CycS ℕ (k + 2) β)) (ω : Ω) (t : ℝ≥0) : Prop :=
  (∀ s : ℝ≥0, ENNReal.ofReal ((t : ℝ) + s) ≤ avoidThit N ω (t : ℝ) →
    avoidWalk N ω ((t : ℝ) + s) - avoidWalk N ω (t : ℝ) = avoidPath (cycNgood M) ω s) ∧
  (regenStart (avoidEnv N ω) (t : ℝ) < t →
    ∀ s : ℝ≥0, ENNReal.ofReal ((t : ℝ) + s) ≤ avoidThit N ω (t : ℝ) →
      (s : ℝ≥0∞) < cycTreg (avoidEnv M ω 0)) ∧
  (regenStart (avoidEnv N ω) (t : ℝ) = t → avoidThit N ω (t : ℝ) = ⊤) ∧
  avoidThit N ω (t : ℝ) =
    ⨅ s ∈ {s : ℝ | (t : ℝ) < s ∧ ∃ s' : ℝ, (∃ kk : ℤ, s' = s + kk * β) ∧
      regenStart (avoidEnv N ω) (t : ℝ) < s' ∧ s' < t ∧
      ‖avoidWalk N ω (t : ℝ) + avoidPath (cycNgood M) ω (s - t).toNNReal -
        avoidWalk N ω s'‖ ≤ 1}, ENNReal.ofReal s

theorem escYv_eq_of_nonneg {N : Ω → Measure (CycS ℕ (k + 2) β)} (v : Fin (k + 2) → ℤ) {ω : Ω}
    (hω : cycNgood N ω = N ω) {r : ℝ} (hr : 0 ≤ r) :
    escYv N v ω r = v + avoidWalk N ω r := by
  have := cpR_escCPath hω hr
  simp only [cpR] at this
  simp only [escYv, escY, escW]
  have h2 : avoidPath (cycNgood N) ω r.toNNReal = regenWalk (avoidEnv N ω) r := this
  rw [h2]; rfl

end ElboimSly.Paper.Escape

end
