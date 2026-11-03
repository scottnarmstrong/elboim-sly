/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.PPP.Exploration.CountF
import Mathlib

/-!
# Sequential first-point exploration: resampling at infinity

Sequential first-point exploration (c), `k = ∞` (Step 5).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace ElboimSly

theorem eventually_eq_of_nat_tendsto (a : ℕ → ℝ≥0∞) (ha : ∀ k, ∃ n : ℕ, a k = n) {L : ℝ≥0∞}
    (hL : L ≠ ∞) (h : Tendsto a atTop (𝓝 L)) : ∀ᶠ k in atTop, a k = L := by
  choose n hn using ha
  have hr : Tendsto (fun k => (n k : ℝ)) atTop (𝓝 L.toReal) := by
    have := (ENNReal.tendsto_toReal hL).comp h
    refine this.congr fun k => ?_
    simp [Function.comp, hn k]
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 hr) (1 / 2) (by norm_num)
  have hconst : ∀ k ≥ N, n k = n N := by
    intro k hk
    have h1 := hN k hk
    have h2 := hN N le_rfl
    rw [Real.dist_eq] at h1 h2
    have : |((n k : ℝ) - n N)| < 1 := by
      calc |((n k : ℝ) - n N)| = |((n k : ℝ) - L.toReal) - ((n N : ℝ) - L.toReal)| := by ring_nf
        _ ≤ |(n k : ℝ) - L.toReal| + |(n N : ℝ) - L.toReal| := abs_sub _ _
        _ < 1 := by linarith
    have : (n k : ℤ) = n N := by
      have h3 : |((n k : ℤ) - n N : ℤ)| < 1 := by exact_mod_cast this
      have := abs_lt.1 h3
      omega
    exact_mod_cast this
  have hev : ∀ᶠ k in atTop, a k = a N := by
    filter_upwards [eventually_ge_atTop N] with k hk
    rw [hn k, hn N, hconst k hk]
  have hlim : Tendsto a atTop (𝓝 (a N)) := tendsto_const_nhds.congr' (hev.mono fun k hk => hk.symm)
  have := tendsto_nhds_unique h hlim
  filter_upwards [hev] with k hk
  rw [hk, this]

end ElboimSly
