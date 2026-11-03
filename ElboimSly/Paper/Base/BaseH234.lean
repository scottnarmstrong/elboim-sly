/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Base.IdentH4
public import Mathlib

/-!
# (H2), (H3), (H4) at the base

(8.1)--(8.3) and (H2)--(H4) at the base (d), (e), (f). For `d ≥ 5`, `t₀ ∈ (1,4]`, `t_n ≤ β`:

* `base_IndH2`: (H2) for all `n`;
* `base_IndH3`: (H3) for `n ≥ max (16, ⌈ln 4d⌉)`;
* `base_IndH4'`: (H4) for `n ≥ max (n₁(d), 77)`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Paper

variable {d : ℕ} {β : ℝ} [Fact (0 < β)]

theorem base_IndH2 {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (N : Ω → Measure (ℕ × RingSpace d β))
    (hN : IsPoissonPointProcess N ((Measure.count : Measure ℕ).prod (ringIntensity d β)) P)
    (n : ℕ) {t₀ : ℝ} (htβ : indScale t₀ n ≤ β) : IndH2 P N n t₀ := by
  intro t ht u
  exact base_H2 hN ht.1 (ht.2.trans htβ) u

theorem base_IndH3 [NeZero d] {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (N : Ω → Measure (ℕ × RingSpace d β))
    (hN : IsPoissonPointProcess N ((Measure.count : Measure ℕ).prod (ringIntensity d β)) P)
    {n : ℕ} (hn16 : 16 ≤ n) (hd : Real.log (4 * d) ≤ n) {t₀ : ℝ} (ht1 : 1 < t₀)
    (htβ : indScale t₀ n ≤ β) : IndH3 P N n t₀ := by
  have h := base_H3_event hN hn16 hd ht1 htβ
  refine h.trans (ENNReal.ofReal_le_ofReal ?_)
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have h16 : (16 : ℝ) ≤ n := by exact_mod_cast hn16
  unfold indFailBound
  split_ifs
  · exact le_rfl
  · exact Real.exp_le_exp.2 (by nlinarith [pow_pos (show (0 : ℝ) < n by linarith) 2])

end ElboimSly.Paper

end
