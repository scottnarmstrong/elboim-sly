/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Base.ConstantsBeta4
public import Mathlib

/-!
# Constants and thresholds of the base

Constants and thresholds of the base (ES22 §8).  The definitions are in `Constants` (constants and
`n₁`), `ConstantsBeta4` (`β₀`, `n_K`, `n₀`).  This file bundles the properties stated in the
written proof.

* `es8_constants`: `c₁ ∈ (0,1)`; every `n ≥ n₀(d)` satisfies (n1)-(n6); `β₀ ≥ 1` and every
  `β ≥ β₀` satisfies (B1)-(B4).
-/

@[expose] public section

namespace ElboimSly.Paper

theorem le_es8n0 (d : ℕ) {n : ℕ} (hn : es8n0 d ≤ n) :
    20 ≤ n ∧ 2 * d ≤ n ∧ 77 ≤ n ∧ es8n1 d ≤ n ∧ ElboimSly.SRW.lem82nC d ≤ n ∧
      ElboimSly.SRW.lem82n2 d ≤ n ∧ 14980 ≤ n ∧ es8nK d ≤ n := by
  unfold es8n0 at hn
  simp only [max_le_iff] at hn
  exact ⟨hn.1, hn.2.1, hn.2.2.1, hn.2.2.2.1, hn.2.2.2.2.1, hn.2.2.2.2.2.1, hn.2.2.2.2.2.2.1,
    hn.2.2.2.2.2.2.2⟩

/-- Constants and thresholds of the base. -/
theorem es8_constants (d : ℕ) (hd : 5 ≤ d) :
    (0 < es8C1 d ∧ es8C1 d < 1) ∧
    (es8Zeta d = 1 / (6000 * (d : ℝ) ^ 2)) ∧
    (∀ n : ℕ, es8n0 d ≤ n →
      (20 ≤ n ∧ 2 * d ≤ n) ∧ es8n1 d ≤ n ∧ 77 ≤ n ∧
        (ElboimSly.SRW.lem82nC d ≤ n ∧ ElboimSly.SRW.lem82n2 d ≤ n) ∧ 14980 ≤ n ∧
        es8nK d ≤ n ∧
        389 ^ n * n ^ 4 < 390 ^ n ∧
        es8CA d * Real.exp (-(4 : ℝ) ^ n / 12) + (2 * 4 ^ n) ^ d * es8Eps d n ≤
          Real.exp (-(n : ℝ) ^ 3)) ∧
    (1 ≤ es8Beta0 d ∧ ∀ β : ℝ, es8Beta0 d ≤ β → es8BetaCond d β) := by
  refine ⟨⟨es8C1_pos d, es8C1_lt_one d⟩, es8Zeta_eq d, fun n hn => ?_,
    es8Beta0_spec (by omega)⟩
  obtain ⟨h20, h2d, h77, h1, hC, h2, h39, hK⟩ := le_es8n0 d hn
  exact ⟨⟨h20, h2d⟩, h1, h77, ⟨hC, h2⟩, h39, hK, es8_threshold_nat n h39, es8nK_spec d n hK⟩

end ElboimSly.Paper
