/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Frozen.Defs.IndDelta
public import ElboimSly.Frozen.Defs.IndScale
public import ElboimSly.Paper.Escape.Gamma
public import Mathlib

/-!
# Scales of ES22 §6

Scales; the constants m_0, j, k, t'_k (ES22 §5, ES22 §6, ES22 §6, ES22 §6).

All quantities are functions of `d`, `t₀` (when they involve `t_n`) and `n`.

* `heavyEps d = 1/(300 d)` (`ε` of constants, scales, failure bounds; not otherwise defined in Lean).
* `heavyM0 d t₀ n = ⌊δ log₂ t_n⌋`.
* `heavyScaleJ n`: the unique `j` with `n^20 ≤ 2^j < 2 n^20` (`n ≥ 2`), here `⌈log₂ n^20⌉`.
* `heavyTrials d n = ⌈n^(γ+3)⌉`.
* `heavyLevel d n = k = ⌊4δ n⌋`, `heavyTkPrime d t₀ n = t'_k = t_k / k^4`,
  `heavyLevelPrime = k' = ⌈log₄ t'_k⌉ - 1`, `heavyT0pp = t₀'' = t'_k / 4^{k'}`.
* `heavyD m n = n² 4^m`, `heavyKappa = k - 2 log₂ k - 1`, `heavyH = t_n^{ε/2}`.

Deviation F55: `t'_k = t_k / k^4` (not `4^k/k^4`).
-/

@[expose] public section

namespace ElboimSly.Paper

open ElboimSly

/-- `ε = 1/(300 d)`. -/
noncomputable def heavyEps (d : ℕ) : ℝ := 1 / (300 * (d : ℝ))

/-- `m₀ = ⌊δ log₂ t_n⌋`. -/
noncomputable def heavyM0 (d : ℕ) (t₀ : ℝ) (n : ℕ) : ℕ :=
  ⌊indDelta d * Real.logb 2 (indScale t₀ n)⌋₊

/-- The escape scale `j_n`: `n^20 ≤ 2^j < 2 n^20`. -/
def heavyScaleJ (n : ℕ) : ℕ := Nat.clog 2 (n ^ 20)

/-- The number of entrance trials `K_n = ⌈n^{γ+3}⌉`. -/
noncomputable def heavyTrials (d n : ℕ) : ℕ := ⌈(n : ℝ) ^ (escGamma d + 3)⌉₊

/-- The level `k = ⌊4 δ n⌋`. -/
noncomputable def heavyLevel (d n : ℕ) : ℕ := ⌊4 * indDelta d * n⌋₊

/-- `t'_k = t_k / k^4` (deviation F55). -/
noncomputable def heavyTkPrime (d : ℕ) (t₀ : ℝ) (n : ℕ) : ℝ :=
  indScale t₀ (heavyLevel d n) / (heavyLevel d n : ℝ) ^ 4

/-- `k' = ⌈log₄ t'_k⌉ - 1`. -/
noncomputable def heavyLevelPrime (d : ℕ) (t₀ : ℝ) (n : ℕ) : ℕ :=
  ⌈Real.logb 4 (heavyTkPrime d t₀ n)⌉₊ - 1

/-- `t₀'' = t'_k / 4^{k'}`. -/
noncomputable def heavyT0pp (d : ℕ) (t₀ : ℝ) (n : ℕ) : ℝ :=
  heavyTkPrime d t₀ n / 4 ^ heavyLevelPrime d t₀ n

/-- `D_m = n² 4^m`. -/
def heavyD (n m : ℕ) : ℕ := n ^ 2 * 4 ^ m

/-- `κ = k - 2 log₂ k - 1`. -/
noncomputable def heavyKappa (d n : ℕ) : ℝ :=
  (heavyLevel d n : ℝ) - 2 * Real.logb 2 (heavyLevel d n) - 1

/-- `h = t_n^{ε/2}`. -/
noncomputable def heavyH (d : ℕ) (t₀ : ℝ) (n : ℕ) : ℝ :=
  indScale t₀ n ^ (heavyEps d / 2)

theorem heavyScaleJ_spec {n : ℕ} (hn : 2 ≤ n) :
    n ^ 20 ≤ 2 ^ heavyScaleJ n ∧ 2 ^ heavyScaleJ n < 2 * n ^ 20 := by
  refine ⟨Nat.le_pow_clog (by norm_num) _, ?_⟩
  have h1 : 1 < n ^ 20 := Nat.one_lt_pow (by norm_num) (by omega)
  have h0 : heavyScaleJ n ≠ 0 := by
    unfold heavyScaleJ
    exact (Nat.clog_pos (by norm_num) h1).ne'
  have := Nat.pow_pred_clog_lt_self (b := 2) (x := n ^ 20) (by norm_num) h1
  have e : 2 ^ heavyScaleJ n = 2 * 2 ^ (heavyScaleJ n - 1) := by
    rw [← pow_succ']; congr 1; omega
  simp only [Nat.pred_eq_sub_one] at this
  unfold heavyScaleJ at e ⊢
  omega

end ElboimSly.Paper
