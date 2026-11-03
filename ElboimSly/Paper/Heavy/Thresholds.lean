/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Heavy.Scales

/-!
# Constants and thresholds of ES22 §6

Constants and thresholds (supplement).

The constants `c₅ = c₅₁`, `β₅`, `N₅ = ⌈log₄ β₅⌉` come from interface with S6 (§5), which
has not landed on this branch.  They enter as the typing data `HeavyEscConsts` (positive `c₅`,
`β₅ > 0`, `N₅` natural); nothing about the escape bound is assumed here.

* `heavyCJ`, `heavyc`, `heavyC6`, `heavyL`, `heavyA`: the explicit constants.
* `HeavyT d n₀ E n`: the conditions (T1)-(T11) at `n`.
* `heavyN6 d n₀ E`: the least `N ≥ max(N₅, n₀+1, 4)` such that `HeavyT` holds for all `n ≥ N`
  (`0` if there is none; the thresholds are finite shows there is one).
-/

@[expose] public section

namespace ElboimSly.Paper

open ElboimSly

/-- Typing data from interface with S6: `c₅ > 0`, `β₅ > 0`, `N₅ ∈ ℕ`. -/
structure HeavyEscConsts where
  c5 : ℝ
  beta5 : ℝ
  N5 : ℕ
  c5_pos : 0 < c5
  beta5_pos : 0 < beta5

/-- `C_J = 4 e^{4d(e-1)}`. -/
noncomputable def heavyCJ (d : ℕ) : ℝ := 4 * Real.exp (4 * d * (Real.exp 1 - 1))

/-- The exponent constant `c_♭ = min{c₅, 1/17, δ³/2, δ²/(2·33^d)}`. -/
noncomputable def heavyc (d : ℕ) (E : HeavyEscConsts) : ℝ :=
  min (min E.c5 (1 / 17)) (min (indDelta d ^ 3 / 2) (indDelta d ^ 2 / (2 * 33 ^ d)))

/-- `c₆ = c_♭ / 2`. -/
noncomputable def heavyC6 (d : ℕ) (E : HeavyEscConsts) : ℝ := heavyc d E / 2

/-- `L_cov = 3^{d+2} n^{γ+9}`. -/
noncomputable def heavyL (d n : ℕ) : ℝ := 3 ^ (d + 2) * (n : ℝ) ^ (escGamma d + 9)

/-- `A_n = 4 C_J 16^{n+1} + 2(n+1) 5^{d(n+1)} + 1`. -/
noncomputable def heavyA (d n : ℕ) : ℝ :=
  4 * heavyCJ d * 16 ^ (n + 1) + 2 * (n + 1) * 5 ^ (d * (n + 1)) + 1

/-- The conditions (T1)-(T11) at the level `n`. -/
structure HeavyT (d n₀ : ℕ) (E : HeavyEscConsts) (n : ℕ) : Prop where
  /-- (T1) -/
  t1 : (n₀ : ℝ) ≤ heavyKappa d n ∧ 16 ≤ heavyLevel d n
  /-- (T2) -/
  t2 : 2 + 20 * Real.logb 2 n ≤ 2 * indDelta d * n ∧ 1 + 2 * indDelta d ≤ 2 * indDelta d * n ∧
    1 < indDelta d * n
  /-- (T3) -/
  t3 : (n : ℝ) ^ 3 * (4 ^ (n + 1) + 1) ≤ 5 ^ n
  /-- (T4) -/
  t4 : 4 ≤ n
  /-- (T5) -/
  t5 : 144 * 4 ^ d * (n : ℝ) ^ (escGamma d + 8 + 20 * d) < (2 : ℝ) ^ (indDelta d * n)
  /-- (T6) -/
  t6 : (n : ℝ) ^ 41 + 3 * n ^ 3 < 2 ^ (heavyLevel d n - 1) ∧ 20 * (n : ℝ) ^ 3 ≤ 2 ^ heavyLevel d n ∧
    5 * (2 : ℝ) ^ (2 * indDelta d * (n + 1)) ≤ 2 ^ (4 * indDelta d * n) ∧
    (2 : ℝ) ^ (2 * indDelta d * (n + 1)) + (n : ℝ) ^ 41 ≤ (1.9 : ℝ) ^ (4 * indDelta d * n - 1)
  /-- (T7) -/
  t7 : (9 * 2 ^ heavyLevel d n : ℝ) ^ (2 * d) * (4 ^ (n + 1) + 1) ^ 2 *
      (3 * Real.exp (-(heavyKappa d n) ^ 2) +
        4 * d * Real.exp (-((heavyLevel d n : ℝ) ^ 4 / 3200))) ≤
        Real.exp (-(indDelta d ^ 2 * n ^ 2)) ∧
    d * (n + 1) * Real.log 5 ≤ indDelta d ^ 2 * n ^ 2 / 2
  /-- (T8) -/
  t8 : (9 * 2 ^ heavyLevel d n : ℝ) ^ (2 * d) * (4 ^ (n + 1) + 1) ^ 2 *
      (3 * Real.exp (-(heavyKappa d n) ^ 3) +
        4 * d * Real.exp (-((heavyLevel d n : ℝ) ^ 4 / 3200))) ≤
        Real.exp (-(indDelta d ^ 3 * n ^ 3)) ∧
    d * (n + 1) * Real.log 5 ≤ indDelta d ^ 3 * n ^ 3 / 2
  /-- (T9) -/
  t9 : 2 + heavyL d n * (3.9 : ℝ) ^ heavyLevel d n ≤
    4 ^ heavyLevel d n / (8 * indDelta d * n * (heavyLevel d n : ℝ) ^ 4)
  /-- (T10) -/
  t10 : 2 * n * (3 * 4 ^ (4 * indDelta d * n + 1) + 4 +
        n * (4 : ℝ) ^ (3 * heavyEps d * (n + 1) / 10)) ≤ (4 : ℝ) ^ (heavyEps d * n / 2) ∧
    2 * n * ((n : ℝ) ^ 3 + 2) ≤ (4 : ℝ) ^ (heavyEps d * n / 2)
  /-- (T11) -/
  t11 : Real.exp (-(n : ℝ) ^ 3) + ((n : ℝ) ^ 3 + 1) * heavyA d n *
      Real.exp (-(heavyc d E * n ^ 3)) ≤ Real.exp (-(heavyC6 d E * n ^ 3))

/-- The threshold `N₆`: the least `N ≥ max(N₅, n₀+1, 4)` such that `HeavyT` holds for all
`n ≥ N`. (`0` if there is no such `N`; see the thresholds are finite.) -/
noncomputable def heavyN6 (d n₀ : ℕ) (E : HeavyEscConsts) : ℕ :=
  sInf {N : ℕ | max (max E.N5 (n₀ + 1)) 4 ≤ N ∧ ∀ n, N ≤ n → HeavyT d n₀ E n}

/-- If the defining set is nonempty, `n ≥ N₆` implies the conditions. -/
theorem HeavyT.of_ge_heavyN6 {d n₀ : ℕ} {E : HeavyEscConsts}
    (hne : {N : ℕ | max (max E.N5 (n₀ + 1)) 4 ≤ N ∧ ∀ n, N ≤ n → HeavyT d n₀ E n}.Nonempty)
    {n : ℕ} (hn : heavyN6 d n₀ E ≤ n) : HeavyT d n₀ E n :=
  (Nat.sInf_mem hne).2 n hn

theorem le_of_ge_heavyN6 {d n₀ : ℕ} {E : HeavyEscConsts}
    (hne : {N : ℕ | max (max E.N5 (n₀ + 1)) 4 ≤ N ∧ ∀ n, N ≤ n → HeavyT d n₀ E n}.Nonempty)
    {n : ℕ} (hn : heavyN6 d n₀ E ≤ n) : max (max E.N5 (n₀ + 1)) 4 ≤ n :=
  (Nat.sInf_mem hne).1.trans hn

end ElboimSly.Paper
