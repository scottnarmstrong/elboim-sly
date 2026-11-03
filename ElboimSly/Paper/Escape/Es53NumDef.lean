/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Escape.Es53Transfer
public import Mathlib

/-!
# The numerical thresholds of ES22 Lemma 5.3

ES22 Lemma 5.3, "Thresholds".  `Es53Num` collects the inequalities between the scales
`β, n, j, m₁` used in the proof; they all hold for `β ≥ β_{53}(d, n₀)` (`es53_num`, in `Es53Num`).
The last field says that the total error is at most `c_line / 2`.
-/

@[expose] public section

open scoped NNReal ENNReal

namespace ElboimSly.Paper.Escape

open ElboimSly ElboimSly.Paper ElboimSly.Brownian

/-- The inequalities between the scales in the proof of ES22 Lemma 5.3. -/
structure Es53Num (k n₀ n m₁ nD : ℕ) (β : ℝ) (CB CB' CC CD cD : ℝ) : Prop where
  hm8 : 8 ≤ m₁
  hm₁ : n₀ + 1 ≤ m₁
  hm1n : m₁ ≤ n
  hm1a : (m₁ : ℝ) ≤ Real.log (Real.log β)
  hm1b : (4 : ℝ) ^ m₁ ≤ Real.log β
  hβ : Real.exp 2 ≤ Real.log β
  hn2 : 2 ≤ n
  hn53 : n53 (k + 2) ≤ n
  hnD : nD ≤ n
  hlb : Real.log β ≤ (n : ℝ) ^ 17 / 7
  hj1 : (n : ℝ) ^ 20 ≤ 2 ^ escJ n
  hj1' : (2 : ℝ) ^ escJ n < 2 * (n : ℝ) ^ 20
  hj2 : 2 ≤ escJ n
  hIn : escIstar n (escJ n) ≤ n ^ 3
  hIlam : 16 * (escIstar n (escJ n) * escLambda n) ≤ 3 * 2 ^ escJ n
  hT1 : (4 : ℝ) ^ (n₀ + 1) ≤ (escJ n : ℝ) * 4 ^ escJ n
  hT2 : (escJ n : ℝ) * 4 ^ escJ n ≤ 4 ^ n
  hε1 : ((escJ n : ℝ) * 4 ^ escJ n) ^ indThetaH ≤ (n : ℝ) ^ 17 / 30
  hε2 : ((escJ n : ℝ) * 4 ^ escJ n) ^ indThetaH ≤ 3 * (2 : ℝ) ^ escJ n / 40
  hθB : ∀ m : ℕ, 1 ≤ m → ((4 : ℝ) ^ m) ^ indThetaH ≤ 2 ^ (m + 3) / m
  hθB' : ((escJ n : ℝ) * 4 ^ escJ n) ^ indThetaH ≤ 2 ^ escJ n
  hL1 : (4 : ℝ) ^ (n₀ + 1) ≤ (n : ℝ) ^ 17 / 7
  hL2 : (n : ℝ) ^ 17 / 7 ≤ 4 ^ n
  hL3 : (n : ℝ) ^ 17 / 7 ≤ (n : ℝ) ^ 17 / 6 - 2
  herr : ENNReal.ofReal (cline (k + 2) / 2) ≤ ENNReal.ofReal (cline (k + 2)) -
      ENNReal.ofReal (Real.exp (-((avoidLevel ((escJ n : ℝ) * 4 ^ escJ n) : ℕ) : ℝ) ^ 2)) -
      errB CB k m₁ n -
      ENNReal.ofReal (CB' * ((2 : ℝ) ^ escJ n) ^ k *
        ((escJ n : ℝ) * 4 ^ escJ n) ^ (-(k : ℝ) / 2)) -
      ENNReal.ofReal (CC * ((n : ℝ) ^ 17 / 7) ^ (-(1 : ℝ) / 30)) - errD CD cD m₁ n

end ElboimSly.Paper.Escape
