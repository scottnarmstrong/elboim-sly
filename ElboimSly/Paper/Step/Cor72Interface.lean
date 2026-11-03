/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Step.Es61Transfer
public import ElboimSly.Paper.Step.Cor72Final
public import Mathlib

/-!
# Lemma 7.1 and Corollary 7.2, conditional only on the interface of §5

ES22 Lemma 7.1; ES22 Corollary 7.2; ES22 Theorem 6.1.

The only residual hypothesis is `HeavyEscInterface` (the conclusion of interface with S6,
a §5 result), for the constants `E`:

* `stepEs61_of_interface`: `StepEs61 d (c₆) (β₆)` for `c₆ = heavyC6 d E`;
* `stepLem71_of_interface`: Lemma 7.1;
* `stepCor72_of_interface`: Corollary 7.2.
-/

@[expose] public section

namespace ElboimSly.Paper.Step

open ElboimSly ElboimSly.Paper ElboimSly.Paper.Heavy

theorem heavyC6_pos {d : ℕ} (hd : 1 ≤ d) (E : HeavyEscConsts) : 0 < heavyC6 d E := by
  have h := indDelta_pos' hd
  unfold heavyC6 heavyc
  have : 0 < min (min E.c5 (1 / 17)) (min (indDelta d ^ 3 / 2) (indDelta d ^ 2 / (2 * 33 ^ d))) :=
    lt_min (lt_min E.c5_pos (by norm_num)) (lt_min (by positivity) (by positivity))
  linarith

theorem stepEs61_of_interface {d : ℕ} (hd : 5 ≤ d) (E : HeavyEscConsts)
    (hI : ∀ (β : ℝ) [Fact (0 < β)] (n₀ n : ℕ) (t₀ : ℝ), HeavyEscInterface d β E n₀ n t₀) :
    StepEs61 d (heavyC6 d E) (stepBeta6 d E) :=
  stepEs61_of_envEs61 (stepEs61Env_of_interface hd E hI)

theorem stepLem71_of_interface {d : ℕ} (hd : 5 ≤ d) (E : HeavyEscConsts)
    (hI : ∀ (β : ℝ) [Fact (0 < β)] (n₀ n : ℕ) (t₀ : ℝ), HeavyEscInterface d β E n₀ n t₀) :
    ∃ c : ℝ, 0 < c ∧ ∃ βCat : ℕ → ℝ, StepLem71 d c βCat :=
  stepLem71_of_es61 hd (heavyC6_pos (by omega) E) (stepEs61_of_interface hd E hI)

theorem stepCor72_of_interface {d : ℕ} (hd : 5 ≤ d) (E : HeavyEscConsts)
    (hI : ∀ (β : ℝ) [Fact (0 < β)] (n₀ n : ℕ) (t₀ : ℝ), HeavyEscInterface d β E n₀ n t₀) :
    ∃ c : ℝ, 0 < c ∧ ∃ βCat : ℕ → ℝ, StepCor72 d c βCat :=
  stepCor72_of_es61 hd (heavyC6_pos (by omega) E) (stepEs61_of_interface hd E hI)

end ElboimSly.Paper.Step

end
