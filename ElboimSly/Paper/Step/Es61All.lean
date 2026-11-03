/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Step.Cor72Interface
public import ElboimSly.Paper.Heavy.EscInterfaceAll
public import Mathlib

/-!
# `StepEs61` from `HeavyEscInterfaceAll`

ES22 Theorem 6.1, with `c₅ = c₅(d)` and `β₅ = β₅(d, n₀)`: at base level `n₁` only the
interface for `E n₁` at `n₀ = n₁` is used.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Step

open ElboimSly ElboimSly.Paper ElboimSly.Cyclic ElboimSly.Paper.Heavy

theorem heavyC6_eq_of_c5 {d : ℕ} {E E' : HeavyEscConsts} (h : E.c5 = E'.c5) :
    heavyC6 d E = heavyC6 d E' := by
  unfold heavyC6 heavyc; rw [h]

theorem stepEs61Env_of_interfaceAll {d : ℕ} (hd : 5 ≤ d) {E : ℕ → HeavyEscConsts}
    (hI : HeavyEscInterfaceAll d E) :
    StepEs61Env d (heavyC6 d (E 0)) (fun n₁ => stepBeta6 d (E n₁) n₁) := by
  intro n₁ h8 β _ n t₀ hβ hR Ω _ Pe N hN
  obtain ⟨-, hβ1, -, ht, hlt, hind⟩ := hR
  have hc6 : heavyC6 d (E n₁) = heavyC6 d (E 0) := heavyC6_eq_of_c5 (hI.1 n₁)
  set M := max (heavyN6 d n₁ (E n₁)) n₁ with hM
  have hb1 : (4 : ℝ) ^ (M + 1) ≤ β := le_trans (le_max_right _ _) hβ
  have hb2 : (10 : ℝ) ^ 14 ≤ β := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hβ
  have hb3 : (E n₁).beta5 ≤ β := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hβ
  have hnM : M < n := by
    by_contra h
    push Not at h
    have : indScale t₀ n ≤ (4 : ℝ) ^ (M + 1) := by
      unfold indScale
      have h1 : (4 : ℝ) ^ n * t₀ ≤ 4 * (4 : ℝ) ^ n := by
        nlinarith [ht.2, pow_pos (by norm_num : (0 : ℝ) < 4) n]
      have h2 : (4 : ℝ) ^ n ≤ 4 ^ M := pow_le_pow_right₀ (by norm_num) h
      calc _ ≤ 4 * (4 : ℝ) ^ n := h1
        _ ≤ 4 * 4 ^ M := by linarith
        _ = _ := by ring
    linarith
  have hp : Es4Params d β n₁ n t₀ :=
    ⟨hd, h8, lt_of_le_of_lt (le_max_right _ _) hnM, hb2, ht.1, ht.2, hlt,
      fun n' h1 h2 t' h3 h4 => hind n' h1 h2 t' ⟨h3, h4⟩⟩
  have hT : HeavyT d n₁ (E n₁) n :=
    HeavyT.of_ge_N6 (by omega) (le_of_lt (lt_of_le_of_lt (le_max_left _ _) hnM))
  rw [← hc6]
  exact es6_one_of_params (hI.2 n₁ β n t₀) hN hp hT hb3

/-- `StepEs61` from the interface with the written proof's constant dependence. -/
theorem stepEs61_of_interfaceAll {d : ℕ} (hd : 5 ≤ d) {E : ℕ → HeavyEscConsts}
    (hI : HeavyEscInterfaceAll d E) :
    StepEs61 d (heavyC6 d (E 0)) (fun n₁ => stepBeta6 d (E n₁) n₁) :=
  stepEs61_of_envEs61 (stepEs61Env_of_interfaceAll hd hI)

end ElboimSly.Paper.Step

end
