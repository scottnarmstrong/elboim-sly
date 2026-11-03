/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Escape.Es52Incl
public import ElboimSly.Paper.Escape.Es52Resample
public import Mathlib

/-!
# Auxiliary definitions and numerics for ES22 Proposition 5.2

* `escYg`, `escPiG`: the good-guarded versions of `Y_B` and `π_B`; `escPiG ≤ escPi`;
* the numerical consequences of `β ≥ 4^2001` in a setting: `2000 ≤ n`, `ln β ≤ n^40`;
* disjointness of the events `Con_i`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Escape

open ElboimSly ElboimSly.Cyclic ElboimSly.Paper

variable {k : ℕ} {β : ℝ} [Fact (0 < β)]

open Classical in
/-- `Y_B` restricted to good environments. -/
noncomputable def escYg (n : ℕ) (tn : ℝ) (u : Fin (k + 2) → ℤ)
    (ν : Measure (CycS ℕ (k + 2) β)) : ℝ≥0∞ :=
  if CycGood ν then escY n (escJ n) tn (escBlock (escJ n) u) ν else 0

/-- `π_B` with `Y_B` restricted to good environments. -/
noncomputable def escPiG {Ω : Type*} [MeasurableSpace Ω] (Pr : Measure Ω)
    (N : Ω → Measure (CycS ℕ (k + 2) β)) (n : ℕ) (tn : ℝ) (u : Fin (k + 2) → ℤ) (ω : Ω) :
    ℝ≥0∞ :=
  resampleInt (regPlan (k + 2) β) Pr N (escT N tn (escBlock (escJ n) u))
    (fun p => escYg n tn u p.2) ω

omit [Fact (0 < β)] in
theorem escYg_le (n : ℕ) (tn : ℝ) (u : Fin (k + 2) → ℤ) (ν : Measure (CycS ℕ (k + 2) β)) :
    escYg n tn u ν ≤ escY n (escJ n) tn (escBlock (escJ n) u) ν := by
  unfold escYg
  split_ifs
  · exact le_rfl
  · exact zero_le

omit [Fact (0 < β)] in
theorem escPiG_le_escPi {Ω : Type*} [MeasurableSpace Ω] (Pr : Measure Ω)
    (N : Ω → Measure (CycS ℕ (k + 2) β)) (n : ℕ) (tn : ℝ) (u : Fin (k + 2) → ℤ) (ω : Ω) :
    escPiG Pr N n tn u ω ≤ escPi Pr N n (escJ n) tn (escBlock (escJ n) u) ω :=
  lintegral_mono fun _ν => escYg_le n tn u _

omit [Fact (0 < β)] in
theorem escYg_eq_one {n : ℕ} {tn : ℝ} {u : Fin (k + 2) → ℤ} {ν : Measure (CycS ℕ (k + 2) β)}
    (h : ν ∈ escYSet (β := β) tn n u) : escYg n tn u ν = 1 := by
  obtain ⟨hg, h1, h2⟩ := h
  unfold escYg escY
  rw [ite_eq_left hg, ite_eq_left ⟨h1, h2⟩]

/-- Distinct points `p_i` for distinct indices (once `λ_n > 0`). -/
theorem escPoint_injective {n j : ℕ} {u : Fin (k + 2) → ℤ} (hlam : 0 < escLambda n) {i i' : ℕ}
    (h : escPoint n j u i = escPoint n j u i') : i = i' := by
  have h1 := congrFun h (1 : Fin (k + 2))
  simp only [escPoint] at h1
  have h2 : (i * escLambda n : ℤ) = i' * escLambda n := by
    simpa using h1
  have h3 : (i : ℤ) = i' := by
    have : (0 : ℤ) < escLambda n := by exact_mod_cast hlam
    exact mul_right_cancel₀ this.ne' h2
  exact_mod_cast h3

theorem escLambda_pos {n : ℕ} (hn : 2000 ≤ n) : 0 < escLambda n := by
  unfold escLambda
  have : 3 ≤ n ^ 17 := by
    calc 3 ≤ n := by omega
      _ = n ^ 1 := (pow_one n).symm
      _ ≤ n ^ 17 := Nat.pow_le_pow_right (by omega) (by omega)
  omega

/-- In a setting: `ln β ≤ n^40` for `n ≥ 2000`. -/
theorem log_le_pow_forty {n : ℕ} {t₀ β : ℝ} (hn : 2000 ≤ n) (h4 : t₀ ≤ 4)
    (hβ0 : 0 < β) (ht : β < indScale t₀ n) : Real.log β ≤ (n : ℝ) ^ 40 := by
  have h2 : β ≤ (4 : ℝ) ^ (n + 1) := by
    have : (4 : ℝ) ^ n * t₀ ≤ 4 ^ (n + 1) := by rw [pow_succ]; gcongr
    unfold indScale at ht
    linarith
  have h3 : Real.log β ≤ ((n + 1 : ℕ) : ℝ) * Real.log 4 := by
    calc Real.log β ≤ Real.log ((4 : ℝ) ^ (n + 1)) := Real.log_le_log hβ0 h2
      _ = ((n + 1 : ℕ) : ℝ) * Real.log 4 := Real.log_pow _ _
  have h4' : Real.log 4 ≤ 3 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 by norm_num)
    linarith
  have hnR : (2000 : ℝ) ≤ n := by exact_mod_cast hn
  have h5 : ((n + 1 : ℕ) : ℝ) * Real.log 4 ≤ 3 * (n + 1) := by
    push_cast
    have : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
    nlinarith
  have h6 : (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 40 :=
    pow_le_pow_right₀ (by linarith) (by norm_num)
  nlinarith

end ElboimSly.Paper.Escape
