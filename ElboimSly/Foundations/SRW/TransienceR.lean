/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.SRW.HitThm
public import Mathlib

/-!
# The radius `R_d` of the transience estimate

Transience: escape from the unit box.
-/

@[expose] public section

open Set Filter Topology
open scoped NNReal Real

namespace ElboimSly
namespace SRW

/-- The condition defining `R_d`. -/
def escCond (d R : ℕ) : Prop :=
  2 ≤ R ∧ 4 * (d : ℝ) * Real.exp (-(√(R : ℝ) / 32)) +
    Chit d * (R : ℝ) ^ (-(3 * ((d : ℝ) - 2) / 4)) ≤ 1 / 2

theorem exists_escR {d : ℕ} (hd : 3 ≤ d) : ∃ R, escCond d R := by
  have hc : 0 < 3 * ((d : ℝ) - 2) / 4 := by
    have : (3 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have h1 : Tendsto (fun R : ℕ => 4 * (d : ℝ) * Real.exp (-(√(R : ℝ) / 32))) atTop (𝓝 0) := by
    have h0 : Tendsto (fun R : ℕ => √(R : ℝ) / 32) atTop atTop :=
      (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).atTop_div_const (by norm_num)
    have := Real.tendsto_exp_neg_atTop_nhds_zero.comp h0
    simpa using this.const_mul (4 * (d : ℝ))
  have h2 : Tendsto (fun R : ℕ => Chit d * (R : ℝ) ^ (-(3 * ((d : ℝ) - 2) / 4))) atTop (𝓝 0) := by
    have := (tendsto_rpow_neg_atTop hc).comp tendsto_natCast_atTop_atTop
    simpa using this.const_mul (Chit d)
  have e1 := (tendsto_order.1 h1).2 (1 / 4) (by norm_num)
  have e2 := (tendsto_order.1 h2).2 (1 / 4) (by norm_num)
  obtain ⟨R, hR1, hR2, hR3⟩ := (e1.and (e2.and (eventually_ge_atTop 2))).exists
  exact ⟨R, hR3, by linarith⟩

/-- The least `R ≥ 2` satisfying the condition (Transience: escape from the unit box). -/
noncomputable def escR (d : ℕ) : ℕ :=
  open Classical in if h : ∃ R, escCond d R then Nat.find h else 0

theorem escR_spec {d : ℕ} (hd : 3 ≤ d) : escCond d (escR d) := by
  classical
  have h := exists_escR hd
  unfold escR
  rw [dite_eq_left h]
  exact Nat.find_spec h

end SRW
end ElboimSly
