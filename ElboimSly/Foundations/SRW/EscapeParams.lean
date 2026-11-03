/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.SRW.EscapeSets
public import Mathlib

/-!
# Parameters and path analysis of escape from the boundary
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Real

namespace ElboimSly
namespace SRW

/-- `ℓ_i = 72 (37/36)^i`. -/
noncomputable def ell (i : ℕ) : ℝ := 72 * (37 / 36 : ℝ) ^ i

/-- The window lengths `ρ_{i+1} = (ℓ_i / 18)^2`. -/
noncomputable def rhoN (i : ℕ) : ℝ≥0 := Real.toNNReal ((ell i / 18) ^ 2)

/-- Window `k` has length `win k`: window `0` is the unit window of `E_0`. -/
noncomputable def win : ℕ → ℝ≥0
  | 0 => 1
  | k + 1 => rhoN k

/-- The start times of the windows. -/
noncomputable def tau (n : ℕ) : ℝ≥0 := ∑ i ∈ Finset.range n, win i

theorem tau_succ (n : ℕ) : tau (n + 1) = tau n + win n := by
  simp [tau, Finset.sum_range_succ]

theorem tau_one : tau 1 = 1 := by simp [tau, win]

theorem ell_pos (i : ℕ) : 0 < ell i := by unfold ell; positivity

theorem ell_succ (i : ℕ) : ell (i + 1) = 37 / 36 * ell i := by
  unfold ell; rw [pow_succ]; ring

theorem ell_zero : ell 0 = 72 := by simp [ell]

theorem ell_mono {i j : ℕ} (h : i ≤ j) : ell i ≤ ell j := by
  unfold ell
  gcongr
  norm_num

theorem coe_rhoN (i : ℕ) : (rhoN i : ℝ) = (ell i / 18) ^ 2 := by
  unfold rhoN
  rw [Real.coe_toNNReal _ (by positivity)]

theorem sqrt_rhoN (i : ℕ) : √(rhoN i : ℝ) = ell i / 18 := by
  rw [coe_rhoN, Real.sqrt_sq (by have := ell_pos i; positivity)]

theorem rhoN_ge (i : ℕ) : 16 ≤ (rhoN i : ℝ) := by
  rw [coe_rhoN]
  have : 4 ≤ ell i / 18 := by
    have := ell_mono (Nat.zero_le i)
    rw [ell_zero] at this
    linarith
  nlinarith

theorem coe_tau_succ (n : ℕ) : (tau (n + 1) : ℝ) = 1 + ∑ i ∈ Finset.range n, (ell i / 18) ^ 2 := by
  induction n with
  | zero => simp [tau_one]
  | succ n ih =>
    rw [tau_succ, NNReal.coe_add, ih, Finset.sum_range_succ]
    show _ + (rhoN n : ℝ) = _
    rw [coe_rhoN]; ring

/-- Window membership: `θ_a γ` lies in the `i`-th event. -/
def gamK : ℕ → Set (PathSpace 1)
  | 0 => gam0
  | k + 1 => gamWin (rhoN k)

theorem evalForall_stop {d : ℕ} (K₁ K₂ : Set (Fin d → ℤ)) (r : ℝ≥0) (β : PathSpace d) :
    stopPath r β ∈ evalForall K₁ K₂ r ↔ β ∈ evalForall K₁ K₂ r := by
  simp only [evalForall, stopPath, mem_ofPred_eq, min_self]
  refine and_congr Iff.rfl (forall₂_congr fun s hs => ?_)
  rw [min_eq_left hs]

theorem gamK_stop (k : ℕ) (β : PathSpace 1) : stopPath (win k) β ∈ gamK k ↔ β ∈ gamK k := by
  cases k with
  | zero => exact evalForall_stop _ _ _ β
  | succ k => exact evalForall_stop _ _ _ β

theorem isRegSet_gamK (k : ℕ) : IsRegSet (gamK k) := by
  cases k with
  | zero => exact isRegSet_evalForall _ _ _
  | succ k => exact isRegSet_evalForall _ _ _

/-- Chosen measurable versions. -/
noncomputable def gamV (k : ℕ) : Set (PathSpace 1) := (isRegSet_gamK k).choose

theorem measurableSet_gamV (k : ℕ) : MeasurableSet (gamV k) := (isRegSet_gamK k).choose_spec.1

theorem gamV_spec (k : ℕ) {β : PathSpace 1} (hβ : IsRegularPath β) : β ∈ gamK k ↔ β ∈ gamV k :=
  (isRegSet_gamK k).choose_spec.2 β hβ

theorem stop_mem_gamV_iff (k : ℕ) {β : PathSpace 1} (hβ : IsRegularPath β) :
    stopPath (win k) β ∈ gamV k ↔ β ∈ gamK k := by
  have hs : IsRegularPath (stopPath (win k) β) := hβ.stop _
  rw [← gamV_spec k hs, gamK_stop]

theorem theta_theta {d : ℕ} (a b : ℝ≥0) (γ : PathSpace d) :
    theta a (theta b γ) = theta (b + a) γ := by
  funext s
  simp only [theta]
  rw [show b + (a + s) = b + a + s by ring]
  abel

end SRW
end ElboimSly
