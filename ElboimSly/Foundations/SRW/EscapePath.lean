/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.SRW.EscapeParams
public import ElboimSly.Foundations.SRW.Modulus
public import Mathlib

/-!
# Pathwise analysis of escape from the boundary
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Real

namespace ElboimSly
namespace SRW

theorem mem_Gfrom_regular : ∀ (m k : ℕ) {γ : PathSpace 1}, IsRegularPath γ →
    γ ∈ Gfrom win gamV k (m + 1) →
      γ ∈ gamK k ∧ ∀ i < m, SRW.theta (∑ j ∈ Finset.range (i + 1), win (k + j)) γ ∈ gamK (k + i + 1)
  | 0, k, γ, hγ, h => by
    refine ⟨?_, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
    exact (stop_mem_gamV_iff k hγ).1 h.1
  | m + 1, k, γ, hγ, h => by
    obtain ⟨h1, h2⟩ := h
    have hβ : IsRegularPath (SRW.theta (win k) γ) := hγ.theta _
    obtain ⟨ih1, ih2⟩ := mem_Gfrom_regular m (k + 1) hβ h2
    refine ⟨(stop_mem_gamV_iff k hγ).1 h1, fun i hi => ?_⟩
    rcases i with _ | i
    · simpa using ih1
    · have := ih2 i (by omega)
      rw [theta_theta] at this
      have e : win k + ∑ j ∈ Finset.range (i + 1), win (k + 1 + j) =
          ∑ j ∈ Finset.range (i + 1 + 1), win (k + j) := by
        rw [Finset.sum_range_succ' (fun j => win (k + j)) (i + 1)]
        rw [add_comm]
        simp only [add_zero]
        refine congrArg (· + win k) (Finset.sum_congr rfl fun j _ => ?_)
        rw [show k + 1 + j = k + (j + 1) by omega]
      rw [e] at this
      rw [show k + (i + 1) + 1 = k + 1 + i + 1 by omega]
      exact this

/-- The path-space conditions for the first and the later windows, as explicit inequalities. -/
theorem mem_gamWin_iff (ρ : ℝ≥0) (β : PathSpace 1) :
    β ∈ gamWin ρ ↔ √(ρ : ℝ) / 2 ≤ (β ρ 0 : ℝ) ∧
      ∀ s : ℝ≥0, s ≤ ρ → |(β s 0 : ℝ)| < 9 * √(ρ : ℝ) := Iff.rfl

theorem mem_gam0_iff (β : PathSpace 1) :
    β ∈ gam0 ↔ β 1 0 = 72 ∧ ∀ s : ℝ≥0, s ≤ 1 → 0 ≤ β s 0 ∧ β s 0 ≤ 72 := Iff.rfl

/-- The deterministic induction of the written proof: during and after the first `n` push windows
the path stays in `[0, y + 18 ℓ_n]`, and ends at least at `ℓ_n`. -/
theorem escape_induction {γ : PathSpace 1} {I : ℕ} (h0 : γ ∈ gam0)
    (hW : ∀ j < I, SRW.theta (tau (j + 1)) γ ∈ gamWin (rhoN j)) {y : ℤ} (hy : 0 ≤ y) :
    ∀ n ≤ I, (∀ s : ℝ≥0, s ≤ tau (n + 1) →
        0 ≤ (y : ℝ) + γ s 0 ∧ (y : ℝ) + γ s 0 ≤ y + 18 * ell n) ∧
      ell n ≤ (y : ℝ) + γ (tau (n + 1)) 0
  | 0, _ => by
    rw [mem_gam0_iff] at h0
    have hy' : (0 : ℝ) ≤ y := by exact_mod_cast hy
    refine ⟨fun s hs => ?_, ?_⟩
    · rw [tau_one] at hs
      obtain ⟨a, b⟩ := h0.2 s hs
      have a' : (0 : ℝ) ≤ γ s 0 := by exact_mod_cast a
      have b' : (γ s 0 : ℝ) ≤ 72 := by exact_mod_cast b
      rw [ell_zero]
      constructor <;> linarith
    · rw [tau_one, h0.1, ell_zero]
      push_cast
      linarith
  | n + 1, hn => by
    obtain ⟨ih1, ih2⟩ := escape_induction h0 hW hy n (by omega)
    have hw := (mem_gamWin_iff _ _).1 (hW n (by omega))
    rw [sqrt_rhoN] at hw
    obtain ⟨hw1, hw2⟩ := hw
    have hT : tau (n + 1 + 1) = tau (n + 1) + rhoN n := by
      rw [tau_succ]; rfl
    have hell := ell_succ n
    have hpos := ell_pos n
    have hth : ∀ s : ℝ≥0, (SRW.theta (tau (n + 1)) γ s 0 : ℝ) =
        (γ (tau (n + 1) + s) 0 : ℝ) - γ (tau (n + 1)) 0 := by
      intro s
      simp [SRW.theta]
    have hw1' : ell n / 18 / 2 ≤ (γ (tau (n + 1) + rhoN n) 0 : ℝ) - γ (tau (n + 1)) 0 := by
      rw [← hth]; exact hw1
    have hx := ih2
    have hx2 := (ih1 (tau (n + 1)) le_rfl).2
    refine ⟨fun s hs => ?_, ?_⟩
    · rw [hT] at hs
      rcases le_or_gt s (tau (n + 1)) with h | h
      · obtain ⟨a, b⟩ := ih1 s h
        refine ⟨a, ?_⟩
        have : ell n ≤ ell (n + 1) := ell_mono (Nat.le_succ n)
        linarith
      · have hu : s - tau (n + 1) ≤ rhoN n := by
          rw [tsub_le_iff_left]; exact hs
        have hsu : tau (n + 1) + (s - tau (n + 1)) = s := add_tsub_cancel_of_le h.le
        have := hw2 _ hu
        rw [hth, hsu, abs_lt] at this
        obtain ⟨c1, c2⟩ := this
        constructor <;> nlinarith
    · rw [hT]
      nlinarith

end SRW
end ElboimSly
