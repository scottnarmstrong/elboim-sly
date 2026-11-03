/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import Mathlib

/-!
# (H1) at the base: lattice point counts

ES22 Lemma 8.1, Step 2 and the count of F47.

* `latR`: the embedding `ℤ^d → ℝ^d`; `norm_latR_sub`: it is an isometry for the sup norm.
* `latNear y ρ`: a box of integer points containing the lattice points within `ρ` of `y`, with
  `card ≤ (2ρ+3)^d`.
* `ballBox R`: a box containing the lattice points of sup norm `< R`, with `card ≤ (2R+1)^d`.
-/

@[expose] public section

open Set

namespace ElboimSly.Paper

variable {d : ℕ}

/-- The lattice point as a point of `ℝ^d`. -/
def latR (z : Fin d → ℤ) : Fin d → ℝ := fun k => (z k : ℝ)

theorem latR_sub (z z' : Fin d → ℤ) : latR z - latR z' = latR (z - z') := by
  funext k; simp [latR]

theorem norm_latR (z : Fin d → ℤ) : ‖latR z‖ = ‖z‖ := by
  refine le_antisymm ?_ ?_
  · refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun k => ?_
    have := norm_le_pi_norm z k
    simpa [latR, Int.norm_eq_abs] using this
  · refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun k => ?_
    have := norm_le_pi_norm (latR z) k
    simpa [latR, Int.norm_eq_abs] using this

theorem norm_latR_sub (z z' : Fin d → ℤ) : ‖latR z - latR z'‖ = ‖z - z'‖ := by
  rw [latR_sub, norm_latR]

/-- Integer box around `y` of half-width `ρ`. -/
noncomputable def latNear (y : Fin d → ℝ) (ρ : ℝ) : Finset (Fin d → ℤ) :=
  Fintype.piFinset fun k => Finset.Icc ⌊y k - ρ⌋ ⌈y k + ρ⌉

theorem mem_latNear {y : Fin d → ℝ} {ρ : ℝ} {z : Fin d → ℤ} (h : ‖latR z - y‖ < ρ) :
    z ∈ latNear y ρ := by
  rw [latNear, Fintype.mem_piFinset]
  intro k
  have h1 : |(z k : ℝ) - y k| < ρ := by
    have := norm_le_pi_norm (latR z - y) k
    rw [Real.norm_eq_abs] at this
    simpa [latR] using lt_of_le_of_lt this h
  rw [abs_lt] at h1
  rw [Finset.mem_Icc]
  exact ⟨Int.floor_le_iff.2 (by linarith), Int.le_ceil_iff.2 (by linarith)⟩

theorem card_latNear (y : Fin d → ℝ) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    ((latNear y ρ).card : ℝ) ≤ (2 * ρ + 3) ^ d := by
  rw [latNear, Fintype.card_piFinset, Nat.cast_prod]
  calc ∏ k : Fin d, (((Finset.Icc ⌊y k - ρ⌋ ⌈y k + ρ⌉).card : ℕ) : ℝ)
      ≤ ∏ _k : Fin d, (2 * ρ + 3) := by
        refine Finset.prod_le_prod₀ (fun _ _ => by positivity) fun k _ => ?_
        rw [Int.card_Icc]
        have h1 : (⌈y k + ρ⌉ : ℝ) < y k + ρ + 1 := Int.ceil_lt_add_one _
        have h2 : (y k - ρ - 1 : ℝ) < ⌊y k - ρ⌋ := by
          have := Int.lt_floor_add_one (y k - ρ); linarith
        rcases le_or_gt 0 (⌈y k + ρ⌉ + 1 - ⌊y k - ρ⌋) with h | h
        · rw [← Int.cast_natCast, Int.toNat_of_nonneg h]
          push_cast
          linarith
        · rw [Int.toNat_of_nonpos h.le]
          simp only [Nat.cast_zero]
          positivity
    _ = (2 * ρ + 3) ^ d := by simp

/-- Integer box of sup radius `⌈R⌉ - 1`. -/
noncomputable def ballBox (d : ℕ) (R : ℝ) : Finset (Fin d → ℤ) :=
  Fintype.piFinset fun _ => Finset.Icc (-(⌈R⌉ - 1)) (⌈R⌉ - 1)

theorem mem_ballBox {R : ℝ} {z : Fin d → ℤ} (h : ‖z‖ < R) : z ∈ ballBox d R := by
  rw [ballBox, Fintype.mem_piFinset]
  intro k
  have h1 : |(z k : ℝ)| < R := by
    have := norm_le_pi_norm z k
    rw [Int.norm_eq_abs] at this
    exact lt_of_le_of_lt this h
  rw [abs_lt] at h1
  rw [Finset.mem_Icc]
  have a : z k < ⌈R⌉ := by
    have : (z k : ℝ) < ⌈R⌉ := lt_of_lt_of_le h1.2 (Int.le_ceil R)
    exact_mod_cast this
  have b : -(⌈R⌉) < z k := by
    have : -(⌈R⌉ : ℝ) < z k := by linarith [Int.le_ceil R]
    exact_mod_cast this
  omega

theorem card_ballBox (d : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    ((ballBox d R).card : ℝ) ≤ (2 * R + 1) ^ d := by
  rw [ballBox, Fintype.card_piFinset, Nat.cast_prod]
  calc ∏ _k : Fin d, (((Finset.Icc (-(⌈R⌉ - 1)) (⌈R⌉ - 1)).card : ℕ) : ℝ)
      ≤ ∏ _k : Fin d, (2 * R + 1) := by
        refine Finset.prod_le_prod₀ (fun _ _ => by positivity) fun k _ => ?_
        rw [Int.card_Icc]
        have h1 : (⌈R⌉ : ℝ) < R + 1 := Int.ceil_lt_add_one _
        rcases le_or_gt 0 (⌈R⌉ - 1 + 1 - -(⌈R⌉ - 1)) with h | h
        · rw [← Int.cast_natCast, Int.toNat_of_nonneg h]
          push_cast
          linarith
        · rw [Int.toNat_of_nonpos h.le]
          simp only [Nat.cast_zero]
          positivity
    _ = (2 * R + 1) ^ d := by simp

end ElboimSly.Paper

end
