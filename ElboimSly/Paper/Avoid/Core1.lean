/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Avoid.Claim2Count
public import ElboimSly.Frozen.Defs.IsRelaxedTimeWrt
public import ElboimSly.Frozen.Defs.IsHeavy
public import Mathlib

/-!
# ES22 §4, Lemma 4.1 (core form): the deterministic part

ES22 Lemma 4.1. For a path `w` on `[a, T]` with `T` relaxed (`R1`, `R2`) and
`x₀ = w(T)`, the set `A_w = {u : ‖u‖ ≥ β^δ/2, d(u + x₀, V) ≤ 1}` (translated to `0`) satisfies the
density bound `|A_w ∩ [-r, r]^d| ≤ r^{8/3}` for `r ≥ L = β^δ/2 ≥ 3^{6d+15}` (`density_of_relaxed`),
and a path `y` that avoids `A_w` and satisfies `‖y(r)‖ ≥ β^δ` for `r ∈ [β^{3δ}, 4ⁿ]` cannot hit the
history (`no_hit`).
-/

@[expose] public section

open Set
open scoped ENNReal NNReal

namespace ElboimSly.Paper

variable {d : ℕ}

/-- The (translated) set `A_w`: points at distance `≥ L` from `0` whose translate by `x₀` is within
distance `1` of the visited set. -/
def histSet (V : Set (Fin d → ℤ)) (x₀ : Fin d → ℤ) (L : ℝ) : Set (Fin d → ℤ) :=
  {u | L ≤ ‖u‖ ∧ ∃ v ∈ V, ‖u + x₀ - v‖ ≤ 1}

/-- The count of lattice points near a finite set. -/
theorem ncard_near_le (V : Set (Fin d → ℤ)) (x₀ : Fin d → ℤ) (r : ℝ) (_hr : 0 ≤ r)
    (S : Set (Fin d → ℤ))
    (hS : ∀ u ∈ S, ‖u‖ ≤ r ∧ ∃ v ∈ V, ‖u + x₀ - v‖ ≤ 1) :
    (S.ncard : ℝ) ≤ 3 ^ d * ((V ∩ {v | ‖v - x₀‖ ≤ r + 1}).ncard : ℝ) := by
  classical
  have hVfin : (V ∩ {v | ‖v - x₀‖ ≤ r + 1}).Finite := by
    refine ((latBox d (⌈‖x₀‖ + r + 1⌉₊)).finite_toSet).subset fun v hv => ?_
    rw [Finset.mem_coe, mem_latBox]
    have h1 : ‖v‖ ≤ ‖v - x₀‖ + ‖x₀‖ := by
      calc ‖v‖ = ‖(v - x₀) + x₀‖ := by rw [sub_add_cancel]
        _ ≤ _ := norm_add_le _ _
    have h2 : ‖v - x₀‖ ≤ r + 1 := hv.2
    exact le_trans (by linarith) (Nat.le_ceil _)
  set Vb := hVfin.toFinset with hVb
  -- S is contained in the union of the unit boxes around the points of `Vb`, shifted by `-x₀`
  have hSfin : S ⊆ ↑(Vb.biUnion fun v => (latBox d 1).image (fun e => v - x₀ + e)) := by
    intro u hu
    obtain ⟨hu1, v, hv, hvu⟩ := hS u hu
    simp only [Finset.coe_biUnion, Finset.coe_image, mem_iUnion, mem_image, Finset.mem_coe]
    refine ⟨v, ?_, u - (v - x₀), ?_, by abel⟩
    · rw [hVb, Set.Finite.mem_toFinset]
      refine ⟨hv, ?_⟩
      show ‖v - x₀‖ ≤ r + 1
      have : ‖v - x₀‖ ≤ ‖u‖ + ‖u + x₀ - v‖ := by
        calc ‖v - x₀‖ = ‖u - (u + x₀ - v)‖ := by congr 1; abel
          _ ≤ _ := norm_sub_le _ _
      linarith
    · rw [mem_latBox]
      have : u - (v - x₀) = u + x₀ - v := by abel
      rw [this]
      exact_mod_cast hvu
  calc (S.ncard : ℝ) ≤ ((Vb.biUnion fun v => (latBox d 1).image (fun e => v - x₀ + e)).card : ℝ) := by
        exact_mod_cast Set.ncard_le_ncard hSfin (Finset.finite_toSet _) |>.trans_eq
          (Set.ncard_coe_finset _)
    _ ≤ (∑ v ∈ Vb, ((latBox d 1).image (fun e => v - x₀ + e)).card : ℕ) := by
        exact_mod_cast Finset.card_biUnion_le
    _ ≤ (∑ v ∈ Vb, (latBox d 1).card : ℕ) := by
        exact_mod_cast Finset.sum_le_sum fun v _ => Finset.card_image_le
    _ = Vb.card * 3 ^ d := by
        rw [Finset.sum_const, card_latBox]; simp
    _ = 3 ^ d * ((V ∩ {v | ‖v - x₀‖ ≤ r + 1}).ncard : ℝ) := by
        rw [hVb, Set.ncard_eq_toFinset_card _ hVfin]; ring

theorem finite_box (x₀ : Fin d → ℤ) (ρ : ℝ) : {v : Fin d → ℤ | ‖v - x₀‖ ≤ ρ}.Finite := by
  refine ((latBox d (⌈‖x₀‖ + ρ⌉₊)).finite_toSet).subset fun v hv => ?_
  rw [Finset.mem_coe, mem_latBox]
  have h1 : ‖v‖ ≤ ‖v - x₀‖ + ‖x₀‖ := by
    calc ‖v‖ = ‖(v - x₀) + x₀‖ := by rw [sub_add_cancel]
      _ ≤ _ := norm_add_le _ _
  have h2 : ‖v - x₀‖ ≤ ρ := hv
  exact le_trans (by linarith) (Nat.le_ceil _)

/-- The density bound (`R1`): if `T` is relaxed, then `A_w` has at most `r^{8/3}` points in
`[-r, r]^d` for `r ≥ L = β^δ/2`, provided `L ≥ 3^{6d+15}`. -/
theorem density_of_relaxed {w : ℝ → Fin d → ℤ} {a T L : ℝ} (hL : (3 : ℝ) ^ (6 * d + 15) ≤ L)
    (hR1 : ∀ ρ : ℝ, 2 * L ≤ ρ → ¬ IsHeavy w a T (w T) ρ) :
    ∀ r : ℝ, L ≤ r →
      ((histSet (visitedSet w a T) (w T) L ∩ {u | ‖u‖ ≤ r}).ncard : ℝ) ≤ r ^ (8 / 3 : ℝ) := by
  intro r hr
  have h3 : (1 : ℝ) ≤ 3 ^ (6 * d + 15) := one_le_pow₀ (by norm_num)
  have hL1 : 1 ≤ L := h3.trans hL
  have hr1 : 1 ≤ r := hL1.trans hr
  have hr0 : 0 < r := by linarith
  set V := visitedSet w a T with hV
  set x₀ := w T with hx₀
  have h1 := ncard_near_le V x₀ r hr0.le (histSet V x₀ L ∩ {u | ‖u‖ ≤ r})
    (fun u hu => ⟨hu.2, hu.1.2⟩)
  set ρ : ℝ := max (r + 1) (2 * L) with hρ
  have hρ2 : ρ ≤ 2 * r := max_le (by linarith) (by linarith)
  have hρ0 : 0 < ρ := lt_of_lt_of_le (by linarith) (le_max_left _ _)
  have hnh := hR1 ρ (le_max_right _ _)
  have hlt : (({v : Fin d → ℤ | ‖v - x₀‖ ≤ ρ} ∩ V).ncard : ℝ) < ρ ^ (5 / 2 : ℝ) := by
    by_contra hcon
    exact hnh ⟨hρ0, not_lt.1 hcon⟩
  have hsub : V ∩ {v | ‖v - x₀‖ ≤ r + 1} ⊆ {v : Fin d → ℤ | ‖v - x₀‖ ≤ ρ} ∩ V := by
    rintro v ⟨hv1, hv2⟩
    refine ⟨?_, hv1⟩
    have : ‖v - x₀‖ ≤ r + 1 := hv2
    exact le_trans this (le_max_left _ _)
  have h4 : ((V ∩ {v | ‖v - x₀‖ ≤ r + 1}).ncard : ℝ) ≤
      (({v : Fin d → ℤ | ‖v - x₀‖ ≤ ρ} ∩ V).ncard : ℝ) := by
    exact_mod_cast Set.ncard_le_ncard hsub ((finite_box x₀ ρ).inter_of_left V)
  have h5 : ρ ^ (5 / 2 : ℝ) ≤ (2 * r) ^ (5 / 2 : ℝ) :=
    Real.rpow_le_rpow hρ0.le hρ2 (by norm_num)
  have h6 : (3 : ℝ) ^ d * 2 ^ (5 / 2 : ℝ) ≤ r ^ (1 / 6 : ℝ) := by
    have e1 : ((3 : ℝ) ^ (6 * d + 15)) ^ (1 / 6 : ℝ) = 3 ^ d * 3 ^ (5 / 2 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
        show ((6 * d + 15 : ℕ) : ℝ) * (1 / 6) = (d : ℝ) + 5 / 2 by push_cast; ring,
        Real.rpow_add (by norm_num), Real.rpow_natCast]
    calc (3 : ℝ) ^ d * 2 ^ (5 / 2 : ℝ) ≤ 3 ^ d * 3 ^ (5 / 2 : ℝ) := by
          gcongr
          · norm_num
        _ = ((3 : ℝ) ^ (6 * d + 15)) ^ (1 / 6 : ℝ) := e1.symm
        _ ≤ r ^ (1 / 6 : ℝ) := Real.rpow_le_rpow (by positivity) (hL.trans hr) (by norm_num)
  have h7 : r ^ (8 / 3 : ℝ) = r ^ (5 / 2 : ℝ) * r ^ (1 / 6 : ℝ) := by
    rw [← Real.rpow_add hr0]; norm_num
  calc _ ≤ 3 ^ d * ((V ∩ {v | ‖v - x₀‖ ≤ r + 1}).ncard : ℝ) := h1
    _ ≤ 3 ^ d * ρ ^ (5 / 2 : ℝ) := by gcongr; exact h4.trans hlt.le
    _ ≤ 3 ^ d * (2 * r) ^ (5 / 2 : ℝ) := by gcongr
    _ = (3 ^ d * 2 ^ (5 / 2 : ℝ)) * r ^ (5 / 2 : ℝ) := by
        rw [Real.mul_rpow (by norm_num) hr0.le]; ring
    _ ≤ r ^ (1 / 6 : ℝ) * r ^ (5 / 2 : ℝ) := by gcongr
    _ = r ^ (8 / 3 : ℝ) := by rw [h7]; ring

end ElboimSly.Paper

end
