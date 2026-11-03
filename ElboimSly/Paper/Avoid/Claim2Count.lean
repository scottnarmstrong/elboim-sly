/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Avoid.Hyp
public import ElboimSly.Paper.Avoid.Claim2Series
public import Mathlib

/-!
# ES22 §4, Claim 4.2: counting lattice points near a sparse set, and levels

ES22 Claim 4.2, window `ℓ`, integer times. The set `N(A, r)` of lattice points within
sup-distance `< r` of `A`, intersected with a box, has at most `(2r+1)^d |A ∩ larger box|` points.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Paper

variable {d : ℕ}

/-- The finite set of lattice points of the box `[-m, m]^d`. -/
noncomputable def latBox (d : ℕ) (m : ℕ) : Finset (Fin d → ℤ) :=
  Fintype.piFinset fun _ => Finset.Icc (-(m : ℤ)) m

theorem mem_latBox {m : ℕ} {u : Fin d → ℤ} : u ∈ latBox d m ↔ ‖u‖ ≤ (m : ℝ) := by
  unfold latBox
  rw [Fintype.mem_piFinset, pi_norm_le_iff_of_nonneg (by positivity)]
  refine forall_congr' fun i => ?_
  rw [Finset.mem_Icc, Int.norm_eq_abs, abs_le]
  norm_cast

theorem card_latBox (m : ℕ) : (latBox d m).card = (2 * m + 1) ^ d := by
  unfold latBox
  rw [Fintype.card_piFinset]
  simp only [Int.card_Icc, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  congr 1
  omega

/-- The lattice points of the box `[-m, m]^d` within distance `< r` of a point of `A`. -/
noncomputable def nearSet (A : Set (Fin d → ℤ)) (m : ℕ) (r : ℝ) : Finset (Fin d → ℤ) :=
  open scoped Classical in
  (latBox d m).filter fun u => ∃ a ∈ A, ‖u - a‖ < r

open scoped Classical in
theorem mem_nearSet {A : Set (Fin d → ℤ)} {m : ℕ} {r : ℝ} {u : Fin d → ℤ} :
    u ∈ nearSet A m r ↔ ‖u‖ ≤ (m : ℝ) ∧ ∃ a ∈ A, ‖u - a‖ < r := by
  unfold nearSet
  rw [Finset.mem_filter, mem_latBox]

open scoped Classical in
/-- `|N(A, r) ∩ [-m,m]^d| ≤ (2⌈r⌉+1)^d |A ∩ [-(m+⌈r⌉), m+⌈r⌉]^d|`. -/
theorem card_nearSet_le (A : Set (Fin d → ℤ)) (m : ℕ) (r : ℝ) (_hr : 0 ≤ r) :
    ((nearSet A m r).card : ℝ) ≤ (2 * (⌈r⌉₊ : ℝ) + 1) ^ d *
      ((A ∩ {u | ‖u‖ ≤ ((m + ⌈r⌉₊ : ℕ) : ℝ)}).ncard : ℝ) := by
  set k := ⌈r⌉₊ with hk
  have hfin : (A ∩ {u : Fin d → ℤ | ‖u‖ ≤ ((m + k : ℕ) : ℝ)}).Finite :=
    (Finset.finite_toSet (latBox d (m + k))).subset fun u hu => by
      simpa [mem_latBox] using hu.2
  set S := hfin.toFinset with hS
  have hsub : nearSet A m r ⊆ S.biUnion fun a => (latBox d k).image (fun v => a + v) := by
    intro u hu
    unfold nearSet at hu
    rw [Finset.mem_filter] at hu
    obtain ⟨hu1, a, haA, hua⟩ := hu
    rw [Finset.mem_biUnion]
    have hum : ‖u‖ ≤ (m : ℝ) := mem_latBox.1 hu1
    have hk' : r ≤ k := Nat.le_ceil r
    refine ⟨a, ?_, ?_⟩
    · rw [hS, Set.Finite.mem_toFinset]
      refine ⟨haA, ?_⟩
      show ‖a‖ ≤ _
      have : ‖a‖ ≤ ‖u‖ + ‖u - a‖ := by
        calc ‖a‖ = ‖u - (u - a)‖ := by rw [sub_sub_cancel]
          _ ≤ ‖u‖ + ‖u - a‖ := norm_sub_le _ _
      push_cast
      linarith
    · rw [Finset.mem_image]
      refine ⟨u - a, mem_latBox.2 ?_, by abel⟩
      linarith
  calc ((nearSet A m r).card : ℝ) ≤ ((S.biUnion fun a => (latBox d k).image
          (fun v => a + v)).card : ℝ) := by exact_mod_cast Finset.card_le_card hsub
    _ ≤ (∑ a ∈ S, ((latBox d k).image (fun v => a + v)).card : ℕ) := by
        exact_mod_cast Finset.card_biUnion_le
    _ ≤ (∑ a ∈ S, (latBox d k).card : ℕ) := by
        exact_mod_cast Finset.sum_le_sum fun a _ => Finset.card_image_le
    _ = S.card * (2 * k + 1) ^ d := by
        rw [Finset.sum_const, card_latBox]; simp
    _ = (2 * (k : ℝ) + 1) ^ d * ((A ∩ {u | ‖u‖ ≤ ((m + k : ℕ) : ℝ)}).ncard : ℝ) := by
        rw [hS, Set.ncard_eq_toFinset_card _ hfin]; push_cast; ring

theorem avoidLevel_pow (ℓ : ℕ) (hℓ : 1 ≤ ℓ) : avoidLevel ((4 : ℝ) ^ ℓ) = ℓ - 1 := by
  have h1 : 1 < (4 : ℝ) ^ ℓ := one_lt_pow₀ (by norm_num) (by omega)
  obtain ⟨h2, h3⟩ := avoidLevel_spec h1
  have a : avoidLevel ((4 : ℝ) ^ ℓ) < ℓ := (pow_lt_pow_iff_right₀ (by norm_num)).1 h2
  have b : ℓ ≤ avoidLevel ((4 : ℝ) ^ ℓ) + 1 := (pow_le_pow_iff_right₀ (by norm_num)).1 h3
  omega

theorem sq_pred_le_two_pow (ℓ : ℕ) : (((ℓ : ℝ) - 1) ^ 2) ≤ 2 ^ ℓ ∨ ℓ = 0 := by
  rcases Nat.eq_zero_or_pos ℓ with rfl | h
  · right; rfl
  left
  obtain ⟨m, rfl⟩ : ∃ m, ℓ = m + 1 := ⟨ℓ - 1, by omega⟩
  push_cast
  simp only [add_sub_cancel_right]
  have : ∀ m : ℕ, ((m : ℝ)) ^ 2 ≤ 2 ^ (m + 1) := by
    intro m
    induction m with
    | zero => norm_num
    | succ k ih =>
      rcases Nat.lt_or_ge k 3 with hk | hk
      · interval_cases k <;> norm_num
      · have : (k : ℝ) ≥ 3 := by exact_mod_cast hk
        push_cast
        calc ((k : ℝ) + 1) ^ 2 ≤ 2 * (k : ℝ) ^ 2 := by nlinarith
          _ ≤ 2 * 2 ^ (k + 1) := by linarith
          _ = 2 ^ (k + 1 + 1) := by ring
  exact this m

end ElboimSly.Paper

end
