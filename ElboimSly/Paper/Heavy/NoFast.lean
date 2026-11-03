/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Heavy.Lambda

/-!
# A good block cannot be approached fast

A good block cannot be approached fast (ES22 proof of Claim 6.9, ES22 §6, ES22 §6, ES22 §6).

Supporting facts: `latDist` is `1`-Lipschitz, the cyclic integer times are finite on bounded sets and
have gaps at most `1`.
-/

@[expose] public section

open Set
open scoped ENNReal

namespace ElboimSly.Paper

open ElboimSly

variable {d : ℕ}

theorem latDist_le_add {A : Set (Fin d → ℤ)} (hA : A.Nonempty) (u v : Fin d → ℤ) :
    latDist u A ≤ latDist v A + ‖u - v‖ := by
  have : Nonempty A := hA.to_subtype
  have h : latDist u A - ‖u - v‖ ≤ latDist v A := by
    refine le_ciInf fun a => ?_
    have h1 : latDist u A ≤ ‖u - (a : Fin d → ℤ)‖ :=
      ciInf_le ⟨0, fun _ ⟨_, h⟩ => h ▸ norm_nonneg _⟩ a
    have h2 : ‖u - (a : Fin d → ℤ)‖ ≤ ‖u - v‖ + ‖v - (a : Fin d → ℤ)‖ := by
      calc ‖u - (a : Fin d → ℤ)‖ = ‖(u - v) + (v - (a : Fin d → ℤ))‖ := by congr 1; abel
        _ ≤ _ := norm_add_le _ _
    linarith
  linarith

theorem heavyBlock_nonempty (k : ℕ) (ι : Fin d → ℤ) : (heavyBlock k ι).Nonempty := by
  refine ⟨fun c => 2 ^ k * ι c, fun c => ?_⟩
  have hp : (0 : ℤ) < 2 ^ k := by positivity
  exact Int.mul_ediv_cancel_left _ hp.ne'

/-- The cyclic integer times in a bounded interval form a finite set. -/
theorem cycIntTimes_inter_Icc_finite {β : ℝ} (hβ : 0 < β) (T : ℝ) :
    (cycIntTimes β ∩ Icc 0 T).Finite := by
  have hsub : cycIntTimes β ∩ Icc 0 T ⊆
      (fun p : ℕ × ℕ => (p.1 : ℝ) * β + p.2) ''
        ((Finset.range (⌊T / β⌋₊ + 1) ×ˢ Finset.range (⌈β⌉₊ + 1) : Finset (ℕ × ℕ)) : Set (ℕ × ℕ)) := by
    rintro x ⟨⟨hx0, j, hj⟩, -, hxT⟩
    have hℓ0 : 0 ≤ ⌊x / β⌋ := Int.floor_nonneg.2 (by positivity)
    have hj0 : (0 : ℝ) ≤ j := by
      rw [← hj]
      have := Int.floor_le (x / β)
      have h2 : β * (x / β) = x := by field_simp
      nlinarith
    have hjβ : (j : ℝ) < β := by
      rw [← hj]
      have := Int.lt_floor_add_one (x / β)
      have h2 : β * (x / β) = x := by field_simp
      nlinarith
    obtain ⟨ℓ, hℓ⟩ := Int.eq_ofNat_of_zero_le hℓ0
    obtain ⟨j', hj'⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ j by exact_mod_cast hj0)
    refine ⟨(ℓ, j'), ?_, ?_⟩
    · simp only [Finset.coe_product, Finset.coe_range, mem_prod, mem_Iio]
      constructor
      · have : (ℓ : ℝ) ≤ T / β := by
          have h1 : ((⌊x / β⌋ : ℤ) : ℝ) ≤ x / β := Int.floor_le _
          rw [hℓ] at h1
          have h2 : x / β ≤ T / β := by gcongr
          exact_mod_cast h1.trans h2
        have := Nat.le_floor this
        omega
      · have : (j' : ℝ) ≤ ⌈β⌉₊ := by
          have : (j : ℝ) < β := hjβ
          rw [hj'] at this
          exact_mod_cast (this.le.trans (Nat.le_ceil β))
        have : j' ≤ ⌈β⌉₊ := by exact_mod_cast this
        omega
    · simp only
      have e : x = β * ⌊x / β⌋ + j := by rw [← hj]; ring
      rw [e, hℓ, hj']; push_cast; ring
  exact ((Finset.finite_toSet _).image _).subset hsub

end ElboimSly.Paper
