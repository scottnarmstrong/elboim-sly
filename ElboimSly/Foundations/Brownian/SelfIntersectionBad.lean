/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Brownian.SelfIntersectionGlobal
public import ElboimSly.Foundations.Brownian.SelfIntersectionNum
public import ElboimSly.Foundations.Brownian.SelfIntersectionAsymp

import Mathlib

/-!
# The failure bounds are `O(e^{-t^{ζ²/4}})`

ES22 Claim 9.4, Step 5.

Every error term of Steps 3 and 4 has the form `poly(t) e^{-c' t^{e'}}` with `e' ≥ ζ²/2`, so is
bounded by a constant times `e^{-t^{ζ²/4}}`, uniformly in `t ≥ 1`.
-/

@[expose] public section

open Filter Topology Set
open scoped NNReal ENNReal

namespace ElboimSly.Brownian

section Facts

variable {ζ t : ℝ}

lemma siRho_sq (ht : 1 ≤ t) : siRho ζ t ^ 2 = t ^ (ζ / 50) := by
  unfold siRho siR
  rw [rpow_sq' (Real.rpow_nonneg (by linarith) _), ← Real.rpow_mul (by linarith)]
  congr 1; ring

lemma siM_div (ht : 1 ≤ t) : siM ζ t / (3 * siBig ζ t) ^ 2 = t ^ (ζ ^ 2 / 2) / 9 := by
  have hr : 0 < siR ζ t := Real.rpow_pos_of_pos (by linarith) _
  unfold siM siBig
  rw [mul_pow, rpow_sq' hr.le, show (3 : ℝ) ^ 2 = 9 by norm_num,
    show 2 * (1 + ζ) = (2 + 3 * ζ) - ζ by ring, Real.rpow_sub hr]
  have : siR ζ t ^ ζ = t ^ (ζ ^ 2 / 2) := by
    unfold siR
    rw [← Real.rpow_mul (by linarith)]; congr 1; ring
  rw [this]
  have hp : 0 < siR ζ t ^ (2 + 3 * ζ) := Real.rpow_pos_of_pos hr _
  field_simp

lemma card_latticeBox_le (ht : 1 ≤ t) : ((latticeBox t).card : ℝ) ≤ 3125 * t ^ 5 := by
  unfold latticeBox
  rw [Fintype.card_piFinset]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, Int.card_Icc]
  have h : (((⌊2 * t⌋₊ : ℤ) + 1 - -(⌊2 * t⌋₊ : ℤ)).toNat : ℝ) ≤ 5 * t := by
    have h1 : ((⌊2 * t⌋₊ : ℤ) + 1 - -(⌊2 * t⌋₊ : ℤ)).toNat = 2 * ⌊2 * t⌋₊ + 1 := by omega
    rw [h1]
    have := Nat.floor_le (by linarith : (0 : ℝ) ≤ 2 * t)
    push_cast
    linarith
  calc ((((⌊2 * t⌋₊ : ℤ) + 1 - -(⌊2 * t⌋₊ : ℤ)).toNat ^ 5 : ℕ) : ℝ)
      = (((⌊2 * t⌋₊ : ℤ) + 1 - -(⌊2 * t⌋₊ : ℤ)).toNat : ℝ) ^ 5 := by push_cast; ring
    _ ≤ (5 * t) ^ 5 := pow_le_pow_left₀ (Nat.cast_nonneg _) h 5
    _ = 3125 * t ^ 5 := by ring

end Facts

/-- The failure bounds: the Bernoulli term and the three terms of `good_compl_le` are
`≤ C e^{-t^{ζ²/4}}`. -/
theorem bad_bound {ζ : ℝ} (hζ : 0 < ζ) (hζ1 : ζ ≤ 1 / 100) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 1 ≤ t →
      ENNReal.ofReal (Real.exp (-siMstar ζ t / 2)) +
        (20 * ENNReal.ofReal (Real.exp (-t ^ 2 / (2 * (t + 1)))) +
          (20 * (⌈t + 1⌉₊ : ℕ) : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-siRho ζ t ^ 2 / 16)) +
          ((latticeBox t).card : ℝ≥0∞) * ENNReal.ofReal
            (2 * Real.exp (-(cocc 5) * (siM ζ t / (3 * siBig ζ t) ^ 2)))) ≤
        ENNReal.ofReal (C * Real.exp (-t ^ (ζ ^ 2 / 4))) := by
  have ha0 : 0 ≤ ζ ^ 2 / 4 := by positivity
  -- the four decay constants
  obtain ⟨C1, hC1⟩ := exists_decay_bound 0 (c := 1 / 2) (e := 1 - 11 / 10 * ζ) (a := ζ ^ 2 / 4)
    (by norm_num) ha0 (by nlinarith)
  obtain ⟨C2, hC2⟩ := exists_decay_bound 0 (c := 1 / 4) (e := 1) (a := ζ ^ 2 / 4)
    (by norm_num) ha0 (by nlinarith)
  obtain ⟨C3, hC3⟩ := exists_decay_bound 1 (c := 1 / 16) (e := ζ / 50) (a := ζ ^ 2 / 4)
    (by norm_num) ha0 (by nlinarith)
  obtain ⟨C4, hC4⟩ := exists_decay_bound 5 (c := cocc 5 / 9) (e := ζ ^ 2 / 2) (a := ζ ^ 2 / 4)
    (by have := cocc_pos 5; positivity) ha0 (by nlinarith [sq_nonneg ζ])
  refine ⟨max C1 0 + 20 * max C2 0 + 60 * max C3 0 + 6250 * max C4 0, by positivity, ?_⟩
  intro t ht
  have ht0 : (0 : ℝ) < t := by linarith
  have hE : 0 < Real.exp (-t ^ (ζ ^ 2 / 4)) := Real.exp_pos _
  -- term 1
  have r1 : Real.exp (-siMstar ζ t / 2) ≤ max C1 0 * Real.exp (-t ^ (ζ ^ 2 / 4)) := by
    have := hC1 t ht
    rw [Real.rpow_zero, one_mul] at this
    have e : -siMstar ζ t / 2 = -(1 / 2) * t ^ (1 - 11 / 10 * ζ) := by unfold siMstar; ring
    rw [e]
    exact this.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hE.le)
  -- term 2
  have r2 : Real.exp (-t ^ 2 / (2 * (t + 1))) ≤ max C2 0 * Real.exp (-t ^ (ζ ^ 2 / 4)) := by
    have := hC2 t ht
    rw [Real.rpow_zero, one_mul, Real.rpow_one] at this
    refine le_trans (Real.exp_le_exp.2 ?_) (this.trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hE.le))
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  -- term 3
  have r3 : (⌈t + 1⌉₊ : ℝ) * Real.exp (-siRho ζ t ^ 2 / 16) ≤
      3 * (max C3 0 * Real.exp (-t ^ (ζ ^ 2 / 4))) := by
    have := hC3 t ht
    rw [Real.rpow_one] at this
    rw [siRho_sq ht]
    have e : -t ^ (ζ / 50) / 16 = -(1 / 16) * t ^ (ζ / 50) := by ring
    rw [e]
    have hc : (⌈t + 1⌉₊ : ℝ) ≤ 3 * t := by
      have := (Nat.ceil_lt_add_one (by linarith : (0 : ℝ) ≤ t + 1)).le
      linarith
    calc (⌈t + 1⌉₊ : ℝ) * Real.exp (-(1 / 16) * t ^ (ζ / 50))
        ≤ 3 * t * Real.exp (-(1 / 16) * t ^ (ζ / 50)) :=
          mul_le_mul_of_nonneg_right hc (Real.exp_nonneg _)
      _ = 3 * (t * Real.exp (-(1 / 16) * t ^ (ζ / 50))) := by ring
      _ ≤ 3 * (C3 * Real.exp (-t ^ (ζ ^ 2 / 4))) := by gcongr
      _ ≤ _ := by gcongr; exact le_max_left _ _
  -- term 4
  have r4 : ((latticeBox t).card : ℝ) * (2 * Real.exp (-(cocc 5) * (siM ζ t / (3 * siBig ζ t) ^ 2)))
      ≤ 6250 * (max C4 0 * Real.exp (-t ^ (ζ ^ 2 / 4))) := by
    have := hC4 t ht
    have e : -(cocc 5) * (siM ζ t / (3 * siBig ζ t) ^ 2) = -(cocc 5 / 9) * t ^ (ζ ^ 2 / 2) := by
      rw [siM_div ht]; ring
    rw [e]
    have h5 : t ^ (5 : ℝ) = t ^ 5 := by exact_mod_cast Real.rpow_natCast t 5
    rw [h5] at this
    have hcard := card_latticeBox_le ht
    calc ((latticeBox t).card : ℝ) * (2 * Real.exp (-(cocc 5 / 9) * t ^ (ζ ^ 2 / 2)))
        ≤ 3125 * t ^ 5 * (2 * Real.exp (-(cocc 5 / 9) * t ^ (ζ ^ 2 / 2))) :=
          mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = 6250 * (t ^ 5 * Real.exp (-(cocc 5 / 9) * t ^ (ζ ^ 2 / 2))) := by ring
      _ ≤ 6250 * (C4 * Real.exp (-t ^ (ζ ^ 2 / 4))) := by gcongr
      _ ≤ _ := by gcongr; exact le_max_left _ _
  -- combine
  have n1 : 0 ≤ Real.exp (-siMstar ζ t / 2) := Real.exp_nonneg _
  have n2 : 0 ≤ 20 * Real.exp (-t ^ 2 / (2 * (t + 1))) := by positivity
  have n3 : 0 ≤ 20 * ((⌈t + 1⌉₊ : ℝ) * Real.exp (-siRho ζ t ^ 2 / 16)) := by positivity
  have n4 : 0 ≤ ((latticeBox t).card : ℝ) *
      (2 * Real.exp (-(cocc 5) * (siM ζ t / (3 * siBig ζ t) ^ 2))) := by positivity
  have c2 : (20 : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-t ^ 2 / (2 * (t + 1)))) =
      ENNReal.ofReal (20 * Real.exp (-t ^ 2 / (2 * (t + 1)))) := by
    rw [ENNReal.ofReal_mul (by norm_num)]; simp
  have c3 : (20 * ((⌈t + 1⌉₊ : ℕ) : ℝ≥0∞)) * ENNReal.ofReal (Real.exp (-siRho ζ t ^ 2 / 16)) =
      ENNReal.ofReal (20 * ((⌈t + 1⌉₊ : ℝ) * Real.exp (-siRho ζ t ^ 2 / 16))) := by
    rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    simp [mul_assoc]
  have c4 : ((latticeBox t).card : ℝ≥0∞) * ENNReal.ofReal
      (2 * Real.exp (-(cocc 5) * (siM ζ t / (3 * siBig ζ t) ^ 2))) =
      ENNReal.ofReal (((latticeBox t).card : ℝ) *
        (2 * Real.exp (-(cocc 5) * (siM ζ t / (3 * siBig ζ t) ^ 2)))) := by
    rw [ENNReal.ofReal_mul (Nat.cast_nonneg _)]; simp
  rw [c2, c3, c4, ← ENNReal.ofReal_add n2 n3, ← ENNReal.ofReal_add (add_nonneg n2 n3) n4,
    ← ENNReal.ofReal_add n1 (add_nonneg (add_nonneg n2 n3) n4)]
  refine ENNReal.ofReal_le_ofReal ?_
  have : (max C1 0 + 20 * max C2 0 + 60 * max C3 0 + 6250 * max C4 0) *
      Real.exp (-t ^ (ζ ^ 2 / 4)) =
      max C1 0 * Real.exp (-t ^ (ζ ^ 2 / 4)) + 20 * (max C2 0 * Real.exp (-t ^ (ζ ^ 2 / 4))) +
      20 * (3 * (max C3 0 * Real.exp (-t ^ (ζ ^ 2 / 4)))) +
      6250 * (max C4 0 * Real.exp (-t ^ (ζ ^ 2 / 4))) := by ring
  rw [this]
  linarith

end ElboimSly.Brownian
