/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Heavy.GoodLocalIndep
public import Mathlib

/-!
# Counting the starting data of a block

Probability that a block is bad, the count `|U| = (9·2^k)^d` and `⌊β⌋ + 1 ≤ 4^{n+1} + 1`.
-/

@[expose] public section

open Set

namespace ElboimSly.Paper.Heavy

open ElboimSly ElboimSly.Paper

variable {d : ℕ}

theorem abs_sub_le_of_latDist_pow {k m : ℕ} {ι z : Fin d → ℤ}
    (h : latDist z (heavyBlock k ι) ≤ (2 : ℝ) ^ m) :
    ∃ a ∈ heavyBlock k ι, ∀ c, |z c - a c| ≤ 2 ^ m := by
  have h' : latDist z (heavyBlock k ι) ≤ ((2 ^ m : ℕ) : ℝ) := by
    push_cast; exact h
  obtain ⟨a, haB, ha⟩ := exists_le_of_latDist_le (heavyBlock_nonempty k ι) h'
  refine ⟨a, haB, fun c => ?_⟩
  have h1 : ((|z c - a c| : ℤ) : ℝ) ≤ ((2 ^ m : ℕ) : ℝ) := by
    have h2 : ‖(z - a) c‖ ≤ ‖z - a‖ := norm_le_pi_norm (z - a) c
    rw [Int.cast_abs]
    simpa [Int.norm_eq_abs] using h2.trans ha
  have h3 : |z c - a c| ≤ ((2 ^ m : ℕ) : ℤ) := by exact_mod_cast h1
  simpa using h3

theorem exists_finset_nbhd (k : ℕ) (ι : Fin d → ℤ) :
    ∃ Uf : Finset (Fin d → ℤ), (∀ u, u ∈ latNbhd (heavyBlock k ι) ((2 : ℝ) ^ (k + 2)) ↔ u ∈ Uf) ∧
      Uf.card ≤ (9 * 2 ^ k) ^ d := by
  classical
  set P : ℤ := 2 ^ k with hP
  have hP0 : 0 < P := by positivity
  set box : Finset (Fin d → ℤ) :=
    Fintype.piFinset fun c => Finset.Ico (P * ι c - 4 * P) (P * ι c + 5 * P) with hbox
  refine ⟨box.filter (· ∈ latNbhd (heavyBlock k ι) ((2 : ℝ) ^ (k + 2))), fun u => ?_, ?_⟩
  · simp only [Finset.mem_filter]
    refine ⟨fun hu => ⟨?_, hu⟩, fun h => h.2⟩
    obtain ⟨a, haB, ha⟩ := abs_sub_le_of_latDist_pow (m := k + 2) hu
    simp only [hbox, Fintype.mem_piFinset, Finset.mem_Ico]
    intro c
    have h1 := mem_heavyBlock_bounds haB c
    have h2 := abs_le.1 (ha c)
    have : (2 : ℤ) ^ (k + 2) = 4 * P := by rw [hP]; ring
    rw [this] at h2
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  · refine (Finset.card_filter_le _ _).trans ?_
    rw [hbox, Fintype.card_piFinset]
    have : ∀ c : Fin d, (Finset.Ico (P * ι c - 4 * P) (P * ι c + 5 * P)).card = 9 * 2 ^ k := by
      intro c
      rw [Int.card_Ico]
      have : P * ι c + 5 * P - (P * ι c - 4 * P) = ((9 * 2 ^ k : ℕ) : ℤ) := by
        rw [hP]; push_cast; ring
      rw [this, Int.toNat_natCast]
    rw [Finset.prod_congr rfl (fun c _ => this c)]
    simp

theorem exists_finset_times {β : ℝ} (n : ℕ) (hβ : β ≤ (4 : ℝ) ^ (n + 1)) :
    ∃ Q : Finset ℤ, (∀ q : ℤ, q ∈ Q ↔ (0 : ℝ) ≤ q ∧ (q : ℝ) ≤ β) ∧ Q.card ≤ 4 ^ (n + 1) + 1 := by
  refine ⟨Finset.Icc 0 ⌊β⌋, fun q => ?_, ?_⟩
  · simp only [Finset.mem_Icc, Int.le_floor]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨by exact_mod_cast h1, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨by exact_mod_cast h1, h2⟩
  · rw [Int.card_Icc]
    have h1 : (⌊β⌋ : ℝ) ≤ β := Int.floor_le β
    have h2 : ⌊β⌋ ≤ ((4 ^ (n + 1) : ℕ) : ℤ) := by
      have : (⌊β⌋ : ℝ) ≤ (((4 ^ (n + 1) : ℕ) : ℤ) : ℝ) := by push_cast; linarith
      exact_mod_cast this
    generalize (4 ^ (n + 1) : ℕ) = M at h2 ⊢
    omega

end ElboimSly.Paper.Heavy
