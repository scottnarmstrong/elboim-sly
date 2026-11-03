/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Escape.Plan5Rules
public import ElboimSly.Paper.Escape.Plan5
public import Mathlib

/-!
# Vertex geometry of the block `B`, its half `B⁻`, the box `𝒬` and the face `F_B`

ES22 Lemma 5.5, Step 1 (agreement on `E₅₆ ∩ E₀`: "`𝒬 ∩ B⁻ = ∅`", "`F_B ⊆ B⁻`",
"`0 ∉ 𝒬 ∪ F_B`").
-/

@[expose] public section

namespace ElboimSly.Paper.Escape

variable {k : ℕ}

theorem pw_two_pow_div_two {j : ℕ} (hj : 1 ≤ j) : (2 : ℤ) ^ j / 2 = 2 ^ (j - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
  rw [pow_succ]; simp

/-- `𝒬 ∩ B⁻ = ∅`. -/
theorem escQ_not_mem_blockMinus {j : ℕ} (hj : 1 ≤ j) {u y : EscV k} (hy : y ∈ escQ j u) :
    y ∉ escBlockMinus j u := by
  intro h
  have h1 := hy.1.1
  have h2 := h.1.2
  rw [pw_two_pow_div_two hj] at h1
  omega

/-- `𝒬 ⊆ B`. -/
theorem escQ_subset_block {j : ℕ} (hj : 3 ≤ j) {u y : EscV k} (hy : y ∈ escQ j u) :
    y ∈ escBlock j u := by
  obtain ⟨m, rfl⟩ : ∃ m, j = m + 3 := ⟨j - 3, by omega⟩
  have hp : (2 : ℤ) ^ (m + 3) = 8 * 2 ^ m := by ring
  have hm : (1 : ℤ) ≤ 2 ^ m := one_le_pow₀ (by norm_num)
  obtain ⟨⟨h1, h2⟩, h3⟩ := hy
  intro c
  rw [hp] at *
  generalize (2 : ℤ) ^ m = X at *
  by_cases hc : c = 0
  · subst hc
    constructor <;> omega
  · obtain ⟨h4, h5⟩ := h3 c hc
    constructor <;> omega

/-- `F_B ∩ 𝒬 = ∅`. -/
theorem pw_escFace_not_mem_escQ {j : ℕ} (hj : 1 ≤ j) {u x : EscV k} (hx : x ∈ escFace j u) :
    x ∉ escQ j u := by
  intro h
  have h1 := h.1.1
  have h2 := hx.1
  rw [pw_two_pow_div_two hj] at h1
  omega

/-- `B⁻ ⊆ B`. -/
theorem blockMinus_subset_block {j : ℕ} (hj : 1 ≤ j) {u x : EscV k} (hx : x ∈ escBlockMinus j u) :
    x ∈ escBlock j u := by
  obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
  have hp : (2 : ℤ) ^ (m + 1) = 2 * 2 ^ m := by ring
  have hm : (1 : ℤ) ≤ 2 ^ m := one_le_pow₀ (by norm_num)
  intro c
  by_cases hc : c = 0
  · subst hc
    have := hx.1
    simp only [Nat.add_sub_cancel] at this
    rw [hp]; constructor <;> omega
  · exact hx.2 c hc

/-- `0 ∉ 𝒬` for an admissible block. -/
theorem zero_not_mem_escQ {j : ℕ} (hj : 3 ≤ j) {u : EscV k} (hadm : EscAdmissible j u) :
    (0 : EscV k) ∉ escQ j u := by
  intro h
  have hB := escQ_subset_block hj h
  rcases hadm with h0 | rfl
  · exact h0 hB
  · refine escQ_not_mem_blockMinus (by omega) h ⟨⟨le_rfl, ?_⟩, fun c _ => ⟨le_rfl, ?_⟩⟩
    · simp
    · simp

end ElboimSly.Paper.Escape
