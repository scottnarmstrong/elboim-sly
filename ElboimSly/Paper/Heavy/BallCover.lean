/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Heavy.Blocks

/-!
# Covering a ball by `2^d` dyadic blocks

Supporting material for ES22 Lemma 6.4, Step 2 (supplement; deviation F73).

If `2 r + 1 ≤ 2^m` then the box `{v : ‖v - x‖ ≤ r}` is contained in the union of at most `2^d` blocks
of `ℬ_m`: in each coordinate it meets at most two dyadic intervals of length `2^m`.
-/

@[expose] public section

open Set

namespace ElboimSly.Paper

variable {d : ℕ}

theorem ball_subset_blocks (m : ℕ) (x : Fin d → ℤ) {r : ℝ} (hr : 0 ≤ r)
    (hm : 2 * r + 1 ≤ (2 : ℝ) ^ m) :
    ∃ T : Finset (Fin d → ℤ), T.card ≤ 2 ^ d ∧
      {v : Fin d → ℤ | ‖v - x‖ ≤ r} ⊆ ⋃ ι ∈ T, heavyBlock m ι := by
  classical
  set R : ℤ := ⌊r⌋ with hR
  have hR0 : 0 ≤ R := Int.floor_nonneg.2 hr
  have hRr : (R : ℝ) ≤ r := Int.floor_le r
  have hq : (0 : ℤ) < 2 ^ m := by positivity
  have h2R : 2 * R < 2 ^ m := by
    have : (2 * (R : ℝ)) < (2 : ℝ) ^ m := by linarith
    exact_mod_cast this
  set a : Fin d → ℤ := fun c => (x c - R) / 2 ^ m with ha
  refine ⟨Fintype.piFinset fun c => {a c, a c + 1}, ?_, ?_⟩
  · calc (Fintype.piFinset fun c => ({a c, a c + 1} : Finset ℤ)).card
        = ∏ c : Fin d, ({a c, a c + 1} : Finset ℤ).card := Fintype.card_piFinset _
      _ ≤ ∏ _c : Fin d, 2 := Finset.prod_le_prod fun c _ => Finset.card_le_two
      _ = 2 ^ d := by simp
  · intro v hv
    have hvc : ∀ c, |v c - x c| ≤ R := by
      intro c
      have h1 : ‖v - x‖ ≤ r := hv
      have h2 : ‖(v - x) c‖ ≤ ‖v - x‖ := norm_le_pi_norm (v - x) c
      have h3 : (|v c - x c| : ℝ) ≤ r := by
        simpa [Int.norm_eq_abs] using h2.trans h1
      have h4 : |v c - x c| ≤ R := by
        rw [hR]; apply Int.le_floor.2
        exact_mod_cast h3
      exact h4
    refine mem_iUnion₂.2 ⟨heavyBlockIdx m v, ?_, mem_heavyBlock_idx m v⟩
    rw [Fintype.mem_piFinset]
    intro c
    have hb := abs_le.1 (hvc c)
    have hlo : a c ≤ v c / 2 ^ m := Int.ediv_le_ediv hq (by linarith)
    have hhi : v c / 2 ^ m ≤ a c + 1 := by
      have h1 := Int.emod_add_mul_ediv (x c - R) (2 ^ m)
      have h2 := Int.emod_nonneg (x c - R) hq.ne'
      have h3 : v c < (a c + 2) * 2 ^ m := by
        have : (x c - R) % 2 ^ m < 2 ^ m := Int.emod_lt_of_pos _ hq
        simp only [ha]
        nlinarith
      have := (Int.ediv_lt_iff_lt_mul hq).2 h3
      omega
    simp only [heavyBlockIdx, Finset.mem_insert, Finset.mem_singleton]
    omega

end ElboimSly.Paper
