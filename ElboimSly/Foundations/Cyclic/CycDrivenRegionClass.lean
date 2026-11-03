/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycDrivenRegionRules
public import Mathlib

/-!
# Jumps of the driven walk in the class of a jump of the driver

The driven walk is a driven world-line, "The rules agree": if `x` jumps at `r`, then `w` has no jump at
the times `r - kβ > 0`, since such a jump's class would contain a jump of `x` at a time `≡ r`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

variable {d : ℕ} {β : ℝ} [Fact (0 < β)] {x : ℝ≥0 → Fin d → ℤ}

omit [Fact (0 < β)] in
/-- Every jump of `w` up to `τ` lies in the class of a jump of `x`. -/
theorem class_root (hx : IsDrivingPath x) (hβ : 0 < β.toNNReal)
    (hi : ∀ s ∈ CDisc x, ∀ s' ∈ CDisc x, ∀ k : ℕ, 1 ≤ k → s' ≠ s + k * β.toNNReal) :
    ∀ t ∈ CDisc (drivenWalk β.toNNReal x), (t : ℝ≥0∞) ≤ drivenTreg β.toNNReal x →
      ∃ t0 ∈ CDisc x, ∃ m : ℕ, t = t0 + m * β.toNNReal := by
  obtain ⟨-, -, a3, -⟩ := drivenWalk_closing hx hβ hi
  have key : ∀ n : ℕ, ∀ t ∈ CDisc (drivenWalk β.toNNReal x),
      (t : ℝ≥0∞) ≤ drivenTreg β.toNNReal x → t < n * β.toNNReal →
        ∃ t0 ∈ CDisc x, ∃ m : ℕ, t = t0 + m * β.toNNReal := by
    intro n
    induction n with
    | zero => intro t _ _ ht; simp at ht
    | succ n ih =>
      intro t ht hτ htn
      by_cases hall : ∀ k, IsDelayIdx β.toNNReal t k →
          t - k * β.toNNReal ∉ CDisc (drivenWalk β.toNNReal x)
      · exact ⟨t, a3 t ht hτ hall, 0, by simp⟩
      · push Not at hall
        obtain ⟨k, hk, hkd⟩ := hall
        have hlt : t - k * β.toNNReal < t := delayIdx_lt β.toNNReal hβ hk
        have hτ' : ((t - k * β.toNNReal : ℝ≥0) : ℝ≥0∞) ≤ drivenTreg β.toNNReal x :=
          (by exact_mod_cast hlt.le : ((t - k * β.toNNReal : ℝ≥0) : ℝ≥0∞) ≤ t).trans hτ
        have hlt2 : t - k * β.toNNReal < n * β.toNNReal := by
          have hβk : β.toNNReal ≤ k * β.toNNReal := by
            exact le_mul_of_one_le_left zero_le (by exact_mod_cast hk.1)
          calc t - k * β.toNNReal ≤ t - β.toNNReal := tsub_le_tsub_left hβk _
            _ < n * β.toNNReal := by
              rw [tsub_lt_iff_left (hβk.trans hk.2)]
              calc t < (n + 1 : ℕ) * β.toNNReal := htn
                _ = n * β.toNNReal + β.toNNReal := by push_cast; ring
                _ = β.toNNReal + n * β.toNNReal := add_comm _ _
        obtain ⟨t0, ht0, m, hm⟩ := ih _ hkd hτ' hlt2
        refine ⟨t0, ht0, m + k, ?_⟩
        have : t = t - k * β.toNNReal + k * β.toNNReal := (tsub_add_cancel_of_le hk.2).symm
        rw [this, hm]; push_cast; ring
  intro t ht hτ
  obtain ⟨n, hn⟩ := exists_lt_nsmul hβ t
  exact key n t ht hτ (by simpa [nsmul_eq_mul] using hn)

omit [Fact (0 < β)] in
/-- If `x` jumps at `r ≤ τ`, then `w` has no jump at `r - kβ > 0`. -/
theorem no_jump_in_class (hx : IsDrivingPath x) (hβ : 0 < β.toNNReal)
    (hi : ∀ s ∈ CDisc x, ∀ s' ∈ CDisc x, ∀ k : ℕ, 1 ≤ k → s' ≠ s + k * β.toNNReal)
    {r : ℝ≥0} (hrx : r ∈ CDisc x) (hrτ : (r : ℝ≥0∞) ≤ drivenTreg β.toNNReal x) {k : ℕ}
    (hk : IsDelayIdx β.toNNReal r k) (_hpos : 0 < r - k * β.toNNReal) :
    r - k * β.toNNReal ∉ CDisc (drivenWalk β.toNNReal x) := by
  intro hd
  have hlt : r - k * β.toNNReal < r := delayIdx_lt β.toNNReal hβ hk
  have hτ' : ((r - k * β.toNNReal : ℝ≥0) : ℝ≥0∞) ≤ drivenTreg β.toNNReal x :=
    (by exact_mod_cast hlt.le : ((r - k * β.toNNReal : ℝ≥0) : ℝ≥0∞) ≤ r).trans hrτ
  obtain ⟨t0, ht0, m, hm⟩ := class_root hx hβ hi _ hd hτ'
  have : r = t0 + (m + k : ℕ) * β.toNNReal := by
    have h2 : r = r - k * β.toNNReal + k * β.toNNReal := (tsub_add_cancel_of_le hk.2).symm
    rw [h2, hm]; push_cast; ring
  exact hi t0 ht0 r hrx (m + k) (by have := hk.1; omega) this

end ElboimSly.Cyclic

end
