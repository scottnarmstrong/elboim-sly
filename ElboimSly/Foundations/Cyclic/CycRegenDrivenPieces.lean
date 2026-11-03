/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycThitDriven
public import ElboimSly.Foundations.Cyclic.CycThitDrivenRules
public import Mathlib

/-!
# The pieces of the regenerated driven walk

ES22 Lemma 2.1 (a) and the shift identity of (b).

* `drivenPieces_mem_cycCF`: (a), the pieces `x^{(i)}` are coincidence free.
* `drivenRegenFrom_shift`: `W^x_reg(σ_n + r) = W^y_reg(r)` for `y = x^{(n+1)}`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

variable {d : ℕ} {b : ℝ≥0} {x : ℝ≥0 → Fin d → ℤ}

theorem shiftPath_add (f : ℝ≥0 → Fin d → ℤ) (a c : ℝ≥0) :
    shiftPath (shiftPath f a) c = shiftPath f (a + c) := by
  funext s
  simp only [shiftPath_apply]
  rw [add_assoc]; abel

theorem drivenPieces_add (b : ℝ≥0) (x : ℝ≥0 → Fin d → ℤ) (n j : ℕ) :
    drivenPieces b (drivenPieces b x n) j = drivenPieces b x (n + j) := by
  induction j with
  | zero => rfl
  | succ j ih => rw [← Nat.add_assoc]; simp only [drivenPieces]; rw [ih]

theorem drivenSigma_add (b : ℝ≥0) (x : ℝ≥0 → Fin d → ℤ) (n j : ℕ) :
    drivenSigma b x (n + j) = drivenSigma b x n + drivenSigma b (drivenPieces b x n) j := by
  unfold drivenSigma partialSums
  rw [Finset.sum_range_add]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  show _ = drivenTreg b (drivenPieces b (drivenPieces b x n) k)
  rw [drivenPieces_add]

theorem pathTreg_exists {w : ℝ≥0 → Fin d → ℤ} (h : pathTreg b w < ⊤) :
    ∃ j : ℕ, 1 ≤ j ∧ pathTreg b w = (((j : ℝ≥0) * b : ℝ≥0) : ℝ≥0∞) ∧ w ((j : ℝ≥0) * b) = 0 := by
  rcases pathTreg_top_or b w with h' | h'
  · exact absurd h' h.ne
  · exact h'

theorem drivenSigma_succ_lt {n : ℕ} (h : drivenSigma b x (n + 1) < ⊤) :
    drivenSigma b x n < ⊤ ∧ drivenTreg b (drivenPieces b x n) < ⊤ := by
  rw [drivenSigma_succ] at h
  exact ⟨lt_of_le_of_lt le_self_add h, lt_of_le_of_lt le_add_self h⟩

/-- **(a)**: the pieces `x^{(i)}` of a coincidence-free path are coincidence free. -/
theorem drivenPieces_mem_cycCF (hx : x ∈ CycCF b) :
    ∀ n : ℕ, drivenSigma b x n < ⊤ → drivenPieces b x n ∈ CycCF b := by
  intro n
  induction n with
  | zero => intro _; exact hx
  | succ n ih =>
    intro h
    obtain ⟨h1, h2⟩ := drivenSigma_succ_lt h
    obtain ⟨j, -, hj, -⟩ := pathTreg_exists (b := b) (w := drivenWalk b (drivenPieces b x n)) h2
    have : (drivenTreg b (drivenPieces b x n)).toNNReal = (j : ℝ≥0) * b := by
      have : drivenTreg b (drivenPieces b x n) = (((j : ℝ≥0) * b : ℝ≥0) : ℝ≥0∞) := hj
      rw [this, ENNReal.toNNReal_coe]
    show shiftPath (drivenPieces b x n) (drivenTreg b (drivenPieces b x n)).toNNReal ∈ CycCF b
    rw [this]
    exact cycCF_shiftPath (ih h1) j

/-- The pieces are shifts of `x` by the regeneration times. -/
theorem drivenPieces_eq_shift (b : ℝ≥0) {x : ℝ≥0 → Fin d → ℤ} (hx0 : x 0 = 0) :
    ∀ n : ℕ, drivenSigma b x n < ⊤ → drivenPieces b x n = shiftPath x (drivenSigma b x n).toNNReal := by
  intro n
  induction n with
  | zero =>
    intro _
    funext s
    simp [drivenSigma_zero, shiftPath_apply, hx0, drivenPieces]
  | succ n ih =>
    intro h
    obtain ⟨h1, h2⟩ := drivenSigma_succ_lt h
    show shiftPath (drivenPieces b x n) _ = _
    rw [drivenSigma_succ, ENNReal.toNNReal_add h1.ne h2.ne, ← shiftPath_add, ← ih h1]

end ElboimSly.Cyclic

end
