/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import Mathlib

/-!
# Scale, escape event, blocks and the points `p_i` of ES22 §5

Scale and the constant γ; The escape event; Blocks with arbitrary corner, halves, admissibility; The points p_i.

The dimension is `k + 2` so that the first coordinate (index `0`) and the second coordinate
(index `1`, the direction `e₂`) exist.  Paths are `ℝ → Fin (k+2) → ℤ`.
-/

@[expose] public section

namespace ElboimSly.Paper

/-- Scale and the constant γ: `j = j_n` with `n^20 ≤ 2^j < 2 n^20` (the ceiling of `log₂ n^20`). -/
def escJ (n : ℕ) : ℕ := Nat.clog 2 (n ^ 20)

lemma le_two_pow_escJ (n : ℕ) : n ^ 20 ≤ 2 ^ escJ n :=
  Nat.le_pow_clog (by norm_num) _

lemma two_pow_escJ_lt {n : ℕ} (hn : 2 ≤ n) : 2 ^ escJ n < 2 * n ^ 20 := by
  have h1 : 1 < n ^ 20 := Nat.one_lt_pow (by norm_num) (by omega)
  have h := Nat.pow_pred_clog_lt_self (b := 2) (x := n ^ 20) (by norm_num) h1
  rw [Nat.pred_eq_sub_one] at h
  have hj : 0 < escJ n := Nat.clog_pos (by norm_num) h1
  have : 2 ^ escJ n = 2 * 2 ^ (escJ n - 1) := by
    rw [← pow_succ']; congr 1; unfold escJ at *; omega
  unfold escJ at *
  omega

section Escape

variable {d : ℕ}

/-- The escape event: `ℰ(T) = {∀ s ∈ [4^j, 4^n], ‖W(T+s) - W(T)‖ ≥ √s / n}`. -/
def EscEvent (n j : ℕ) (W : ℝ → Fin d → ℤ) (T : ℝ) : Prop :=
  ∀ s : ℝ, (4 : ℝ) ^ j ≤ s → s ≤ (4 : ℝ) ^ n → Real.sqrt s / n ≤ ‖W (T + s) - W T‖

end Escape

section Blocks

variable {k : ℕ}

/-- Blocks with arbitrary corner, halves, admissibility: `B_u = u + [0, 2^j)^d ∩ ℤ^d`. -/
def escBlock (j : ℕ) (u : Fin (k + 2) → ℤ) : Set (Fin (k + 2) → ℤ) :=
  {x | ∀ c, u c ≤ x c ∧ x c < u c + 2 ^ j}

/-- Blocks with arbitrary corner, halves, admissibility: `B^- = u + ([0, 2^{j-1}) × [0, 2^j)^{d-1}) ∩ ℤ^d`. -/
def escBlockMinus (j : ℕ) (u : Fin (k + 2) → ℤ) : Set (Fin (k + 2) → ℤ) :=
  {x | (u 0 ≤ x 0 ∧ x 0 < u 0 + 2 ^ (j - 1)) ∧ ∀ c, c ≠ 0 → (u c ≤ x c ∧ x c < u c + 2 ^ j)}

/-- Blocks with arbitrary corner, halves, admissibility: `B^+ = B \ B^-`. -/
def escBlockPlus (j : ℕ) (u : Fin (k + 2) → ℤ) : Set (Fin (k + 2) → ℤ) :=
  escBlock j u \ escBlockMinus j u

/-- Blocks with arbitrary corner, halves, admissibility: `∂B`, the vertices of `B` with a neighbour (at `ℓ¹` distance one)
outside `B`. -/
def escBoundary (j : ℕ) (u : Fin (k + 2) → ℤ) : Set (Fin (k + 2) → ℤ) :=
  {x | x ∈ escBlock j u ∧ ∃ c, ∃ s : ℤ, (s = 1 ∨ s = -1) ∧
    Function.update x c (x c + s) ∉ escBlock j u}

/-- Blocks with arbitrary corner, halves, admissibility: the centre `q = u + 2^{j-2}(1,2,…,2)` of `B^-`, in `ℝ^d`. -/
noncomputable def escCentre (j : ℕ) (u : Fin (k + 2) → ℤ) : Fin (k + 2) → ℝ :=
  fun c => (u c : ℝ) + (2 : ℝ) ^ j / 4 * (if c = 0 then 1 else 2)

/-- Blocks with arbitrary corner, halves, admissibility: the face `F_B = u + {2^{j-1}-1} × [2^{j-2}, 3·2^{j-2}]^{d-1} ∩ ℤ^d`. -/
def escFace (j : ℕ) (u : Fin (k + 2) → ℤ) : Set (Fin (k + 2) → ℤ) :=
  {x | x 0 = u 0 + 2 ^ (j - 1) - 1 ∧
    ∀ c, c ≠ 0 → (u c + 2 ^ j / 4 ≤ x c ∧ x c ≤ u c + 3 * (2 ^ j / 4))}

/-- Blocks with arbitrary corner, halves, admissibility: a block is admissible if `0 ∉ B` or `u = 0`. -/
def EscAdmissible (j : ℕ) (u : Fin (k + 2) → ℤ) : Prop :=
  (0 : Fin (k + 2) → ℤ) ∉ escBlock j u ∨ u = 0

/-- The points p_i: `λ_n = ⌊n^17 / 3⌋`. -/
def escLambda (n : ℕ) : ℕ := n ^ 17 / 3

/-- The points p_i: `p_i = u + 2^{j-2}(3,2,…,2) + i λ_n e₂`. -/
def escPoint (n j : ℕ) (u : Fin (k + 2) → ℤ) (i : ℕ) : Fin (k + 2) → ℤ :=
  fun c => u c + 2 ^ j / 4 * (if c = 0 then 3 else 2) + (if c = 1 then (i * escLambda n : ℤ) else 0)

/-- The points p_i: `I_* = min(n^3, max{i ≥ 1 : i λ_n ≤ 3·2^{j-4}})`, written as the
greatest `i ≤ n^3` with `1 ≤ i` and `16 i λ_n ≤ 3·2^j` (the condition is downward closed in `i`). -/
def escIstar (n j : ℕ) : ℕ :=
  Nat.findGreatest (fun i => 1 ≤ i ∧ 16 * (i * escLambda n) ≤ 3 * 2 ^ j) (n ^ 3)

end Blocks

end ElboimSly.Paper
