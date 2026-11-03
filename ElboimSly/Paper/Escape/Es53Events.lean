/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Escape.Es53Region
public import ElboimSly.Paper.Escape.Es53Geom
public import ElboimSly.Paper.Escape.Es53Arith
public import ElboimSly.Paper.Escape.Plan53Stop
public import ElboimSly.Paper.Avoid.ProcessLaw
public import Mathlib

/-!
# The events `ℬ, ℬ', 𝒞, 𝒟, 𝒢` of ES22 Lemma 5.3 for a path, in countable form

ES22 Lemma 5.3.  For a path `y : ℝ≥0 → ℤ^d` (the walk `W'_i` started at `p_i`), the five
events are written with the test times `qSet`, so that they are measurable for the product
`σ`-algebra, and equivalent to the real-time events for right-continuous paths:

* `EsB`: `‖y(s) - p_i‖ ≥ 2^{m+3}/m` for `s ∈ [4^m, 4^n]`, `m₁ ≤ m ≤ n`;
* `EsB'`: `‖y(s) - p_i‖ ≥ 2^j` for `s ∈ [j4^j, 4^n]`;
* `EsC A`: `y(s) ∉ A` for `s ≤ 4^n`;
* `EsD`: unit-window displacements ending at `t ≤ 4^m` are `< m²`, `m₁ ≤ m ≤ n`;
* `EsG`: for `s ≤ j4^j`, `d(y(s), B^-) > 2^{j-3}` and `‖y(s) - p_ℓ‖ > n^{17}/6`, `ℓ ≠ i`.
-/

@[expose] public section

open Set
open scoped NNReal

namespace ElboimSly.Paper.Escape

open ElboimSly.Paper

variable {k : ℕ}

/-- The test time `x.toNNReal` of a nonnegative real bound. -/
noncomputable abbrev tn (x : ℝ) : ℝ≥0 := x.toNNReal

def EsB (n m₁ : ℕ) (p : Fin (k + 2) → ℤ) (y : ℝ≥0 → Fin (k + 2) → ℤ) : Prop :=
  ∀ m : ℕ, m₁ ≤ m → m ≤ n → ¬ ∃ q ∈ qSet (tn ((4 : ℝ) ^ m)) (tn ((4 : ℝ) ^ n)),
    ‖y q - p‖ < 2 ^ (m + 3) / m

def EsB' (n j : ℕ) (p : Fin (k + 2) → ℤ) (y : ℝ≥0 → Fin (k + 2) → ℤ) : Prop :=
  ¬ ∃ q ∈ qSet (tn ((j : ℝ) * 4 ^ j)) (tn ((4 : ℝ) ^ n)), ‖y q - p‖ < 2 ^ j

def EsC (n : ℕ) (A : Set (Fin (k + 2) → ℤ)) (y : ℝ≥0 → Fin (k + 2) → ℤ) : Prop :=
  ¬ ∃ q ∈ qSet 0 (tn ((4 : ℝ) ^ n)), y q ∈ A

def EsD (n m₁ : ℕ) (y : ℝ≥0 → Fin (k + 2) → ℤ) : Prop :=
  ∀ m : ℕ, m₁ ≤ m → m ≤ n → ¬ ∃ t ∈ qSet 0 (tn ((4 : ℝ) ^ m)), ∃ s ∈ qSet 0 (tn ((4 : ℝ) ^ m)),
    0 < t ∧ s ≤ t ∧ t ≤ s + 1 ∧ (m : ℝ) ^ 2 ≤ ‖y t - y s‖

def EsG (n j I : ℕ) (u : Fin (k + 2) → ℤ) (i : ℕ) (y : ℝ≥0 → Fin (k + 2) → ℤ) : Prop :=
  ¬ ∃ q ∈ qSet 0 (tn ((j : ℝ) * 4 ^ j)),
    (Metric.infDist (fun c => ((y q c : ℤ) : ℝ))
        ((fun x c => ((x c : ℤ) : ℝ)) '' escBlockMinus j u) ≤ (2 : ℝ) ^ j / 8) ∨
    (∃ ℓ, 1 ≤ ℓ ∧ ℓ ≤ I ∧ ℓ ≠ i ∧ ‖y q - escPoint n j u ℓ‖ ≤ (n : ℝ) ^ 17 / 6)

theorem norm_escCast_sub (z p : Fin (k + 2) → ℤ) : ‖escCast z - escCast p‖ = ‖z - p‖ := by
  apply le_antisymm
  · rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
    intro c
    have := norm_le_pi_norm (z - p) c
    simpa [escCast, Real.norm_eq_abs, Int.norm_eq_abs] using this
  · rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
    intro c
    have := norm_le_pi_norm (escCast z - escCast p) c
    simpa [escCast, Real.norm_eq_abs, Int.norm_eq_abs] using this

/-- A right-continuous path avoiding a condition at all test times avoids it at all times. -/
theorem forall_of_not_exists_qSet {x : ℝ≥0 → Fin (k + 2) → ℤ} (hx : IsRCPath x) {a b : ℝ≥0}
    (hab : a ≤ b) {P : (Fin (k + 2) → ℤ) → Prop} (h : ¬ ∃ q ∈ qSet a b, P (x q)) :
    ∀ s : ℝ≥0, a ≤ s → s ≤ b → ¬ P (x s) := fun s h1 h2 hP =>
  h ((exists_Icc_iff_qSet hx hab P).1 ⟨s, h1, h2, hP⟩)

end ElboimSly.Paper.Escape
