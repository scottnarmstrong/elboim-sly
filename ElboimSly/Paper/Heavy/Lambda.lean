/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Heavy.Entrance
public import ElboimSly.Paper.Heavy.ScalesFactsB

/-!
# Segments and blocks that are bad by time `t`

Segments; blocks bad by time t; Lambda_t (ES22 §6; deviation F57).

For a path `w`, `x ∈ CI_β`, the segment at `x` is `u ↦ w (x + u)`, `u ∈ [0, t'_k]`.

* `latDist u A = d(u, A)`, `latNbhd A r = N(A, r)`.
* `SegClosed`, `SegRelaxed`, `SegMerge`, `proxSet`: closing, relaxedness, merging, proximity set.
* `BadByTime` (V1)-(V3), `badCount = b_t`, `badUnion = Λ_t`.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace ElboimSly.Paper

open ElboimSly

variable {d : ℕ}

/-- `d(u, A) = inf_{v ∈ A} ‖u - v‖`. -/
noncomputable def latDist (u : Fin d → ℤ) (A : Set (Fin d → ℤ)) : ℝ := ⨅ v : A, ‖u - (v : Fin d → ℤ)‖

/-- `N(A, r) = {u : d(u, A) ≤ r}`. -/
def latNbhd (A : Set (Fin d → ℤ)) (r : ℝ) : Set (Fin d → ℤ) := {u | latDist u A ≤ r}

section seg

variable (β : ℝ) (tk : ℝ) (w : ℝ → Fin d → ℤ)

/-- The segment at `x` closes: `w (x + u) = w x` for some `u ∈ βℤ ∩ (0, t'_k]`. -/
def SegClosed (x : ℝ) : Prop := ∃ u : ℝ, 0 < u ∧ u ≤ tk ∧ (∃ ℓ : ℤ, u = ℓ * β) ∧ w (x + u) = w x

/-- The segment at `x` is relaxed: the relaxed times have measure `≥ (0.9 + 1/k') t'_k`. -/
def SegRelaxed (k' : ℕ) (x : ℝ) : Prop :=
  ENNReal.ofReal ((9 / 10 + 1 / (k' : ℝ)) * tk) ≤
    volume {u : ℝ | u ∈ Icc 0 tk ∧ IsRelaxedTimeWrt β w x (x + u)}

/-- The segments at `x₁, x₂` merge. -/
def SegMerge (x₁ x₂ : ℝ) : Prop :=
  ∃ u₁ u₂ : ℝ, u₁ ∈ Icc 0 tk ∧ u₂ ∈ Icc 0 tk ∧ w (x₁ + u₁) = w (x₂ + u₂) ∧
    ∃ ℓ : ℤ, (x₁ + u₁) - (x₂ + u₂) = ℓ * β

/-- The proximity set `𝔓(x₁, x₂)` with radius `ρ = 1.9^k`. -/
def proxSet (ρ : ℝ) (x₁ x₂ : ℝ) : Set ℝ :=
  {u₂ : ℝ | u₂ ∈ Icc 0 tk ∧ ∃ u₁ ∈ Icc 0 tk, ‖w (x₁ + u₁) - w (x₂ + u₂)‖ ≤ ρ}

end seg

/-- Segments; blocks bad by time t; Lambda_t. The block `B = heavyBlock k ι` is bad by time `t` for `w`
(conditions (V1)-(V3)). The data: `β`, `t₀` and the level `n` (through `k`, `k'`, `t'_k`). -/
def BadByTime (d : ℕ) (β t₀ : ℝ) (n : ℕ) (w : ℝ → Fin d → ℤ) (ι : Fin d → ℤ) (t : ℝ) : Prop :=
  let k := heavyLevel d n
  let tk := heavyTkPrime d t₀ n
  let B := heavyBlock k ι
  -- (V1)
  (∃ x ∈ cycIntTimes β, w x ∈ latNbhd B (2 ^ (k + 2)) ∧ x + tk ≤ t ∧ ¬ SegClosed β tk w x ∧
      ¬ SegRelaxed β tk w (heavyLevelPrime d t₀ n) x) ∨
  -- (V2)
  (∃ x ∈ cycIntTimes β, x ≤ t ∧ w x ∈ latNbhd B (2 ^ (k + 2)) ∧
      ∃ u ∈ Icc (0 : ℝ) (min tk (t - x)), (2 : ℝ) ^ (k - 1) < ‖w (x + u) - w x‖) ∨
  -- (V3)
  (∃ x₁ ∈ cycIntTimes β, ∃ x₂ ∈ cycIntTimes β, w x₁ ∈ latNbhd B (2 ^ (k + 2)) ∧
      w x₂ ∈ latNbhd B (2 ^ (k + 2)) ∧ x₁ + tk ≤ t ∧ x₂ + tk ≤ t ∧
      ¬ SegMerge β tk w x₁ x₂ ∧ ¬ SegClosed β tk w x₁ ∧ ¬ SegClosed β tk w x₂ ∧
      ENNReal.ofReal ((3.9 : ℝ) ^ k) ≤ volume (proxSet tk w ((1.9 : ℝ) ^ k) x₁ x₂))

/-- `b_t`: the number of blocks of `ℬ_k` that are bad by time `t`. -/
noncomputable def badCount (d : ℕ) (β t₀ : ℝ) (n : ℕ) (w : ℝ → Fin d → ℤ) (t : ℝ) : ℕ :=
  {ι : Fin d → ℤ | BadByTime d β t₀ n w ι t}.ncard

/-- `Λ_t`: the union of the blocks of `ℬ_k` that are bad by time `t`. -/
def badUnion (d : ℕ) (β t₀ : ℝ) (n : ℕ) (w : ℝ → Fin d → ℤ) (t : ℝ) : Set (Fin d → ℤ) :=
  ⋃ ι ∈ {ι : Fin d → ℤ | BadByTime d β t₀ n w ι t}, heavyBlock (heavyLevel d n) ι

/-- Badness by time `t` is monotone in `t`. -/
theorem BadByTime.mono {β t₀ : ℝ} {n : ℕ} {w : ℝ → Fin d → ℤ} {ι : Fin d → ℤ} {t t' : ℝ}
    (h : BadByTime d β t₀ n w ι t) (htt : t ≤ t') : BadByTime d β t₀ n w ι t' := by
  unfold BadByTime at h ⊢
  rcases h with ⟨x, hx, h1, h2, h3, h4⟩ | ⟨x, hx, h1, h2, u, hu, h3⟩ |
    ⟨x₁, hx₁, x₂, hx₂, h1, h2, h3, h4, h5, h6, h7, h8⟩
  · exact Or.inl ⟨x, hx, h1, h2.trans htt, h3, h4⟩
  · refine Or.inr (Or.inl ⟨x, hx, h1.trans htt, h2, u, ⟨hu.1, hu.2.trans (min_le_min le_rfl
      (by linarith))⟩, h3⟩)
  · exact Or.inr (Or.inr ⟨x₁, hx₁, x₂, hx₂, h1, h2, h3.trans htt, h4.trans htt, h5, h6, h7, h8⟩)

end ElboimSly.Paper
