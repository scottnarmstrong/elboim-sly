/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Frozen.Defs.IndDelta
public import ElboimSly.Paper.Heavy.CyclicPath

/-!
# The sets `U₁`, `U₂`

The sets U_1, U_2 (ES22 proof of Lemma 6.8, ES22 §6; deviation F61).

For a time `t` and a length `r` (`= t'_k` in the source), `t⋆ := max (CI_β ∩ [0, t - r])`
(`heavyTStar`), so `t - r - 1 < t⋆ ≤ t - r`, and

* `U₁ = {s ∈ [t - r, t] ∩ [t⋆, t⋆ + r] : s is relaxed with respect to w|[t⋆, s]}`,
* `U₂ = {s ∈ [t⋆, t] : ‖w s - w s'‖ > t_n ^ δ for all s' ∈ [0, t⋆)}`.
-/

@[expose] public section

open Set

namespace ElboimSly.Paper

variable {d : ℕ}

/-- The sets U_1, U_2. `t⋆ = max (CI_β ∩ [0, t - r])`. -/
noncomputable def heavyTStar (β r t : ℝ) : ℝ := cycFloor β (t - r)

/-- The sets U_1, U_2. `U₁`. -/
def heavyU1 (β r : ℝ) (w : ℝ → Fin d → ℤ) (t : ℝ) : Set ℝ :=
  {s | s ∈ Icc (t - r) t ∩ Icc (heavyTStar β r t) (heavyTStar β r t + r) ∧
    IsRelaxedTimeWrt β w (heavyTStar β r t) s}

/-- The sets U_1, U_2. `U₂`, with `tn = t_n` and the exponent `δ = indDelta d`. -/
noncomputable def heavyU2 (β r tn : ℝ) (w : ℝ → Fin d → ℤ) (t : ℝ) : Set ℝ :=
  {s | s ∈ Icc (heavyTStar β r t) t ∧
    ∀ s' ∈ Ico 0 (heavyTStar β r t), tn ^ indDelta d < ‖w s - w s'‖}

theorem heavyTStar_mem {β r t : ℝ} (hβ : 0 < β) (h : r ≤ t) :
    heavyTStar β r t ∈ cycIntTimes β :=
  cycFloor_mem hβ (by linarith)

theorem heavyTStar_le {β r t : ℝ} (hβ : 0 < β) : heavyTStar β r t ≤ t - r :=
  cycFloor_le hβ

theorem lt_heavyTStar_add_one {β r t : ℝ} (hβ : 0 < β) : t - r - 1 < heavyTStar β r t := by
  have := lt_cycFloor_add_one (x := t - r) hβ
  unfold heavyTStar; linarith

theorem heavyU1_subset {β r : ℝ} {w : ℝ → Fin d → ℤ} {t : ℝ} :
    heavyU1 β r w t ⊆ Icc (t - r) t := fun _ hs => hs.1.1

end ElboimSly.Paper
