/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Escape.Es55PWClose3
public import ElboimSly.Paper.Escape.Es55Stmt
public import ElboimSly.Paper.Escape.InclusionRestart
public import ElboimSly.Paper.Step.RegenMeas
public import Mathlib

/-!
# Step 1 of ES22 Lemma 5.5: from no closing to `t' < t_reg`

ES22 Lemma 5.5, Step 1, "Conclusion of Step 1".

`pwc_conSet`: from the agreement of `Ŵ = W^{N¹}` with the continuation `P̃` on `[ξ_B, t' - r_i)`,
the event `E₅₆` for `P̃` (`PWPath`), `𝒦(β')`, the geometry of the backward entry (in `𝒬` before
`r_i`, exit value `w`), and the absence of rings at `p_i` at `[β']`, conclude
`t' < t_reg` and `W(t') = p_i`, i.e. `ν ∈ Con_i`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Escape

open ElboimSly ElboimSly.Cyclic ElboimSly.Interchange ElboimSly.Paper

set_option linter.unusedSectionVars false

variable {k : ℕ} {β : ℝ} [Fact (0 < β)]

/-- **`t' < t_reg`** from the absence of zeros of `Ŵ` at multiples of `β` up to `t'`. -/
theorem pwc_lt_cycTreg {μ : Measure (RingSpace k β)} {tp : ℝ} (htp : 0 ≤ tp)
    (hno : ∀ n : ℕ, 1 ≤ n → (n : ℝ) * β ≤ tp → cycWalk μ 0 0 ((n : ℝ) * β) ≠ 0) :
    ENNReal.ofReal tp < cycTreg μ := by
  have hβ : 0 < β := Fact.out
  set T : ℝ := ((⌊tp / β⌋₊ + 1 : ℕ) : ℝ) * β with hT
  have hTt : tp < T := by
    have := Nat.lt_floor_add_one (tp / β)
    rw [hT]
    have h2 : tp = tp / β * β := by field_simp
    calc tp = tp / β * β := h2
      _ < _ := by push_cast; exact mul_lt_mul_of_pos_right this hβ
  refine lt_of_lt_of_le ((ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 hTt) ?_
  unfold cycTreg
  refine le_iInf fun ⟨n, hn1, hn0⟩ => ENNReal.ofReal_le_ofReal ?_
  have hgt : tp < (n : ℝ) * β := by
    by_contra hle
    exact hno n hn1 (not_lt.1 hle) hn0
  have hn : ⌊tp / β⌋₊ < n := by
    rw [Nat.floor_lt (by positivity)]
    rw [div_lt_iff₀ hβ]; exact hgt
  rw [hT]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hn) hβ.le

end ElboimSly.Paper.Escape
