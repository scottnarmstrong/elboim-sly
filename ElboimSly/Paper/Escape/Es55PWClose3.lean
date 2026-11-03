/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Escape.Es55PWClose2
public import ElboimSly.Paper.Escape.EscapeTime
public import Mathlib

/-!
# Step 1 of ES22 Lemma 5.5: no closing in `(0, t']`

ES22 Lemma 5.5, Step 1, "Conclusion of Step 1": "No closing occurs in `(0, t']`: before
`ξ_B` by `𝒦(β')`; on `(ξ_B, t' - r_i)`, `Ŵ ∈ B⁻`, which excludes `0` unless `u = 0`, and then
`v = 0` and `Ŵ(kβ) ≠ v` for `kβ ∈ [β, t_*]` by `E₅₆`; on `[t' - r_i, t']`, `Ŵ` follows `η` inside
`𝒬 ∌ 0`".

* `pwc_noZero`: `Ŵ(kβ) ≠ 0` for `1 ≤ k` with `kβ ≤ t'`;
* `pwc_lt_cycTreg`: hence `t' < t_reg`;
* `pwc_zero_case`: if `0 ∈ B⁻` for an admissible block then `ξ_B = 0` and `v = 0`;
* `pwc_back_mem_Q`: `Ŵ(τ + mβ) ∈ 𝒬` for `τ ∈ [β' - r, β']`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Escape

open ElboimSly ElboimSly.Cyclic ElboimSly.Interchange ElboimSly.Paper

set_option linter.unusedSectionVars false

variable {k : ℕ} {β : ℝ} [Fact (0 < β)]

/-- **No zero of `Ŵ` at a multiple of `β` up to `t'`.**  `Wh` is the walk `Ŵ`, `Pt` the
continuation `P̃` started at `v` at the phase `ξ`, `t_* = t' - r - ξ`; `hagree` is the agreement
on `[ξ, t' - r)`, `hQ` that `Ŵ` is in `𝒬` on `[t' - r, t']` (read at `τ + mβ`, `τ ∈ [β'-r, β']`),
and `hK` that every zero at a multiple of `β` is after `ξ`. -/
theorem pwc_noZero {j : ℕ} {u v w : EscV k} {ξ tp r β' : ℝ} {m : ℤ} (Wh : ℝ → EscV k)
    {Pt : CycPath (k + 2)} (hP : PWPath β j u v w (tp - r - ξ) Pt)
    (hagree : ∀ s : ℝ≥0, (s : ℝ) < tp - r - ξ → Wh (ξ + s) = Pt.1.fn s)
    (ht' : tp = β' + m * β)
    (hQ : ∀ τ, β' - r ≤ τ → τ ≤ β' → Wh (τ + m * β) ∈ escQ j u)
    (hzQ : (0 : EscV k) ∉ escQ j u)
    (hzero : (0 : EscV k) ∈ escBlockMinus j u → ξ = 0 ∧ v = 0)
    (hK : ∀ n : ℕ, 1 ≤ n → Wh ((n : ℝ) * β) = 0 → ξ < (n : ℝ) * β) :
    ∀ n : ℕ, 1 ≤ n → (n : ℝ) * β ≤ tp → Wh ((n : ℝ) * β) ≠ 0 := by
  intro n hn hnt hz
  have hβ : 0 < β := Fact.out
  have hξ := hK n hn hz
  by_cases hc : (n : ℝ) * β < tp - r
  · -- on `(ξ, t' - r)`
    set s : ℝ≥0 := ((n : ℝ) * β - ξ).toNNReal with hs
    have hsR : (s : ℝ) = (n : ℝ) * β - ξ := Real.coe_toNNReal _ (by linarith)
    have hslt : (s : ℝ) < tp - r - ξ := by rw [hsR]; linarith
    have hag := hagree s hslt
    rw [show ξ + (s : ℝ) = (n : ℝ) * β by rw [hsR]; ring, hz] at hag
    have hmem := hP.mem s hslt.le
    rw [← hag] at hmem
    obtain ⟨hξ0, hv0⟩ := hzero hmem
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hβs : β ≤ (s : ℝ) := by rw [hsR, hξ0]; nlinarith
    exact hP.ne_v s hβs hslt.le (by rw [← hag, hv0])
  · -- on `[t' - r, t']`
    push Not at hc
    refine hzQ ?_
    have := hQ ((n : ℝ) * β - m * β) (by linarith) (by linarith)
    rw [sub_add_cancel, hz] at this
    exact this

/-- If `0 ∈ B⁻` for an admissible block and the walk starts at `0`, then `ξ_B = 0`. -/
theorem pwc_zero_case {j : ℕ} {u : EscV k} (hj : 1 ≤ j) (_hadm : EscAdmissible j u)
    (W : ℝ → EscV k) (hW0 : W 0 = 0) (hz : (0 : EscV k) ∈ escBlockMinus j u) :
    escXi W (escBlock j u) = 0 := by
  have hB : (0 : EscV k) ∈ escBlock j u := blockMinus_subset_block hj hz
  unfold escXi
  refine le_antisymm ?_ zero_le
  refine (iInf₂_le (0 : ℝ≥0) ?_).trans (by simp)
  simpa [hW0] using hB

/-- `Ŵ` is in `𝒬` on `[t' - r, t']`: from restart, the backward path before its length in `𝒬`,
and `p ∈ 𝒬`. -/
theorem pwc_back_mem_Q {j : ℕ} {u : EscV k} {μ : Measure (RingSpace (k + 2) β)} (hμ : Good μ)
    (p w : EscV k) {β' tp r : ℝ} (m : ℤ) (ht' : tp = β' + m * β) (hr : 0 ≤ r) (hrt : r < tp)
    (hη : ∃ a0 < β' - r, ∀ τ ∈ Ioo a0 (β' - r), bwdTraj hμ p β' τ = w)
    (hW : ∃ s0 < tp - r, ∀ s ∈ Ioo s0 (tp - r), fwdTraj hμ 0 0 s = w)
    (hpQ : p ∈ escQ j u)
    (hbQ : ∀ s : ℝ≥0, 0 < s → (s : ℝ) ≤ r → bwdTraj hμ p β' (β' - s) ∈ escQ j u) :
    ∀ τ, β' - r ≤ τ → τ ≤ β' → fwdTraj hμ 0 0 (τ + m * β) ∈ escQ j u := by
  intro τ h1 h2
  rw [pwc_restart hμ p w m ht' hr hrt hη hW τ h1 h2]
  rcases h2.eq_or_lt with rfl | hlt
  · rw [bwdTraj_self]; exact hpQ
  · have hs : (0 : ℝ) < β' - τ := by linarith
    have := hbQ (β' - τ).toNNReal (by rw [← NNReal.coe_pos, Real.coe_toNNReal _ hs.le]; exact hs)
      (by rw [Real.coe_toNNReal _ hs.le]; linarith)
    rwa [Real.coe_toNNReal _ hs.le, sub_sub_cancel] at this

end ElboimSly.Paper.Escape
