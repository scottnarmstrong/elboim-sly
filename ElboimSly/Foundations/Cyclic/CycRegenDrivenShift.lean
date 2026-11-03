/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycRegenDrivenPieces
public import Mathlib

/-!
# The shift identity for the regenerated driven walk

ES22 Lemma 2.1 (b), first step: for `y = x^{(n+1)}`,
`W^x_reg(σ_n + r) = W^y_reg(r)` for all `r ≥ 0`, and the last regeneration time at or before
`t = σ_n + t'` (for `t' < treg^y`) is `σ_n`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

variable {d : ℕ} {b : ℝ≥0} {x : ℝ≥0 → Fin d → ℤ}

theorem bdd_sigma (hb : 0 < b) (x : ℝ≥0 → Fin d → ℤ) (t : ℝ≥0) :
    BddAbove {k : ℕ | drivenSigma b x k ≤ t} := by
  obtain ⟨N, hN⟩ := exists_lt_nsmul hb t
  refine ⟨N, fun k hk => ?_⟩
  by_contra hkN
  rw [not_le] at hkN
  have h1 := sum_ge_nsmul (τ := fun k => drivenTreg b (drivenPieces b x k)) (b := b)
    (fun k => le_pathTreg b _) k
  have h2 : ((k : ℝ≥0) * b : ℝ≥0) ≤ t := by
    have : ((k : ℝ≥0) * b : ℝ≥0) ≤ (t : ℝ≥0∞) := by
      calc (((k : ℝ≥0) * b : ℝ≥0) : ℝ≥0∞) = (k : ℝ≥0∞) * b := by push_cast; rfl
        _ ≤ _ := h1
        _ ≤ t := hk
    exact_mod_cast this
  have h3 : (N : ℝ≥0) * b ≤ k * b := mul_le_mul_of_nonneg_right (by exact_mod_cast hkN.le) zero_le
  rw [nsmul_eq_mul] at hN
  exact absurd (lt_of_lt_of_le hN h3) (not_lt.2 h2)

theorem gluedCount_spec' (hb : 0 < b) (x : ℝ≥0 → Fin d → ℤ) (t : ℝ≥0) :
    drivenSigma b x (gluedCount (drivenSigma b x) t) ≤ t ∧
      (t : ℝ≥0∞) < drivenSigma b x (gluedCount (drivenSigma b x) t + 1) :=
  gluedCount_spec (drivenSigma_zero b x) (bdd_sigma hb x t)

/-- `W^x_reg(σ_n + r) = W^y_reg(r)` for `y = x^{(n+1)}` (written proof (b), the shift identity). -/
theorem drivenRegenFrom_shift (hb : 0 < b) {n : ℕ} (hn : drivenSigma b x n < ⊤) (r : ℝ≥0) :
    drivenRegenFrom b x ((drivenSigma b x n).toNNReal + r) =
      drivenRegenFrom b (drivenPieces b x n) r := by
  set y := drivenPieces b x n with hy
  set a := (drivenSigma b x n).toNNReal with ha
  have hna : drivenSigma b x n = (a : ℝ≥0∞) := (ENNReal.coe_toNNReal hn.ne).symm
  obtain ⟨hm1, hm2⟩ := gluedCount_spec' hb y r
  set m := gluedCount (drivenSigma b y) r with hm
  have hmfin : drivenSigma b y m < ⊤ := lt_of_le_of_lt hm1 ENNReal.coe_lt_top
  have hcnt : gluedCount (drivenSigma b x) (a + r) = n + m := by
    refine gluedCount_eq (drivenSigma_mono b x) ?_ ?_
    · rw [drivenSigma_add, hna]
      push_cast
      exact add_le_add le_rfl hm1
    · rw [show n + m + 1 = n + (m + 1) from rfl, drivenSigma_add, hna]
      push_cast
      exact ENNReal.add_lt_add_left (by simp) hm2
  have hV : ∀ (z : ℝ≥0 → Fin d → ℤ) (s : ℝ≥0), drivenRegenFrom b z s =
      drivenWalk b (drivenPieces b z (gluedCount (drivenSigma b z) s))
        (s - (drivenSigma b z (gluedCount (drivenSigma b z) s)).toNNReal) := fun z s => rfl
  rw [hV x, hV y, hcnt, ← hm, drivenPieces_add, drivenSigma_add, hna,
    ENNReal.toNNReal_add ENNReal.coe_ne_top hmfin.ne, ENNReal.toNNReal_coe,
    add_tsub_add_eq_tsub_left]

/-- Right after `treg^x` (and at it), the regenerated walk is `0`, equal to `w^x(treg^x)`. -/
theorem drivenRegenFrom_eq_walk_of_le (hb : 0 < b) (hx : IsRegPath x) {s : ℝ≥0}
    (hs : (s : ℝ≥0∞) ≤ drivenTreg b x) : drivenRegenFrom b x s = drivenWalk b x s := by
  rcases hs.lt_or_eq with h | h
  · exact drivenRegenFrom_of_lt b x h
  · obtain ⟨j, -, hj, hz⟩ := pathTreg_exists (b := b) (w := drivenWalk b x)
      (show drivenTreg b x < ⊤ from h ▸ ENNReal.coe_lt_top)
    have hτ : drivenTreg b x = (s : ℝ≥0∞) := h.symm
    obtain ⟨ε, hε, hεV⟩ := drivenRegenFrom_after b hb hx hτ
    have h0 := hεV 0 hε
    rw [add_zero] at h0
    rw [h0]
    have : (s : ℝ≥0∞) = (((j : ℝ≥0) * b : ℝ≥0) : ℝ≥0∞) := h.trans hj
    have hs' : s = (j : ℝ≥0) * b := by exact_mod_cast this
    rw [hs']; exact hz.symm

end ElboimSly.Cyclic

end
