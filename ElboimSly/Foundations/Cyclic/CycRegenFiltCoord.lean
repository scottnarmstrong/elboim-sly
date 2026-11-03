/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycRegenRecordTrunc
public import ElboimSly.Foundations.Cyclic.CycRegenPiece
public import ElboimSly.Foundations.Cyclic.CycClosing
public import ElboimSly.Foundations.Cyclic.CycFastWin
public import Mathlib

/-!
# ES22 Lemma 2.1 (a): the coordinates of `Rec^{𝒫_reg}(s)` through `W`

ES22 Lemma 2.1 (a), proof: "entry `k` has datum `(k, 0, 0, +1)`, length
`ℓ = min(σ_k, s) - σ_{k-1}` and path `r ↦ W(σ_{k-1} + r ∧ ℓ)`". With
`revT ν s j = min(σ_j, s)` (the *revealed* regeneration time), for a good environment `ν` and
`j` with `σ_j ≤ s` the coordinate `j` of `Trunc_s(ρ^{𝒫_reg}(ν))` has datum `(j, 0, 0, +1)`, length
`revT (j+1) - revT j` and path `r ↦ W(revT j + r ∧ (revT (j+1) - revT j))`
(`coord_trunc_data`, `coord_trunc_len`, `coord_trunc_fn`); it is the junk entry if `σ_j > s`
(`coord_trunc_of_gt`).
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

open CycSchemeEnv

variable {d : ℕ} {β : ℝ} [Fact (0 < β)] {ν : Measure (ℕ × RingSpace d β)}

/-- The revealed regeneration time `min(σ_j, s)`. -/
noncomputable def revT (ν : Measure (ℕ × RingSpace d β)) (s : ℝ≥0) (j : ℕ) : ℝ≥0 :=
  (min (ElboimSly.regenSigma (slices ν) j) (s : ℝ≥0∞)).toNNReal

theorem cut_coe_fn {V : Type*} (q : CPath V) (ℓ r : ℝ≥0) :
    (q.cut (ℓ : ℝ≥0∞)).fn r = q.fn (min r ℓ) := by
  rw [CPath.cut_fn, ← ENNReal.coe_min, ENNReal.toNNReal_coe]

theorem regE_path (hν : CycGood ν) (k : ℕ) :
    ((regPlan d β).E (rule (regPlan d β) ν) k).path =
      (envPath ν (regionData d k)).1.cut (ElboimSly.cycTreg (cycSlice k ν)) := by
  rw [regE_eq hν k]; rfl

/-- The path of a complete piece with finite closing time. -/
theorem regE_fn_of_ne_top (hν : CycGood ν) (k : ℕ)
    (ht : ElboimSly.cycTreg (cycSlice k ν) ≠ ⊤) (r : ℝ≥0) :
    ((regPlan d β).E (rule (regPlan d β) ν) k).path.fn r =
      ElboimSly.cycWalk (cycSlice k ν) 0 0
        ((min r (ElboimSly.cycTreg (cycSlice k ν)).toNNReal : ℝ≥0) : ℝ) := by
  rw [regE_path hν k]
  conv_lhs => rw [← ENNReal.coe_toNNReal ht]
  rw [cut_coe_fn, envPath_fn_regionData hν]

/-- The path of a piece cut at `L ≤ treg`. -/
theorem cut_regE_fn (hν : CycGood ν) (k : ℕ) {L : ℝ≥0}
    (hL : (L : ℝ≥0∞) ≤ ElboimSly.cycTreg (cycSlice k ν)) (r : ℝ≥0) :
    (((regPlan d β).E (rule (regPlan d β) ν) k).cut (L : ℝ≥0∞)).path.fn r =
      ElboimSly.cycWalk (cycSlice k ν) 0 0 ((min r L : ℝ≥0) : ℝ) := by
  show (((regPlan d β).E (rule (regPlan d β) ν) k).path.cut (L : ℝ≥0∞)).fn r = _
  rw [cut_coe_fn, regE_path hν k, CPath.cut_fn, envPath_fn_regionData hν]
  congr 2
  have : (min ((min r L : ℝ≥0) : ℝ≥0∞) (ElboimSly.cycTreg (cycSlice k ν))) = ((min r L : ℝ≥0) : ℝ≥0∞) :=
    min_eq_left ((by exact_mod_cast min_le_right r L : ((min r L : ℝ≥0) : ℝ≥0∞) ≤ L).trans hL)
  rw [this, ENNReal.toNNReal_coe]

theorem coord_trunc_of_gt (hν : CycGood ν) (s : ℝ≥0) (junk : CycEntry ℕ d) {j : ℕ}
    (h : ¬ ElboimSly.regenSigma (slices ν) j ≤ (s : ℝ≥0∞)) :
    (CycRec.trunc s ((regPlan d β).envFinal ν)).coord junk j = junk := by
  unfold CycRec.coord
  rw [nth_trunc_regPlan_eq_none hν s (by
    by_contra hc
    exact h ((regenSigma_le_iff s j).2 (not_lt.1 hc)))]
  rfl

theorem coord_trunc_eq_tgt (hν : CycGood ν) (s : ℝ≥0) (junk : CycEntry ℕ d) {j : ℕ}
    (h : ElboimSly.regenSigma (slices ν) j ≤ (s : ℝ≥0∞)) :
    (CycRec.trunc s ((regPlan d β).envFinal ν)).coord junk j = tgt (regPlan d β) ν s j := by
  unfold CycRec.coord
  rw [nth_trunc_regPlan_of_le hν s ((regenSigma_le_iff s j).1 h)]
  rfl

omit [Fact (0 < β)] in
theorem revT_eq_toNNReal (s : ℝ≥0) {j : ℕ} (h : ElboimSly.regenSigma (slices ν) j ≤ (s : ℝ≥0∞)) :
    ((revT ν s j : ℝ≥0) : ℝ≥0∞) = ElboimSly.regenSigma (slices ν) j := by
  unfold revT
  rw [min_eq_left h, ENNReal.coe_toNNReal (ne_top_of_le_ne_top ENNReal.coe_ne_top h)]

omit [Fact (0 < β)] in
theorem revT_eq_self (s : ℝ≥0) {j : ℕ} (h : (s : ℝ≥0∞) < ElboimSly.regenSigma (slices ν) j) :
    revT ν s j = s := by
  unfold revT
  rw [min_eq_right h.le, ENNReal.toNNReal_coe]

/-- Length and path of the coordinate `j` of the truncated record. -/
theorem tgt_len_fn (hν : CycGood ν) (s : ℝ≥0) {j : ℕ}
    (hj : ElboimSly.regenSigma (slices ν) j ≤ (s : ℝ≥0∞)) :
    (tgt (regPlan d β) ν s j).len = ((revT ν s (j + 1) - revT ν s j : ℝ≥0) : ℝ≥0∞) ∧
    ∀ r : ℝ≥0, (tgt (regPlan d β) ν s j).path.fn r =
      ElboimSly.regenWalk (slices ν) ((revT ν s j : ℝ) +
        ((min r (revT ν s (j + 1) - revT ν s j) : ℝ≥0) : ℝ)) := by
  have hfin : ElboimSly.regenSigma (slices ν) j < ⊤ := lt_of_le_of_lt hj ENNReal.coe_lt_top
  have hg : ∀ k, Good (slices ν k) := hν
  have hrj : ((revT ν s j : ℝ≥0) : ℝ≥0∞) = ElboimSly.regenSigma (slices ν) j := revT_eq_toNNReal s hj
  have hrjR : (ElboimSly.regenSigma (slices ν) j).toReal = (revT ν s j : ℝ) := by
    rw [← hrj]; simp
  by_cases hnext : ElboimSly.regenSigma (slices ν) (j + 1) ≤ (s : ℝ≥0∞)
  · -- complete piece
    have hjN : j < ElboimSly.regenCount (slices ν) (s : ℝ) :=
      (regenSigma_le_iff s (j + 1)).1 hnext
    rw [tgt_regPlan_lt hν s hjN]
    have hsucc := regenSigma_succ (ν := slices ν) j
    have hrj1 : ((revT ν s (j + 1) : ℝ≥0) : ℝ≥0∞) = ElboimSly.regenSigma (slices ν) (j + 1) :=
      revT_eq_toNNReal s hnext
    have htreg : ElboimSly.cycTreg (cycSlice j ν) ≠ ⊤ := by
      intro h
      rw [hsucc] at hnext
      have : ElboimSly.cycTreg (slices ν j) = ⊤ := h
      rw [this, add_top] at hnext
      exact absurd hnext (by simp)
    have hdiff : revT ν s (j + 1) - revT ν s j = (ElboimSly.cycTreg (cycSlice j ν)).toNNReal := by
      have h1 : ((revT ν s (j + 1) : ℝ≥0) : ℝ≥0∞) =
          ((revT ν s j : ℝ≥0) : ℝ≥0∞) + ((ElboimSly.cycTreg (cycSlice j ν)).toNNReal : ℝ≥0∞) := by
        rw [hrj1, hrj, hsucc, ENNReal.coe_toNNReal htreg]
      have h2 : revT ν s (j + 1) = revT ν s j + (ElboimSly.cycTreg (cycSlice j ν)).toNNReal := by
        exact_mod_cast h1
      rw [h2]; exact add_tsub_cancel_left _ _
    rw [hdiff]
    refine ⟨?_, fun r => ?_⟩
    · rw [regE_len hν, ENNReal.coe_toNNReal htreg]
    · rw [regE_fn_of_ne_top hν j htreg]
      have := regenWalk_piece hg j hfin (u := ((min r (ElboimSly.cycTreg (cycSlice j ν)).toNNReal : ℝ≥0) : ℝ))
        (NNReal.coe_nonneg _) (by
          rw [ENNReal.ofReal_coe_nnreal]
          calc ((min r (ElboimSly.cycTreg (cycSlice j ν)).toNNReal : ℝ≥0) : ℝ≥0∞)
              ≤ ((ElboimSly.cycTreg (cycSlice j ν)).toNNReal : ℝ≥0∞) := by
                exact_mod_cast min_le_right _ _
            _ = ElboimSly.cycTreg (cycSlice j ν) := ENNReal.coe_toNNReal htreg)
      rw [hrjR] at this
      exact this.symm
  · -- the current piece
    have hnext' : (s : ℝ≥0∞) < ElboimSly.regenSigma (slices ν) (j + 1) := not_le.1 hnext
    have hjN : j = ElboimSly.regenCount (slices ν) (s : ℝ) := by
      have h1 := (regenSigma_le_iff s j).1 hj
      have h2 : ¬ j + 1 ≤ ElboimSly.regenCount (slices ν) (s : ℝ) := fun h =>
        hnext ((regenSigma_le_iff s (j + 1)).2 h)
      omega
    subst hjN
    rw [tgt_regPlan_last hν s, revT_eq_self s hnext']
    have hdiff : s - revT ν s (ElboimSly.regenCount (slices ν) (s : ℝ)) = regLast ν s := by
      unfold revT regLast
      rw [min_eq_left hj]
    rw [hdiff]
    refine ⟨CycEntry.len_cut _ _, fun r => ?_⟩
    rw [cut_regE_fn hν _ (regLast_le_treg s)]
    have := regenWalk_piece hg (ElboimSly.regenCount (slices ν) (s : ℝ)) hfin
      (u := ((min r (regLast ν s) : ℝ≥0) : ℝ)) (NNReal.coe_nonneg _) (by
        rw [ENNReal.ofReal_coe_nnreal]
        exact (by exact_mod_cast min_le_right _ _ : ((min r (regLast ν s) : ℝ≥0) : ℝ≥0∞) ≤
          (regLast ν s : ℝ≥0∞)).trans (regLast_le_treg s))
    rw [hrjR] at this
    exact this.symm

end ElboimSly.Cyclic

end
