/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Escape.Es52Refl2
public import ElboimSly.Foundations.Cyclic.CycRegenRecordTrunc
public import ElboimSly.Foundations.Cyclic.CycMultiRecStop
public import Mathlib

/-!
# ES22 Proposition 5.2, Step 2: the explored region of `ρ^{reg}_t` and `ρ^{reg}_T` is equivariant

ES22 Proposition 5.2 Step 2, "covariance of trajectories(a) applied to each piece".  For `ν` good,
`region (Trunc_t ρ^{reg}(h_*ν)) = Ψ⁻¹ (region (Trunc_t ρ^{reg}(ν)))` where `Ψ = psiE`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Escape

open ElboimSly ElboimSly.Cyclic ElboimSly.Cyclic.CycSchemeEnv ElboimSly.Interchange
  ElboimSly.Paper

variable {k : ℕ} {β : ℝ} [Fact (0 < β)] {ν : Measure (ℕ × RingSpace (k + 2) β)}

omit [Fact (0 < β)] in
theorem region_cut_self (e : CycEntry ℕ (k + 2)) (L : ℝ≥0) (h : e.len = L) :
    (e.cut (L : ℝ≥0∞)).region β = e.region β := by
  ext x
  simp only [CycEntry.region, mem_ofPred_eq]
  rw [CycEntry.len_cut, h, CycEntry.data_cut]
  refine exists_congr fun r => and_congr_right fun hr => and_congr_right fun hrL => ?_
  rw [CycEntry.path_cut, CPath.left_cut _ _ hr hrL]

/-- The time at which piece `k'` is cut in `Trunc_t ρ^{reg}(ν)`. -/
noncomputable def pieceL (ν : Measure (ℕ × RingSpace (k + 2) β)) (t : ℝ≥0) (k' : ℕ) : ℝ≥0 :=
  if k' < ElboimSly.regenCount (slices ν) (t : ℝ) then
    (ElboimSly.cycTreg (cycSlice k' ν)).toNNReal
  else regLast ν t

theorem region_tgt (hν : CycGood ν) (t : ℝ≥0) {k' : ℕ}
    (hk' : k' ≤ ElboimSly.regenCount (slices ν) (t : ℝ)) :
    (tgt (regPlan (k + 2) β) ν t k').region β =
      {k'} ×ˢ cycRegion β (fun s => ElboimSly.cycWalk (cycSlice k' ν) 0 0 s) 0
        (pieceL ν t k' : ℝ) := by
  rcases hk'.lt_or_eq with hlt | heq
  · have hfin : ElboimSly.cycTreg (cycSlice k' ν) ≠ ⊤ := by
      have h1 : ElboimSly.regenSigma (slices ν) (k' + 1) ≤ (t : ℝ≥0∞) :=
        (regenSigma_le_iff t (k' + 1)).2 hlt
      rw [regenSigma_succ] at h1
      exact ne_top_of_le_ne_top ENNReal.coe_ne_top (le_trans le_add_self h1)
    have hLe : ((ElboimSly.cycTreg (cycSlice k' ν)).toNNReal : ℝ≥0∞) =
        ElboimSly.cycTreg (cycSlice k' ν) := ENNReal.coe_toNNReal hfin
    have hpl : pieceL ν t k' = (ElboimSly.cycTreg (cycSlice k' ν)).toNNReal := by
      unfold pieceL; rw [ite_eq_left hlt]
    rw [tgt_regPlan_lt hν t hlt, hpl, ← region_cut_self _ (ElboimSly.cycTreg (cycSlice k' ν)).toNNReal
      (by rw [regE_len hν, ← hLe]; rfl)]
    exact region_cut_regE hν k' hLe.le
  · subst heq
    have hpl : pieceL ν t (ElboimSly.regenCount (slices ν) (t : ℝ)) = regLast ν t := by
      unfold pieceL; rw [ite_eq_right (lt_irrefl _)]
    rw [tgt_regPlan_last hν, hpl]
    exact region_cut_regE hν _ (regLast_le_treg t)

omit [Fact (0 < β)] in
theorem cycSlice_envMap_refl (ν : Measure (ℕ × RingSpace (k + 2) β)) (k' : ℕ) :
    cycSlice k' (envMap (reflAut k) ν) = latticeMeasure (reflAut k) (cycSlice k' ν) :=
  cycSlice_envMap _ _ _

theorem treg_envMap (hν : CycGood ν) (k' : ℕ) :
    ElboimSly.cycTreg (cycSlice k' (envMap (reflAut k) ν)) =
      ElboimSly.cycTreg (cycSlice k' ν) := by
  rw [cycSlice_envMap_refl]
  exact cycTreg_latticeMeasure (hν k') _ reflAut_zero

theorem regenSigma_envMap (hν : CycGood ν) (i : ℕ) :
    ElboimSly.regenSigma (slices (envMap (reflAut k) ν)) i =
      ElboimSly.regenSigma (slices ν) i := by
  unfold ElboimSly.regenSigma
  exact Finset.sum_congr rfl fun j _ => treg_envMap hν j

theorem regenCount_envMap (hν : CycGood ν) (t : ℝ) :
    ElboimSly.regenCount (slices (envMap (reflAut k) ν)) t = ElboimSly.regenCount (slices ν) t := by
  unfold ElboimSly.regenCount
  simp only [regenSigma_envMap hν]

theorem regLast_envMap (hν : CycGood ν) (t : ℝ≥0) :
    regLast (envMap (reflAut k) ν) t = regLast ν t := by
  unfold regLast
  rw [regenSigma_envMap hν, regenCount_envMap hν]

theorem pieceL_envMap (hν : CycGood ν) (t : ℝ≥0) (k' : ℕ) :
    pieceL (envMap (reflAut k) ν) t k' = pieceL ν t k' := by
  unfold pieceL
  rw [regenCount_envMap hν, regLast_envMap hν, treg_envMap hν]

theorem cycRegion_walk_envMap (hν : CycGood ν) (k' : ℕ) (L : ℝ≥0) :
    cycRegion β (fun s => ElboimSly.cycWalk (cycSlice k' (envMap (reflAut k) ν)) 0 0 s) 0 (L : ℝ) =
      rR k β ⁻¹' cycRegion β (fun s => ElboimSly.cycWalk (cycSlice k' ν) 0 0 s) 0 (L : ℝ) := by
  rw [← cycRegion_refl]
  refine cycRegion_congr fun t ht => ?_
  rw [cycSlice_envMap_refl]
  exact cycWalk_latticeMeasure_real (hν k') _ reflAut_zero ht.1

theorem region_tgt_envMap (hν : CycGood ν) (t : ℝ≥0) {k' : ℕ}
    (hk' : k' ≤ ElboimSly.regenCount (slices ν) (t : ℝ)) :
    (tgt (regPlan (k + 2) β) (envMap (reflAut k) ν) t k').region β =
      psiE k β ⁻¹' (tgt (regPlan (k + 2) β) ν t k').region β := by
  have hν' : CycGood (envMap (reflAut k) ν) := cycGood_envMap_of hν
  rw [region_tgt hν' t (by rwa [regenCount_envMap hν]), region_tgt hν t hk', pieceL_envMap hν,
    cycRegion_walk_envMap hν]
  ext ⟨a, e, θ⟩
  simp [psiE_apply, rR_apply]

theorem region_trunc_envMap (hν : CycGood ν) (t : ℝ≥0) (x : ℕ × RingSpace (k + 2) β) :
    x ∈ (CycRec.trunc t ((regPlan (k + 2) β).envFinal (envMap (reflAut k) ν))).region β ↔
      psiE k β x ∈ (CycRec.trunc t ((regPlan (k + 2) β).envFinal ν)).region β := by
  have hν' : CycGood (envMap (reflAut k) ν) := cycGood_envMap_of hν
  rw [mem_region_trunc_iff hν', mem_region_trunc_iff hν, regenCount_envMap hν]
  refine exists_congr fun k' => and_congr_right fun hk' => ?_
  rw [region_tgt_envMap hν t hk']
  rfl

end ElboimSly.Paper.Escape
