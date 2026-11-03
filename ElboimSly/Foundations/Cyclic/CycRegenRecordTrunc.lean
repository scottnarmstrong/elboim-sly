/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycRegenRecordPiece
public import Mathlib

/-!
# ES22 Lemma 2.1: the truncated record at time `t`

ES22 Lemma 2.1, proof, "Freezing". For a good environment `ν`, `t ≥ 0`,
`k = regenCount`, `L = t - α(t)`: the record `Trunc_t(ρ^{𝒫_reg}(ν))` has `k + 1` entries, entry `i`
is the complete piece `i` for `i < k` and entry `k` is piece `k` cut at `L`
(`num_trunc_regPlan`, `coord_trunc_regPlan_last`). Its region meets copy `k` in `ℛ_{(0,L]}(w)`
and no later copy (`preimage_region_trunc_last`, `preimage_region_trunc_gt`).
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

open CycSchemeEnv

variable {d : ℕ} {β : ℝ} [Fact (0 < β)] {ν : Measure (ℕ × RingSpace d β)}

/-- `L = t - α(t)` as a nonnegative real. -/
noncomputable def regLast (ν : Measure (ℕ × RingSpace d β)) (t : ℝ≥0) : ℝ≥0 :=
  t - (ElboimSly.regenSigma (slices ν) (ElboimSly.regenCount (slices ν) (t : ℝ))).toNNReal

theorem regLast_coe (t : ℝ≥0) :
    (regLast ν t : ℝ) = (t : ℝ) - ElboimSly.regenStart (slices ν) (t : ℝ) := by
  have hle := (regenSigma_count (slices ν) t.2).1
  have hfin := regenSigma_count_lt_top (slices ν) t.2
  have : (ElboimSly.regenSigma (slices ν) (ElboimSly.regenCount (slices ν) (t : ℝ))).toNNReal ≤ t := by
    have h2 : ElboimSly.regenSigma (slices ν) (ElboimSly.regenCount (slices ν) (t : ℝ)) ≤ t := by
      simpa using hle
    simpa using ENNReal.toNNReal_mono ENNReal.coe_ne_top h2
  unfold regLast ElboimSly.regenStart
  rw [NNReal.coe_sub this]
  rfl

theorem coe_sub_sigma (t : ℝ≥0) :
    (t : ℝ≥0∞) - ElboimSly.regenSigma (slices ν) (ElboimSly.regenCount (slices ν) (t : ℝ)) =
      (regLast ν t : ℝ≥0∞) := by
  have hfin := regenSigma_count_lt_top (slices ν) t.2
  have hle : (ElboimSly.regenSigma (slices ν) (ElboimSly.regenCount (slices ν) (t : ℝ))).toNNReal ≤ t := by
    have h2 : ElboimSly.regenSigma (slices ν) (ElboimSly.regenCount (slices ν) (t : ℝ)) ≤ t := by
      simpa using (regenSigma_count (slices ν) t.2).1
    simpa using ENNReal.toNNReal_mono ENNReal.coe_ne_top h2
  unfold regLast
  rw [ENNReal.coe_sub]
  congr 1
  exact (ENNReal.coe_toNNReal hfin.ne).symm

theorem regLast_le_treg (t : ℝ≥0) :
    (regLast ν t : ℝ≥0∞) ≤
      ElboimSly.cycTreg (cycSlice (ElboimSly.regenCount (slices ν) (t : ℝ)) ν) := by
  have h := ofReal_sub_regenStart_lt (slices ν) t.2
  have h2 : ENNReal.ofReal (regLast ν t : ℝ) <
      ElboimSly.cycTreg (slices ν (ElboimSly.regenCount (slices ν) (t : ℝ))) := by
    rw [regLast_coe]; exact h
  rw [ENNReal.ofReal_coe_nnreal] at h2
  exact h2.le

theorem tgt_regPlan_lt (hν : CycGood ν) (t : ℝ≥0) {k : ℕ}
    (hk : k < ElboimSly.regenCount (slices ν) (t : ℝ)) :
    tgt (regPlan d β) ν t k = (regPlan d β).E (rule (regPlan d β) ν) k := by
  unfold tgt
  rw [ite_eq_left]
  rw [lam_regPlan hν, regE_len hν]
  have : ElboimSly.regenSigma (slices ν) (k + 1) ≤ (t : ℝ≥0∞) :=
    (regenSigma_le_iff t (k + 1)).2 hk
  rwa [regenSigma_succ] at this

theorem tgt_regPlan_last (hν : CycGood ν) (t : ℝ≥0) :
    tgt (regPlan d β) ν t (ElboimSly.regenCount (slices ν) (t : ℝ)) =
      ((regPlan d β).E (rule (regPlan d β) ν)
        (ElboimSly.regenCount (slices ν) (t : ℝ))).cut (regLast ν t : ℝ≥0∞) := by
  unfold tgt
  rw [ite_eq_right]
  · rw [lam_regPlan hν, coe_sub_sigma]
  · rw [lam_regPlan hν, regE_len hν]
    intro h
    have : ElboimSly.regenSigma (slices ν) (ElboimSly.regenCount (slices ν) (t : ℝ) + 1) ≤
        (t : ℝ≥0∞) := by
      rwa [regenSigma_succ]
    have := (regenSigma_le_iff t _).1 this
    omega

theorem nth_trunc_regPlan_eq_none (hν : CycGood ν) (t : ℝ≥0) {k : ℕ}
    (hk : ElboimSly.regenCount (slices ν) (t : ℝ) < k) :
    (CycRec.trunc t ((regPlan d β).envFinal ν)).nth k = none := by
  rw [trunc_regPlan_nth hν, ite_eq_right]
  intro h
  have := (regenSigma_le_iff t k).1 h
  omega

theorem nth_trunc_regPlan_of_le (hν : CycGood ν) (t : ℝ≥0) {k : ℕ}
    (hk : k ≤ ElboimSly.regenCount (slices ν) (t : ℝ)) :
    (CycRec.trunc t ((regPlan d β).envFinal ν)).nth k = some (tgt (regPlan d β) ν t k) := by
  rw [trunc_regPlan_nth hν, ite_eq_left]
  exact (regenSigma_le_iff t k).2 hk

theorem num_trunc_regPlan (hν : CycGood ν) (t : ℝ≥0) :
    (CycRec.trunc t ((regPlan d β).envFinal ν)).num =
      ((ElboimSly.regenCount (slices ν) (t : ℝ) + 1 : ℕ) : ℕ∞) := by
  set N := ElboimSly.regenCount (slices ν) (t : ℝ)
  set ρ := CycRec.trunc t ((regPlan d β).envFinal ν)
  apply le_antisymm
  · by_contra h
    rw [not_le] at h
    obtain ⟨e, he⟩ := nth_of_lt_num (ρ' := ρ) (k := N + 1) (by exact_mod_cast h)
    rw [nth_trunc_regPlan_eq_none hν t (Nat.lt_succ_self N)] at he
    exact absurd he (by simp)
  · have h := lt_num_of_nth (nth_trunc_regPlan_of_le hν t (le_refl N))
    exact Order.add_one_le_of_lt h

theorem coord_trunc_regPlan_last (hν : CycGood ν) (t : ℝ≥0) (junk : CycEntry ℕ d) :
    (CycRec.trunc t ((regPlan d β).envFinal ν)).coord junk
        (ElboimSly.regenCount (slices ν) (t : ℝ)) =
      ((regPlan d β).E (rule (regPlan d β) ν)
        (ElboimSly.regenCount (slices ν) (t : ℝ))).cut (regLast ν t : ℝ≥0∞) := by
  unfold CycRec.coord
  rw [nth_trunc_regPlan_of_le hν t le_rfl, tgt_regPlan_last hν]
  rfl

theorem mem_region_trunc_iff (hν : CycGood ν) (t : ℝ≥0) (x : ℕ × RingSpace d β) :
    x ∈ (CycRec.trunc t ((regPlan d β).envFinal ν)).region β ↔
      ∃ k ≤ ElboimSly.regenCount (slices ν) (t : ℝ), x ∈ (tgt (regPlan d β) ν t k).region β := by
  constructor
  · rintro ⟨e, ⟨k, hk⟩, hx⟩
    by_cases hkN : k ≤ ElboimSly.regenCount (slices ν) (t : ℝ)
    · rw [nth_trunc_regPlan_of_le hν t hkN] at hk
      cases hk
      exact ⟨k, hkN, hx⟩
    · rw [nth_trunc_regPlan_eq_none hν t (not_le.1 hkN)] at hk
      exact absurd hk (by simp)
  · rintro ⟨k, hk, hx⟩
    exact ⟨_, ⟨k, nth_trunc_regPlan_of_le hν t hk⟩, hx⟩

/-- The region of the truncated record in copy `k_t` is `ℛ_{(0,L]}(w)`. -/
theorem preimage_region_trunc_last (hν : CycGood ν) (t : ℝ≥0) :
    Prod.mk (ElboimSly.regenCount (slices ν) (t : ℝ)) ⁻¹'
        (CycRec.trunc t ((regPlan d β).envFinal ν)).region β =
      cycRegion β (fun s => ElboimSly.cycWalk
        (cycSlice (ElboimSly.regenCount (slices ν) (t : ℝ)) ν) 0 0 s) 0 (regLast ν t : ℝ) := by
  set N := ElboimSly.regenCount (slices ν) (t : ℝ)
  ext y
  simp only [mem_preimage, mem_region_trunc_iff hν]
  constructor
  · rintro ⟨k, hk, hx⟩
    rcases hk.lt_or_eq with hlt | rfl
    · rw [tgt_regPlan_lt hν t hlt] at hx
      have := region_regE_subset hν k hx
      simp at this
      omega
    · rw [tgt_regPlan_last hν, region_cut_regE hν _ (regLast_le_treg t)] at hx
      exact (mem_prod.1 hx).2
  · intro hy
    refine ⟨N, le_rfl, ?_⟩
    rw [tgt_regPlan_last hν, region_cut_regE hν _ (regLast_le_treg t)]
    exact ⟨rfl, hy⟩

/-- The region of the truncated record does not meet the copies after `k_t`. -/
theorem preimage_region_trunc_gt (hν : CycGood ν) (t : ℝ≥0) {j : ℕ}
    (hj : ElboimSly.regenCount (slices ν) (t : ℝ) < j) :
    Prod.mk j ⁻¹' (CycRec.trunc t ((regPlan d β).envFinal ν)).region β = ∅ := by
  ext y
  simp only [mem_preimage, mem_region_trunc_iff hν, mem_empty_iff_false, iff_false]
  rintro ⟨k, hk, hx⟩
  rcases hk.lt_or_eq with hlt | rfl
  · rw [tgt_regPlan_lt hν t hlt] at hx
    have := region_regE_subset hν k hx
    simp at this
    omega
  · rw [tgt_regPlan_last hν, region_cut_regE hν _ (regLast_le_treg t)] at hx
    have := (mem_prod.1 hx).1
    simp at this
    omega

end ElboimSly.Cyclic

end
