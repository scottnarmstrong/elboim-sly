/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycRegenFiltCoord
public import ElboimSly.Foundations.Cyclic.CycRegenCoupleDef
public import ElboimSly.Foundations.Cyclic.CycContGlue
public import ElboimSly.Foundations.Cyclic.CycRecCoords
public import ElboimSly.Foundations.Cyclic.CycRegenLawMeas
public import Mathlib

/-!
# ES22 Lemma 2.1 (a): `W(r)`, `r ≤ s`, is a measurable function of `Rec^{𝒫_reg}(s)`

ES22 Lemma 2.1 (a), proof: "Conversely
`W(r) = ∑_k 1{Λ_{k-1} ≤ r < Λ_k} p_k(r - Λ_{k-1})` for `r < s`, and `W(s)` is the endpoint of the
last entry of `cycRec(s)`; these are measurable functions of the record."

`recWalkAt junk r ρ` reads `W(r)` off a record; it is measurable (`measurable_recWalkAt`), and
for a good environment, `recWalkAt junk r (Trunc_s ρ^{𝒫_reg}(ν)) = W(r)` for `r ≤ s`
(`recWalkAt_trunc_regPlan`).
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

open CycSchemeEnv

set_option linter.unusedSectionVars false

variable {d : ℕ}

/-- The cumulative lengths, with `⊤` for the nonexistent entries. -/
noncomputable def cumTop (ρ : CycRec ℕ d) (k : ℕ) : ℝ≥0∞ :=
  open scoped Classical in
  if (k : ℕ∞) < ρ.num then ρ.cum k else ⊤

/-- `W(r)` read off a record: the value at local time `r - Λ` of the entry `N` with
`N = max {k < num : Λ_k ≤ r}`. -/
noncomputable def recWalkAt (junk : CycEntry ℕ d) (r : ℝ≥0) (ρ : CycRec ℕ d) : Fin d → ℤ :=
  (ρ.coord junk (gluedCount (cumTop ρ) r)).path.fn
    (r - (cumTop ρ (gluedCount (cumTop ρ) r)).toNNReal)

theorem measurable_cumTop (junk : CycEntry ℕ d) (k : ℕ) : Measurable fun ρ : CycRec ℕ d => cumTop ρ k := by
  classical
  unfold cumTop
  refine Measurable.ite ?_ (measurable_cum junk k) measurable_const
  exact CycRec.measurable_num (MeasurableSet.of_discrete (s := {x : ℕ∞ | (k : ℕ∞) < x}))

theorem measurable_recWalkAt (junk : CycEntry ℕ d) (r : ℝ≥0) :
    Measurable (recWalkAt junk r) := by
  have hσ : ∀ n, Measurable fun ρ : CycRec ℕ d => cumTop ρ n := measurable_cumTop junk
  have hF : ∀ k, Measurable fun ρ : CycRec ℕ d =>
      (ρ.coord junk k).path.fn (r - (cumTop ρ k).toNNReal) := fun k =>
    measurable_fn_at (fun ρ : CycRec ℕ d => (ρ.coord junk k).path)
      (measurable_entry_path.comp (CycRec.measurable_coord junk k)) _
      (measurable_const.sub (ENNReal.measurable_toNNReal.comp (hσ k)))
  exact measurable_index (measurable_gluedCount_of hσ r) hF

variable {β : ℝ} [Fact (0 < β)] {ν : Measure (ℕ × RingSpace d β)}

theorem cum_trunc_regPlan (hν : CycGood ν) (s : ℝ≥0) {k : ℕ}
    (hk : k ≤ ElboimSly.regenCount (slices ν) (s : ℝ)) :
    (CycRec.trunc s ((regPlan d β).envFinal ν)).cum k = ElboimSly.regenSigma (slices ν) k := by
  unfold CycRec.cum ElboimSly.regenSigma
  refine Finset.sum_congr rfl fun i hi => ?_
  have hik : i < ElboimSly.regenCount (slices ν) (s : ℝ) := lt_of_lt_of_le (Finset.mem_range.1 hi) hk
  unfold CycRec.lenAt
  rw [nth_trunc_regPlan_of_le hν s hik.le, tgt_regPlan_lt hν s hik]
  exact regE_len hν i

theorem cumTop_trunc_regPlan (hν : CycGood ν) (s : ℝ≥0) (k : ℕ) :
    cumTop (CycRec.trunc s ((regPlan d β).envFinal ν)) k =
      if k ≤ ElboimSly.regenCount (slices ν) (s : ℝ) then ElboimSly.regenSigma (slices ν) k
      else ⊤ := by
  classical
  unfold cumTop
  rw [num_trunc_regPlan hν s]
  by_cases h : k ≤ ElboimSly.regenCount (slices ν) (s : ℝ)
  · rw [ite_eq_left (by exact_mod_cast Nat.lt_succ_of_le h), ite_eq_left h]
    exact cum_trunc_regPlan hν s h
  · rw [ite_eq_right (by exact_mod_cast (by omega : ¬ k < ElboimSly.regenCount (slices ν) (s : ℝ) + 1)),
      ite_eq_right h]

theorem recWalkAt_trunc_regPlan (hν : CycGood ν) (s : ℝ≥0) (junk : CycEntry ℕ d) {r : ℝ≥0}
    (hr : r ≤ s) :
    recWalkAt junk r (CycRec.trunc s ((regPlan d β).envFinal ν)) = regW ν r := by
  classical
  set σ := cumTop (CycRec.trunc s ((regPlan d β).envFinal ν)) with hσ
  set N := ElboimSly.regenCount (slices ν) (s : ℝ) with hN
  set n := ElboimSly.regenCount (slices ν) (r : ℝ) with hn
  have hrσ : ENNReal.ofReal (r : ℝ) = (r : ℝ≥0∞) := ENNReal.ofReal_coe_nnreal
  have hnN : n ≤ N := by
    have h1 := (le_regenCount_iff (slices ν) (NNReal.coe_nonneg r) n).1 le_rfl
    have : ElboimSly.regenSigma (slices ν) n ≤ (s : ℝ≥0∞) :=
      h1.trans (hrσ.le.trans (ENNReal.coe_le_coe.2 hr))
    exact (regenSigma_le_iff s n).1 this
  have hσk : ∀ k, σ k = if k ≤ N then ElboimSly.regenSigma (slices ν) k else ⊤ :=
    cumTop_trunc_regPlan hν s
  have hmono : Monotone σ := by
    intro a b hab
    rw [hσk a, hσk b]
    by_cases hb : b ≤ N
    · rw [ite_eq_left hb, ite_eq_left (hab.trans hb)]; exact regenSigma_mono (slices ν) hab
    · rw [ite_eq_right hb]; exact le_top
  have hcnt : gluedCount σ r = n := by
    refine gluedCount_eq hmono ?_ ?_
    · rw [hσk, ite_eq_left hnN, ← hrσ]; exact (regenSigma_count (slices ν) (NNReal.coe_nonneg r)).1
    · rw [hσk, ← hrσ]
      split_ifs with h
      · exact (regenSigma_count (slices ν) (NNReal.coe_nonneg r)).2
      · exact ENNReal.ofReal_lt_top
  unfold recWalkAt
  rw [hcnt]
  have hsn : ElboimSly.regenSigma (slices ν) n ≤ (r : ℝ≥0∞) := by
    have := (regenSigma_count (slices ν) (NNReal.coe_nonneg r)).1
    rwa [hrσ] at this
  have hsns : ElboimSly.regenSigma (slices ν) n ≤ (s : ℝ≥0∞) := hsn.trans (by exact_mod_cast hr)
  have hσn : cumTop (CycRec.trunc s ((regPlan d β).envFinal ν)) n =
      ElboimSly.regenSigma (slices ν) n := by
    have := hσk n
    rw [ite_eq_left hnN] at this
    exact this
  rw [coord_trunc_eq_tgt hν s junk hsns, (tgt_len_fn hν s hsns).2, hσn]
  have hrev : ((revT ν s n : ℝ≥0) : ℝ≥0∞) = ElboimSly.regenSigma (slices ν) n :=
    revT_eq_toNNReal s hsns
  have hnext : (r : ℝ≥0∞) < ElboimSly.regenSigma (slices ν) (n + 1) := by
    have := (regenSigma_count (slices ν) (NNReal.coe_nonneg r)).2
    rwa [hrσ] at this
  have hrle : r ≤ revT ν s (n + 1) := by
    unfold revT
    rw [← ENNReal.coe_le_coe, ENNReal.coe_toNNReal (ne_top_of_le_ne_top ENNReal.coe_ne_top
      (min_le_right _ _))]
    exact le_min hnext.le (by exact_mod_cast hr)
  have hsnr : revT ν s n ≤ r := by
    have : ((revT ν s n : ℝ≥0) : ℝ≥0∞) ≤ r := hrev ▸ hsn
    exact_mod_cast this
  have hu : r - (ElboimSly.regenSigma (slices ν) n).toNNReal = r - revT ν s n := by
    rw [← hrev, ENNReal.toNNReal_coe]
  rw [hu, min_eq_left (tsub_le_tsub_right hrle _)]
  rw [regW_eq_regenWalk hν]
  congr 1
  rw [← NNReal.coe_add, add_tsub_cancel_of_le hsnr]

end ElboimSly.Cyclic

end
