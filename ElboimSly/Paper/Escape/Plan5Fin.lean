/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Escape.LamStopping
public import ElboimSly.Paper.Escape.Plan5
public import Mathlib

/-!
# Every walk of the plans `𝒫₅` and `𝒫_𝒜` has finite length

The connecting plan; The walks W_i and the stopping times tau_i ("`τ_i ≤ 4^n`", "a.s. finite stopping times").

`stopLen_le_of_dl_le`: if the deadline of a plan never exceeds `R - (current length)`, the stopping
length is at most `R`.  Hence `PlanFin` for `plan5` and `planA`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Escape

open ElboimSly.Cyclic ElboimSly.Cyclic.CycSchemeEnv ElboimSly ElboimSly.Paper

set_option linter.unusedSectionVars false

section generic

variable {I : Type*} [MeasurableSpace I] {d : ℕ} {β : ℝ} [Fact (0 < β)]

/-- A deadline bound `dl ≤ R - len` bounds the stopping length by `R`. -/
theorem stopLen_le_of_dl_le (P : CycPlan I d β) (k : ℕ) (ρ : CycRecN I d k) (p : CycPath d)
    {R : ℝ≥0∞} (hR : R ≠ ⊤)
    (hdl : ∀ ρ' : CycRecN I d (k + 1), P.dl k ρ' ≤ R - (ρ' (Fin.last k)).len) :
    P.stopLen k ρ p ≤ R := by
  lift R to ℝ≥0 using hR with B
  set a := p.1.cnt B with ha
  have hjt_le : p.1.jt a ≤ (B : ℝ≥0∞) := (p.1.jt_le_iff a B).2 le_rfl
  have hjt_lt : (B : ℝ≥0∞) < p.1.jt (a + 1) := by
    by_contra h
    rw [not_lt] at h
    have := (p.1.jt_le_iff (a + 1) B).1 h
    omega
  have hfin : p.1.jt a < ⊤ := lt_of_le_of_lt hjt_le ENNReal.coe_lt_top
  have hlen : ((P.hatRec k ρ p a) (Fin.last k)).len = p.1.jt a := by
    unfold CycPlan.hatRec CycRec.snoc
    rw [Fin.snoc_last]
    exact cycPath_cut_len p _
  have hd : P.dl k (P.hatRec k ρ p a) ≤ (B : ℝ≥0∞) - p.1.jt a := by
    have := hdl (P.hatRec k ρ p a)
    rwa [hlen] at this
  have hmem : p.1.jt a + P.dl k (P.hatRec k ρ p a) ∈ stopSet P k ρ p := by
    refine Or.inr ⟨a, hfin, rfl, ?_⟩
    refine lt_of_le_of_lt ?_ hjt_lt
    calc p.1.jt a + P.dl k (P.hatRec k ρ p a) ≤ p.1.jt a + ((B : ℝ≥0∞) - p.1.jt a) :=
          add_le_add le_rfl hd
      _ = B := add_tsub_cancel_of_le hjt_le
  refine (sInf_le hmem).trans ?_
  calc p.1.jt a + P.dl k (P.hatRec k ρ p a) ≤ p.1.jt a + ((B : ℝ≥0∞) - p.1.jt a) :=
        add_le_add le_rfl hd
    _ = B := add_tsub_cancel_of_le hjt_le

end generic

section plans

variable {k : ℕ} {β : ℝ} [Fact (0 < β)]

/-- The common bound on the lengths of the walks of `𝒫₅`. -/
noncomputable def plan5Bound (n : ℕ) (tn : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal tn ⊔ ENNReal.ofReal ((4 : ℝ) ^ n) ⊔ ENNReal.ofReal ((4 : ℝ) ^ (escJ n - 1))

theorem plan5Bound_ne_top (n : ℕ) (tn : ℝ) : plan5Bound n tn ≠ ⊤ := by
  unfold plan5Bound
  simp [ENNReal.ofReal_ne_top]

theorem le_plan5Bound_tn (n : ℕ) (tn : ℝ) : ENNReal.ofReal tn ≤ plan5Bound n tn :=
  le_sup_left.trans le_sup_left

theorem le_plan5Bound_n (n : ℕ) (tn : ℝ) : ENNReal.ofReal ((4 : ℝ) ^ n) ≤ plan5Bound n tn :=
  le_sup_right.trans le_sup_left

theorem le_plan5Bound_j (n : ℕ) (tn : ℝ) :
    ENNReal.ofReal ((4 : ℝ) ^ (escJ n - 1)) ≤ plan5Bound n tn :=
  le_sup_right

theorem plan5_dl_le (n : ℕ) (β : ℝ) [Fact (0 < β)] (tn : ℝ) (u : EscV k) (β' i : ℕ)
    (hlog : 1 < Real.log β) {m : ℕ} (hm : m < escIstar n (escJ n) + 2)
    (ρ : CycRecN ℕ (k + 2) (m + 1)) :
    (plan5 n β tn u β' i hlog).dl m ρ ≤ plan5Bound n tn - (ρ (Fin.last m)).len := by
  by_cases h0 : m = 0
  · subst h0
    simp only [plan5, ite_true]
    unfold plan5Dl0
    split_ifs with h
    · exact zero_le
    · exact (min_le_right _ _).trans (tsub_le_tsub_right (le_plan5Bound_tn n tn) _)
  · by_cases h1 : m ≤ escIstar n (escJ n)
    · simp only [plan5, h0, h1, ite_true, ite_false]
      unfold EscRP.escDl
      split_ifs with h
      · exact zero_le
      · exact (min_le_right _ _).trans (tsub_le_tsub_right (le_plan5Bound_n n tn) _)
    · have h2 : m = escIstar n (escJ n) + 1 := by omega
      have e : (plan5 n β tn u β' i hlog).dl m ρ = plan5DlB (escJ n) ρ := by
        simp only [plan5]
        rw [ite_eq_right h0, ite_eq_right h1, ite_eq_left h2]
      rw [e]
      exact tsub_le_tsub_right (le_plan5Bound_j n tn) _

theorem plan5_planFin (n : ℕ) (β : ℝ) [Fact (0 < β)] (tn : ℝ) (u : EscV k) (β' i : ℕ)
    (hlog : 1 < Real.log β) : PlanFin (plan5 n β tn u β' i hlog) := by
  intro ν hν j hj
  have hj' : j < escIstar n (escJ n) + 2 := by
    have : (j : ℕ∞) < ((escIstar n (escJ n) + 2 : ℕ) : ℕ∞) := hj
    exact_mod_cast this
  rw [len_E_eq]
  exact lt_of_le_of_lt (stopLen_le_of_dl_le _ j _ _ (plan5Bound_ne_top n tn)
    fun ρ' => plan5_dl_le n β tn u β' i hlog hj' ρ') (lt_top_iff_ne_top.2 (plan5Bound_ne_top n tn))

end plans

end ElboimSly.Paper.Escape
