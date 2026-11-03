/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Escape.Es55Assemble
public import ElboimSly.Foundations.Cyclic.CycClosingStopLen
public import Mathlib

/-!
# The stopping length of the first walk of `𝒫₅`

The connecting plan (entry `0`, the walk `W_1` stopped when it enters `B`, closes, or has
length `t_n`).

`stopLen0_eq`: for every path `p`, the stopping length of the first walk of `plan5` is
`min (ξ_B(p), t_reg(p), t_n)`, where `ξ_B(p)` is the first entrance time of `p` into `B` and
`t_reg(p) = inf {jβ : j ≥ 1, p(jβ) = 0}`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace ElboimSly.Paper.Escape

open ElboimSly ElboimSly.Cyclic ElboimSly.Paper

set_option linter.unusedSectionVars false

variable {k : ℕ} {β : ℝ} [Fact (0 < β)]

/-- The first entrance time of a path into a set. -/
noncomputable def pathXi0 (B : Set (EscV k)) (p : CPath (EscV k)) : ℝ≥0∞ :=
  ⨅ (t : ℝ≥0) (_ : p.fn t ∈ B), (t : ℝ≥0∞)

theorem entEnd_cut' (δ : CycData ℕ (k + 2)) (p : CycPath (k + 2)) {x : ℝ≥0∞} (hx : x < ⊤) :
    entEnd ((δ, p.cut x) : CycEntry ℕ (k + 2)) = p.1.fn x.toNNReal := by
  have := entEnd_cut δ p x.toNNReal
  rwa [ENNReal.coe_toNNReal hx.ne] at this

theorem len_cut' (δ : CycData ℕ (k + 2)) (p : CycPath (k + 2)) (x : ℝ≥0∞) :
    CycEntry.len ((δ, p.cut x) : CycEntry ℕ (k + 2)) = x := by
  unfold CycEntry.len CycPath.cut
  simp only [CPath.cut_len]

section entry0

variable (n : ℕ) (tn : ℝ) (u : EscV k) (β' i : ℕ) (hlog : 1 < Real.log β)
  (ρ : CycRecN ℕ (k + 2) 0) (p : CycPath (k + 2))

theorem plan5_hat0 (a : ℕ) :
    (plan5 n β tn u β' i hlog).hatRec 0 ρ p a (Fin.last 0) =
      ((plan5 n β tn u β' i hlog).start 0 ρ, p.cut (p.1.jt a)) := by
  unfold CycPlan.hatRec
  exact snoc_last' _ _

theorem plan5_st_zero (ρ' : CycRecN ℕ (k + 2) (0 + 1)) :
    (plan5 n β tn u β' i hlog).st 0 ρ' = plan5St0 β (escJ n) u ρ' := by
  simp [plan5]

theorem plan5_dl_zero (ρ' : CycRecN ℕ (k + 2) (0 + 1)) :
    (plan5 n β tn u β' i hlog).dl 0 ρ' = plan5Dl0 β tn (escJ n) u ρ' := by
  simp [plan5]

theorem plan5_st0_iff (a : ℕ) (ha : p.1.jt a < ⊤) :
    (plan5 n β tn u β' i hlog).st 0 ((plan5 n β tn u β' i hlog).hatRec 0 ρ p a) = true ↔
      closeSt β (p.cut (p.1.jt a)) = true ∨ p.1.fn (p.1.jt a).toNNReal ∈ escBlock (escJ n) u := by
  classical
  rw [plan5_st_zero]
  unfold plan5St0
  rw [plan5_hat0 n tn u β' i hlog ρ p a]
  rw [entEnd_cut' _ p ha]
  simp

open Classical in
theorem plan5_dl0_eq_ent (a : ℕ) (ha : p.1.jt a < ⊤) :
    (plan5 n β tn u β' i hlog).dl 0 ((plan5 n β tn u β' i hlog).hatRec 0 ρ p a) =
      if p.1.fn (p.1.jt a).toNNReal ∈ escBlock (escJ n) u then 0
      else min (closeDl β (p.cut (p.1.jt a))) (ENNReal.ofReal tn - p.1.jt a) := by
  rw [plan5_dl_zero]
  unfold plan5Dl0
  rw [plan5_hat0 n tn u β' i hlog ρ p a]
  rw [entEnd_cut' _ p ha, len_cut']

/-- The stopping length of the first walk of `𝒫₅`. -/
theorem stopLen0_eq :
    (plan5 n β tn u β' i hlog).stopLen 0 ρ p =
      min (min (pathXi0 (escBlock (escJ n) u) p.1) (pathTreg β.toNNReal p.1.fn))
        (ENNReal.ofReal tn) := by
  classical
  have hβ : 0 < β := Fact.out
  apply le_antisymm
  · refine le_min (le_min ?_ ?_) ?_
    · refine le_iInf fun s => le_iInf fun hs => ?_
      exact stopLen_plan5_zero_le n tn u β' i hlog ρ p s hs
    · rw [← closingPlan_stopLen (β := β) (K := (plan5 n β tn u β' i hlog).K)
        (start := (plan5 n β tn u β' i hlog).start)
        (hs := (plan5 n β tn u β' i hlog).measurable_start) 0 ρ p]
      unfold CycPlan.stopLen
      refine le_sInf ?_
      rintro c (⟨a, ha1, hlt, hst, rfl⟩ | ⟨a, hlt, rfl, hlt2⟩)
      · refine sInf_le (Or.inl ⟨a, ha1, hlt, ?_, rfl⟩)
        rw [plan5_st0_iff n tn u β' i hlog ρ p a hlt]
        left
        have : (closingPlan β (plan5 n β tn u β' i hlog).K (plan5 n β tn u β' i hlog).start
            (plan5 n β tn u β' i hlog).measurable_start).st 0
            ((closingPlan β (plan5 n β tn u β' i hlog).K (plan5 n β tn u β' i hlog).start
              (plan5 n β tn u β' i hlog).measurable_start).hatRec 0 ρ p a) =
            closeSt β (p.cut (p.1.jt a)) := by
          show closeSt β _ = _
          rw [closing_hat_path]
        rw [← this]; exact hst
      · have hdlc : (closingPlan β (plan5 n β tn u β' i hlog).K (plan5 n β tn u β' i hlog).start
            (plan5 n β tn u β' i hlog).measurable_start).dl 0
            ((closingPlan β (plan5 n β tn u β' i hlog).K (plan5 n β tn u β' i hlog).start
              (plan5 n β tn u β' i hlog).measurable_start).hatRec 0 ρ p a) =
            closeDl β (p.cut (p.1.jt a)) := by
          show closeDl β _ = _
          rw [closing_hat_path]
        rw [hdlc] at hlt2 ⊢
        have hle : (plan5 n β tn u β' i hlog).dl 0
            ((plan5 n β tn u β' i hlog).hatRec 0 ρ p a) ≤ closeDl β (p.cut (p.1.jt a)) := by
          rw [plan5_dl0_eq_ent n tn u β' i hlog ρ p a hlt]
          split_ifs
          · exact zero_le
          · exact min_le_left _ _
        exact le_trans (sInf_le (a := p.1.jt a + (plan5 n β tn u β' i hlog).dl 0
            ((plan5 n β tn u β' i hlog).hatRec 0 ρ p a))
          (Or.inr ⟨a, hlt, rfl, lt_of_le_of_lt (add_le_add le_rfl hle) hlt2⟩))
          (add_le_add le_rfl hle)
    · set r : ℝ≥0 := tn.toNNReal with hr
      have hrt : ((r : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal tn := rfl
      set a := p.1.cnt r with ha
      have hja : p.1.jt a ≤ r := (p.1.jt_le_iff a r).2 le_rfl
      have hjb : (r : ℝ≥0∞) < p.1.jt (a + 1) := by
        by_contra h
        rw [not_lt] at h
        have := (p.1.jt_le_iff (a + 1) r).1 h
        omega
      have hlt : p.1.jt a < ⊤ := lt_of_le_of_lt hja ENNReal.coe_lt_top
      have hdl : (plan5 n β tn u β' i hlog).dl 0 ((plan5 n β tn u β' i hlog).hatRec 0 ρ p a) ≤
          ENNReal.ofReal tn - p.1.jt a := by
        rw [plan5_dl0_eq_ent n tn u β' i hlog ρ p a hlt]
        split_ifs
        · exact zero_le
        · exact min_le_right _ _
      have hc' : p.1.jt a + (plan5 n β tn u β' i hlog).dl 0
          ((plan5 n β tn u β' i hlog).hatRec 0 ρ p a) ≤ ENNReal.ofReal tn := by
        calc _ ≤ p.1.jt a + (ENNReal.ofReal tn - p.1.jt a) := add_le_add le_rfl hdl
          _ = max (p.1.jt a) (ENNReal.ofReal tn) := add_tsub_eq_max
          _ ≤ ENNReal.ofReal tn := max_le (by rw [← hrt]; exact hja) le_rfl
      have hlt2 : p.1.jt a + (plan5 n β tn u β' i hlog).dl 0
          ((plan5 n β tn u β' i hlog).hatRec 0 ρ p a) < p.1.jt (a + 1) := by
        refine lt_of_le_of_lt hc' ?_
        rw [← hrt]; exact hjb
      exact le_trans (sInf_le (a := p.1.jt a + (plan5 n β tn u β' i hlog).dl 0
        ((plan5 n β tn u β' i hlog).hatRec 0 ρ p a)) (Or.inr ⟨a, hlt, rfl, hlt2⟩)) hc'
  · unfold CycPlan.stopLen
    refine le_sInf ?_
    rintro c (⟨a, ha1, hlt, hst, rfl⟩ | ⟨a, hlt, rfl, hlt2⟩)
    · rw [plan5_st0_iff n tn u β' i hlog ρ p a hlt] at hst
      rcases hst with hc | hB
      · rw [closeSt_cut_iff p hlt] at hc
        obtain ⟨j, hj, h1, h2⟩ := hc
        have h3 : (p.1.jt a).toNNReal = (j : ℝ≥0) * β.toNNReal := by
          rw [h1, ofReal_nat_mul, ENNReal.toNNReal_coe]
        refine (min_le_left _ _).trans ((min_le_right _ _).trans ?_)
        have h4 : (((j : ℝ≥0) * β.toNNReal : ℝ≥0) : ℝ≥0∞) = p.1.jt a := by
          rw [h1, ofReal_nat_mul]
        exact iInf_le_of_le ⟨j, hj, (congrArg p.1.fn h3).symm.trans h2⟩ (le_of_eq h4)
      · refine (min_le_left _ _).trans ((min_le_left _ _).trans ?_)
        refine (iInf₂_le (p.1.jt a).toNNReal hB).trans ?_
        rw [ENNReal.coe_toNNReal hlt.ne]
    · rw [plan5_dl0_eq_ent n tn u β' i hlog ρ p a hlt] at hlt2 ⊢
      by_cases hB : p.1.fn (p.1.jt a).toNNReal ∈ escBlock (escJ n) u
      · rw [ite_eq_left hB, add_zero]
        refine (min_le_left _ _).trans ((min_le_left _ _).trans ?_)
        refine (iInf₂_le (p.1.jt a).toNNReal hB).trans ?_
        rw [ENNReal.coe_toNNReal hlt.ne]
      · rw [ite_eq_right hB] at hlt2 ⊢
        rcases le_total (closeDl β (p.cut (p.1.jt a))) (ENNReal.ofReal tn - p.1.jt a) with hcl | hcl
        · rw [min_eq_left hcl] at hlt2 ⊢
          refine (min_le_left _ _).trans ((min_le_right _ _).trans ?_)
          by_cases hf : p.1.fn (p.1.jt a).toNNReal = 0
          · set σ := p.1.jt a with hσ
            obtain ⟨hn1, hn2, -⟩ := dl_facts (β := β) σ.toReal ENNReal.toReal_nonneg
            have hX : σ ≤ ENNReal.ofReal (β * (⌈max σ.toReal β / β⌉₊ : ℕ)) := by
              rw [← ENNReal.ofReal_toReal hlt.ne, mul_comm]
              refine ENNReal.ofReal_le_ofReal ?_
              rw [ENNReal.toReal_ofReal ENNReal.toReal_nonneg]; exact hn2
            have hc : σ + closeDl β (p.cut σ) =
                (((⌈max σ.toReal β / β⌉₊ : ℝ≥0) * β.toNNReal : ℝ≥0) : ℝ≥0∞) := by
              rw [closeDl_cut p hlt, ite_eq_left hf, add_tsub_cancel_of_le hX, mul_comm,
                ofReal_nat_mul]
            rw [hc] at hlt2 ⊢
            refine iInf_le_of_le ⟨⌈max σ.toReal β / β⌉₊, hn1, ?_⟩ le_rfl
            have hle : σ ≤ (((⌈max σ.toReal β / β⌉₊ : ℝ≥0) * β.toNNReal : ℝ≥0) : ℝ≥0∞) := by
              rw [← hc]; exact le_self_add
            rw [fn_eq_of_jt p.1 hle hlt2, hf]
          · rw [closeDl_cut p hlt, ite_eq_right hf] at hlt2
            simp at hlt2
        · rw [min_eq_right hcl] at hlt2 ⊢
          refine (min_le_right _ _).trans ?_
          exact le_add_tsub

end entry0

end ElboimSly.Paper.Escape
