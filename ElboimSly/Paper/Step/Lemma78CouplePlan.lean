/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Base.PairPlan
public import ElboimSly.Foundations.Cyclic.CycMultiMain
public import Mathlib

/-!
# The exploration plan `𝔭₈` of Lemma 7.8

Setting of Lemma 7.8 (Exploration). The plan has one copy and two walks: walk 1 has
start `(1, 0, 0, +1)`, decision `0` and deadline `max {t'_n - ς, 0}`; walk 2 has start
`(1, u, q, +1)`, decision `0` and deadline `∞`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Step

open ElboimSly.Cyclic ElboimSly.Paper

variable {d : ℕ} {β : ℝ}

/-- The plan `𝔭₈` of Lemma 7.8. -/
noncomputable def step78Plan (d : ℕ) (β : ℝ) (u : Fin d → ℤ) (q : ℝ) (Tn : ℝ≥0) :
    CycPlan Unit d β where
  K := 2
  start k _ := if k = 0 then ((), 0, 0, true) else ((), u, q, true)
  dl k ρ := if k = 0 then (Tn : ℝ≥0∞) - (ρ (Fin.last k)).len else ⊤
  st _ _ := false
  measurable_start k := by
    by_cases h : k = 0
    · simp only [h, ite_true]; exact measurable_const
    · simp only [h, ite_false]; exact measurable_const
  measurable_dl k := by
    by_cases h : k = 0
    · simp only [h, ite_true]
      exact measurable_const.sub (measurable_entry_len.comp (measurable_pi_apply _))
    · simp only [h, ite_false]; exact measurable_const
  measurable_st _ := measurable_const

theorem step78Plan_dl_hat (u : Fin d → ℤ) (q : ℝ) (Tn : ℝ≥0) (k : ℕ) (ρ : CycRecN Unit d k)
    (p : CycPath d) (n : ℕ) :
    (step78Plan d β u q Tn).dl k ((step78Plan d β u q Tn).hatRec k ρ p n) =
      if k = 0 then (Tn : ℝ≥0∞) - p.1.jt n else ⊤ := by
  simp [step78Plan, CycPlan.hatRec, CycRec.snoc, CycEntry.len, CycPath.cut]

/-- Walk 1 is stopped at length `t'_n`. -/
theorem step78Plan_stopLen_zero (u : Fin d → ℤ) (q : ℝ) (Tn : ℝ≥0) (ρ : CycRecN Unit d 0)
    (p : CycPath d) : (step78Plan d β u q Tn).stopLen 0 ρ p = Tn := by
  unfold CycPlan.stopLen
  apply le_antisymm
  · set n := p.1.cnt Tn with hn
    have hja : p.1.jt n ≤ Tn := (p.1.jt_le_iff n Tn).2 le_rfl
    have hjb : (Tn : ℝ≥0∞) < p.1.jt (n + 1) := by
      by_contra h
      rw [not_lt] at h
      have := (p.1.jt_le_iff (n + 1) Tn).1 h
      omega
    refine sInf_le (Or.inr ⟨n, lt_of_le_of_lt hja ENNReal.coe_lt_top, ?_, ?_⟩)
    · rw [step78Plan_dl_hat]; simpa using (add_tsub_cancel_of_le hja).symm
    · exact hjb
  · refine le_sInf ?_
    rintro t (⟨n, -, -, h, -⟩ | ⟨n, -, rfl, -⟩)
    · exact absurd h (by simp [step78Plan])
    · rw [step78Plan_dl_hat]; simpa using le_add_tsub

/-- Walk 2 has deadline `∞` and no decisions, so its stopping length is `∞`. -/
theorem step78Plan_stopLen_succ (u : Fin d → ℤ) (q : ℝ) (Tn : ℝ≥0) (k : ℕ)
    (ρ : CycRecN Unit d (k + 1)) (p : CycPath d) :
    (step78Plan d β u q Tn).stopLen (k + 1) ρ p = ⊤ := by
  unfold CycPlan.stopLen
  refine top_unique (le_sInf ?_)
  rintro t (⟨n, -, -, h, -⟩ | ⟨n, hn, rfl, hlt⟩)
  · exact absurd h (by simp [step78Plan])
  · rw [step78Plan_dl_hat] at hlt ⊢
    simp only [Nat.succ_ne_zero, ite_false, add_top] at hlt ⊢
    exact absurd hlt (not_lt_of_ge le_top)

end ElboimSly.Paper.Step

end
