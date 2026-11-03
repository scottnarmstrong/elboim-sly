/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycPlanSanity
public import ElboimSly.Foundations.Cyclic.CycClosingStopLen
public import ElboimSly.Foundations.Cyclic.CycSchemeEnvFinalNth
public import ElboimSly.Foundations.Cyclic.CycRecCoords
public import ElboimSly.Foundations.Cyclic.CycRegionMeas
public import Mathlib

/-!
# The two-walk exploration plan of cyclic walks within one lap

Cyclic walks within one lap (b), (c), construction of the plan `𝔭`.

`pairPlan d β a b ra rb L` is the plan with `K = 2`, `Start₁ = (a, ra, +1)`,
`Start₂ = (b, rb, +1)`, no stopping decisions and the deadline `dl_k(ρ) = (L - ℓ(ρ))⁺`.
Its stopping length is `L` for every path (`pairPlan_stopLen`).
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Paper

open ElboimSly.Cyclic

variable {d : ℕ} {β : ℝ} [Fact (0 < β)]

/-- The plan `𝔭` of cyclic walks within one lap (b), (c). -/
noncomputable def pairPlan (d : ℕ) (β : ℝ) (a b : Fin d → ℤ) (ra rb : ℝ) (L : ℝ≥0) :
    CycPlan Unit d β where
  K := 2
  start k _ := if k = 0 then ((), a, ra, true) else ((), b, rb, true)
  dl k ρ := (L : ℝ≥0∞) - (ρ (Fin.last k)).len
  st _ _ := false
  measurable_start k := by
    by_cases h : k = 0
    · simp only [h, ite_true]; exact measurable_const
    · simp only [h, ite_false]; exact measurable_const
  measurable_dl k :=
    measurable_const.sub (measurable_entry_len.comp (measurable_pi_apply _))
  measurable_st _ := measurable_const

omit [Fact (0 < β)] in
theorem pairPlan_dl_hat (a b : Fin d → ℤ) (ra rb : ℝ) (L : ℝ≥0) (k : ℕ) (ρ : CycRecN Unit d k)
    (p : CycPath d) (n : ℕ) :
    (pairPlan d β a b ra rb L).dl k ((pairPlan d β a b ra rb L).hatRec k ρ p n) =
      (L : ℝ≥0∞) - p.1.jt n := by
  simp [pairPlan, CycPlan.hatRec, CycRec.snoc, CycEntry.len, CycPath.cut]

omit [Fact (0 < β)] in
/-- The stopping length of the plan `𝔭` is `L`, for every path. -/
theorem pairPlan_stopLen (a b : Fin d → ℤ) (ra rb : ℝ) (L : ℝ≥0) (k : ℕ)
    (ρ : CycRecN Unit d k) (p : CycPath d) :
    (pairPlan d β a b ra rb L).stopLen k ρ p = L := by
  unfold CycPlan.stopLen
  apply le_antisymm
  · set n := p.1.cnt L with hn
    have hja : p.1.jt n ≤ L := (p.1.jt_le_iff n L).2 le_rfl
    have hjb : (L : ℝ≥0∞) < p.1.jt (n + 1) := by
      by_contra h
      rw [not_lt] at h
      have := (p.1.jt_le_iff (n + 1) L).1 h
      omega
    refine sInf_le (Or.inr ⟨n, lt_of_le_of_lt hja ENNReal.coe_lt_top, ?_, ?_⟩)
    · rw [pairPlan_dl_hat]; exact (add_tsub_cancel_of_le hja).symm
    · exact hjb
  · refine le_sInf ?_
    rintro t (⟨n, -, -, h, -⟩ | ⟨n, -, rfl, -⟩)
    · exact absurd h (by simp [pairPlan])
    · rw [pairPlan_dl_hat]; exact le_add_tsub

end ElboimSly.Paper

end
