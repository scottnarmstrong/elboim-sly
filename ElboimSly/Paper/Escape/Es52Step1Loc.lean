/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Escape.Es52StopT
public import ElboimSly.Paper.Escape.Es52Loc
public import ElboimSly.Paper.Escape.Es52Resample
public import ElboimSly.Paper.Escape.ResampleTower
public import Mathlib

/-!
# Localization of `Φ_X` on `𝒦(β')`: `Φ_X(ρ^{reg}(T_B)) = Φ_X(ρ^{𝒫₅}(S₁))`

ES22 Proposition 5.2 Step 1, "the agreement of the explored regions and ring measures of
`cycRec^{𝒫₅}(S₁)` and `cycRec^{avoidPreg}(T_B)` on `G_B`" together with resampling formula(c).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace ElboimSly.Paper.Escape

open ElboimSly ElboimSly.Cyclic ElboimSly.Cyclic.CycSchemeEnv ElboimSly.Paper

set_option linter.unusedSectionVars false

variable {k : ℕ} {β : ℝ} [Fact (0 < β)] {Ω : Type} [MeasurableSpace Ω]
  {N : Ω → Measure (CycS ℕ (k + 2) β)}

theorem lam_one_eq_cum (P : CycPlan ℕ (k + 2) β) (hK : (0 : ℕ∞) < P.K)
    (ν : Measure (CycS ℕ (k + 2) β)) : lam P ν 1 = (P.envFinal ν).cum 1 := by
  unfold CycRec.cum lam
  rw [Finset.sum_range_one, Finset.sum_range_one]
  unfold CycRec.lenAt
  rw [envFinal_nth0 ν P hK]
  rfl

/-- **Localization.**  On `{N ∈ 𝒦(β')}` (with `N` good), `Φ_X(ρ^{reg}_{T_B})` is
`Φ_X(ρ^{𝒫₅}_{S₁})`, for every set `X`. -/
theorem resPhi_reg_eq_plan5 (n : ℕ) (tn : ℝ) (u : EscV k) (β' i : ℕ) (hlog : 1 < Real.log β)
    (hadm : EscAdmissible (escJ n) u) (htn : 0 < tn) {Pr : Measure Ω} {ω : Ω}
    (hω : CycGood (N ω)) (hK : N ω ∈ escKSet β tn n β' u)
    (X : Set (Measure (CycS ℕ (k + 2) β))) :
    resPhi (regPlan (k + 2) β) Pr N (escTg N tn n u) X ω =
      resPhi (plan5 n β tn u β' i hlog) Pr N (lamT (plan5 n β tn u β' i hlog) N 1) X ω := by
  have e := cycNgood_of_good hω
  have hS : SRW.stopReal (lamT (plan5 n β tn u β' i hlog) N 1) ω =
      escS1 n tn u β' i hlog (N ω) := by
    show (lam (plan5 n β tn u β' i hlog) (cycNgood N ω) 1).toNNReal = _
    rw [e, lam_one_eq_cum _ (by
      show (0 : ℕ∞) < ((escIstar n (escJ n) + 2 : ℕ) : ℕ∞)
      exact_mod_cast Nat.succ_pos _)]
    rfl
  have hT : SRW.stopReal (escTg N tn n u) ω = escT0 β tn n u (N ω) := by
    show (escT0 β tn n u (cycNgood N ω)) = _
    rw [e]
  refine resPhi_loc (escTg_ne_top N tn n u ω)
    (lamT_ne_top _ (plan5_planFin n β tn u β' i hlog) ω (by
      show ((1 : ℕ) : ℕ∞) ≤ ((escIstar n (escJ n) + 2 : ℕ) : ℕ∞)
      exact_mod_cast (by omega))) ?_ ?_ X
  · have h := loc_rm n tn u β' i hlog hadm htn hK
    unfold cycRecStop
    rw [hS, hT, e]
    exact h
  · have h := loc_region n tn u β' i hlog hadm htn hK
    unfold cycRecStop
    rw [hS, hT, e]
    exact h

end ElboimSly.Paper.Escape
