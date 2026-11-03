/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Escape.Es52Meas3
public import ElboimSly.Paper.Escape.Es52Aux
public import ElboimSly.Paper.Escape.Es52Meas2
public import ElboimSly.Paper.Escape.C56Adapted
public import ElboimSly.Paper.Heavy.RegenAdapted
public import Mathlib

/-!
# `T_B = ξ_B ∧ t_n` is a stopping time of the regeneration filtration

First entrance times and the escape stopping time; Measurability (a).  `escTg` is `T_B` computed from the
good version `cycNgood N` of the environment; it is a finite stopping time of `avoidFilt`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace ElboimSly.Paper.Escape

open ElboimSly ElboimSly.Cyclic ElboimSly.Paper

set_option linter.unusedSectionVars false

variable {k : ℕ} {β : ℝ} [Fact (0 < β)] {n₀ n : ℕ} {t₀ : ℝ} {Ω : Type}
  {𝒢₀ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {Pr : Measure Ω}
  {N N' : Ω → Measure (CycS ℕ (k + 2) β)}

/-- `T_B`, from the good version of the environment, as a time. -/
noncomputable def escTg (N : Ω → Measure (CycS ℕ (k + 2) β)) (tn : ℝ) (n : ℕ)
    (u : Fin (k + 2) → ℤ) (ω : Ω) : WithTop ℝ≥0 :=
  ((escT0 β tn n u (cycNgood N ω) : ℝ≥0) : WithTop ℝ≥0)

theorem escTg_eq_min (N : Ω → Measure (CycS ℕ (k + 2) β)) (tn : ℝ) (n : ℕ)
    (u : Fin (k + 2) → ℤ) (ω : Ω) :
    escTg N tn n u ω = min (entranceTime (avoidWalk (cycNgood N) ω) (escBlock (escJ n) u))
      ((tn.toNNReal : ℝ≥0) : WithTop ℝ≥0) := by
  unfold escTg escT0
  have h1 : escXi (escWalk (cycNgood N ω)) (escBlock (escJ n) u) =
      entranceTime (avoidWalk (cycNgood N) ω) (escBlock (escJ n) u) :=
    escXi_eq_entranceTime _ _
  rw [h1]
  have h2 : ENNReal.ofReal tn = ((tn.toNNReal : ℝ≥0) : ℝ≥0∞) := rfl
  rw [h2]
  have h3 : min (entranceTime (avoidWalk (cycNgood N) ω) (escBlock (escJ n) u))
      ((tn.toNNReal : ℝ≥0) : ℝ≥0∞) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_right _ _)
  exact ENNReal.coe_toNNReal h3

theorem isStoppingTime_escTg (S : Es4Setting (k + 2) β n₀ n t₀ 𝒢₀ Pr N N') (tn : ℝ)
    (u : Fin (k + 2) → ℤ) :
    IsStoppingTime (avoidFilt 𝒢₀ S.space) (escTg N tn n u) := by
  have h := (Heavy.avoidWalk_cycNgood_adapted S).isStoppingTime_entrance (escBlock (escJ n) u)
  have h2 := h.min_const (tn.toNNReal)
  have e : escTg N tn n u = fun ω => min (entranceTime (avoidWalk (cycNgood N) ω)
      (escBlock (escJ n) u)) ((tn.toNNReal : ℝ≥0) : WithTop ℝ≥0) := funext (escTg_eq_min N tn n u)
  rw [e]
  exact h2

theorem escTg_ne_top (N : Ω → Measure (CycS ℕ (k + 2) β)) (tn : ℝ) (n : ℕ)
    (u : Fin (k + 2) → ℤ) (ω : Ω) : escTg N tn n u ω ≠ ⊤ := WithTop.coe_ne_top

end ElboimSly.Paper.Escape
