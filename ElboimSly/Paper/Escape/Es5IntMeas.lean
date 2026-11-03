/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Escape.Es52Meas2
public import ElboimSly.Paper.Escape.Es52Incl
public import ElboimSly.Paper.Heavy.EscMeas
public import Mathlib

/-!
# Measurability of the escape set `{Y_B = 1}` of environments

Interface with S6 (proof: `Y_{B'}` is the indicator of a measurable set of
environments), first entrance times and the escape stopping time.

`measurableSet_escYSet`: the set `escYSet tn n u` of good environments `ν` with
`ξ_B(ν) ≤ t_n` and `ℰ(ξ_B(ν))` is measurable.  The walk of the good version of `ν` is an adapted
family of cyclic paths for the constant filtration, so `Heavy.measurableSet_heavyEscSet` applies.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Escape

open ElboimSly ElboimSly.Cyclic ElboimSly.Paper

variable {k : ℕ} {β : ℝ} [Fact (0 < β)]

/-- The regenerated walk of the good version of an environment. -/
noncomputable def escWalkG (ν : Measure (CycS ℕ (k + 2) β)) : ℝ → Fin (k + 2) → ℤ :=
  escWalk (cycNgood (fun ν : Measure (CycS ℕ (k + 2) β) => ν) ν)

omit [Fact (0 < β)] in
theorem escWalkG_eq {ν : Measure (CycS ℕ (k + 2) β)} (hν : CycGood ν) : escWalkG ν = escWalk ν := by
  simp [escWalkG, cycNgood, hν]

theorem adaptedCyclic_escWalkG :
    AdaptedCyclic (Filtration.const ℝ≥0
      (inferInstance : MeasurableSpace (Measure (CycS ℕ (k + 2) β))) le_rfl)
      (escWalkG (k := k) (β := β)) where
  path ν := isCyclicPath_escWalk (cycGood_cycNgood _ ν)
  adapted s := by
    have h : (fun ν : Measure (CycS ℕ (k + 2) β) => escWalkG ν (s : ℝ)) =
        fun ν => regW (cycNgood (fun ν : Measure (CycS ℕ (k + 2) β) => ν) ν) s := by
      funext ν
      exact escWalk_eq_regW (cycGood_cycNgood _ ν) s
    rw [h]
    exact (measurable_pi_apply s).comp (measurable_regW.comp (measurable_cycNgood measurable_id))

/-- **The escape set of environments is measurable.** -/
theorem measurableSet_escYSet (tn : ℝ) {n : ℕ} (hn : 0 < n) (u : Fin (k + 2) → ℤ) :
    MeasurableSet (escYSet (β := β) tn n u) := by
  set B := escBlock (escJ n) u with hB
  have h1 := Heavy.measurableSet_heavyEscSet adaptedCyclic_escWalkG
    (measurable_escXiTot (β := β) B) hn (escJ n)
  have h2 : MeasurableSet {ν : Measure (CycS ℕ (k + 2) β) |
      escXiTot B ν ≤ ENNReal.ofReal tn} :=
    measurableSet_le (measurable_escXiTot B) measurable_const
  have e : escYSet (β := β) tn n u = {ν | CycGood ν} ∩
      ({ν | escXiTot B ν ≤ ENNReal.ofReal tn} ∩
        Heavy.heavyEscSet (escWalkG (k := k) (β := β)) n (escJ n) (escXiTot B)) := by
    ext ν
    by_cases hν : CycGood ν
    · have hx : escXiTot B ν = escXi (escWalk ν) B := escXiTot_eq hν
      simp only [escYSet, Heavy.heavyEscSet, mem_ofPred_eq, mem_inter_iff, hν, true_and, hx,
        escWalkG_eq hν]
      constructor
      · rintro ⟨h, h'⟩
        exact ⟨h, ne_top_of_le_ne_top ENNReal.ofReal_ne_top h, h'⟩
      · rintro ⟨h, -, h'⟩
        exact ⟨h, h'⟩
    · simp [escYSet, hν]
  rw [e]
  exact measurableSet_cycGood.inter (h2.inter h1)

end ElboimSly.Paper.Escape
