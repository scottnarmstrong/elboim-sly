/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycSchemeDrvDef
public import Mathlib

/-!
# The driving scheme (a): measurability of the driving data of a state

`drvIdx` (`j_k`) and `drvOff` (`a_k`) are measurable functions of the state, for a measurable driving
assignment `(𝖩_k)` (`hj : ∀ k, Measurable (jx k)`).
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

variable {I : Type*} [MeasurableSpace I] [Countable I] [MeasurableSingletonClass I] {d : ℕ} {β : ℝ} [Fact (0 < β)]
  {J : Type*} [MeasurableSpace J] [Countable J] [MeasurableSingletonClass J]
  {jx : ∀ k : ℕ, CycRecN I d k → J}

omit [Countable I] [MeasurableSingletonClass I] in
theorem measurable_prefix (n : ℕ) :
    Measurable fun f : Fin (n + 1) → CycEntry I d => (fun m : Fin n => f m.castSucc) :=
  measurable_pi_iff.2 fun _m => measurable_pi_apply _

omit [Countable J] [MeasurableSingletonClass J] in
omit [Countable I] [MeasurableSingletonClass I] in
theorem measurable_drvIdx (hj : ∀ k, Measurable (jx k)) (j0 : J) :
    Measurable (drvIdx jx j0 : CycScheme.State I d → J) := by
  have : Measurable fun ρ : CycRec I d => drvIdx jx j0 (ρ, false) := by
    refine measurable_fun_sum ?_ ?_
    · refine measurable_sigma_of fun k => ?_
      cases k with
      | zero => exact measurable_const
      | succ n => exact (hj n).comp (measurable_prefix n)
    · exact measurable_const
  have h2 : (drvIdx jx j0 : CycScheme.State I d → J) =
      fun st => drvIdx jx j0 (st.1, false) := by
    funext st; rfl
  rw [h2]
  exact this.comp measurable_fst

omit [Countable I] [MeasurableSingletonClass I] in
theorem measurable_drvOff (hj : ∀ k, Measurable (jx k)) :
    Measurable (drvOff jx : CycScheme.State I d → ℝ≥0) := by
  have : Measurable fun ρ : CycRec I d => drvOff jx (ρ, false) := by
    refine measurable_fun_sum ?_ ?_
    · refine measurable_sigma_of fun k => ?_
      cases k with
      | zero => exact measurable_const
      | succ n =>
        show Measurable fun f : Fin (n + 1) → CycEntry I d =>
          drvOffset jx (fun m : Fin n => f m.castSucc) (jx n (fun m => f m.castSucc))
        unfold drvOffset
        refine Finset.measurable_sum _ fun i _ => ?_
        refine Measurable.ite ?_ ?_ measurable_const
        · refine measurableSet_eq_fun ?_ ?_
          · exact (hj i).comp (measurable_pi_iff.2 fun m =>
              measurable_pi_apply _)
          · exact (hj n).comp (measurable_prefix n)
        · exact measurable_time.comp (measurable_pi_apply _)
    · exact measurable_const
  have h2 : (drvOff jx : CycScheme.State I d → ℝ≥0) = fun st => drvOff jx (st.1, false) := by
    funext st; rfl
  rw [h2]
  exact this.comp measurable_fst

end ElboimSly.Cyclic

end
