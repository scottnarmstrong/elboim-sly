/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycSchemePath
public import ElboimSly.Foundations.Cyclic.CycRestrictMeas
public import ElboimSly.Foundations.Cyclic.CycTruncMeas
public import ElboimSly.Foundations.Cyclic.CycPlan
public import ElboimSly.Foundations.Cyclic.CycRingMeas2
public import Mathlib

/-!
# Record operations used by the environment scheme

The environment scheme of a plan. Total operations on records `CycRec`, each with a coordinate
description and measurability:

* `CycRec.lastIdx`, `CycRec.lastEntry`: the last entry (the *current walk*);
* `CycRec.setLast e ρ`: replace the last entry of a finite record by `e`;
* `CycRec.push e ρ`: append a world-line to a finite record;
* `CycPlan.startOf`, `CycPlan.dlOf`, `CycPlan.stOf`: the plan data `cycStart_{k+1}`, `cycdl_k`,
  `cycst_k` applied to a (finite) record of the right length, with junk values otherwise;
* `CycRec.total`: `Λ(ρ)` is measurable.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

variable {I : Type*} [MeasurableSpace I] {d : ℕ}

namespace CycRec

/-- The index of the last entry of a finite record (`0` for the empty record and for infinite
records). -/
def lastIdx (ρ : CycRec I d) : ℕ := ρ.num.toNat - 1

/-- The last entry (the current walk), `junk` if there is none. -/
def lastEntry (junk : CycEntry I d) (ρ : CycRec I d) : CycEntry I d := ρ.coord junk ρ.lastIdx

/-- Replace the last entry of a finite non-empty record by `e`. -/
def setLast (e : CycEntry I d) : CycRec I d → CycRec I d
  | Sum.inl ⟨0, f⟩ => Sum.inl ⟨0, f⟩
  | Sum.inl ⟨n + 1, f⟩ => Sum.inl ⟨n + 1, Function.update f (Fin.last n) e⟩
  | Sum.inr f => Sum.inr f

/-- Append the world-line `e` to a finite record. -/
def push (e : CycEntry I d) : CycRec I d → CycRec I d
  | Sum.inl ⟨n, f⟩ => Sum.inl ⟨n + 1, CycRec.snoc f e⟩
  | Sum.inr f => Sum.inr f

theorem enat_succ_eq {j n : ℕ} : ((j : ℕ∞) + 1 = ((n + 1 : ℕ) : ℕ∞)) ↔ j = n := by
  constructor
  · intro h
    have : ((j + 1 : ℕ) : ℕ∞) = ((n + 1 : ℕ) : ℕ∞) := by push_cast; exact h
    have := Nat.cast_injective this
    omega
  · rintro rfl; push_cast; rfl

omit [MeasurableSpace I] in
theorem num_setLast (e : CycEntry I d) (ρ : CycRec I d) : (ρ.setLast e).num = ρ.num := by
  rcases ρ with ⟨n, f⟩ | f
  · cases n <;> simp [setLast, num]
  · simp [setLast, num]

open scoped Classical in
omit [MeasurableSpace I] in
theorem coord_setLast (junk : CycEntry I d) (e : CycEntry I d) (ρ : CycRec I d) (j : ℕ) :
    (ρ.setLast e).coord junk j = if (j : ℕ∞) + 1 = ρ.num then e else ρ.coord junk j := by
  rcases ρ with ⟨n, f⟩ | f
  · cases n with
    | zero => simp [setLast, coord, nth, num]
    | succ n =>
      simp only [setLast, coord, nth, num]
      by_cases hj : j < n + 1
      · simp only [hj, dite_true, Option.getD_some]
        by_cases hjn : j = n
        · subst hjn
          have : (⟨j, hj⟩ : Fin (j + 1)) = Fin.last j := rfl
          rw [this, Function.update_self, ite_eq_left (enat_succ_eq.2 rfl)]
        · have : (⟨j, hj⟩ : Fin (n + 1)) ≠ Fin.last n := fun h =>
            hjn (by simpa using congrArg Fin.val h)
          rw [Function.update_of_ne this, ite_eq_right (fun h => hjn (enat_succ_eq.1 h))]
      · simp only [hj, dite_false, Option.getD_none]
        rw [ite_eq_right (fun h => hj (by have := enat_succ_eq.1 h; omega))]
  · simp [setLast, coord, nth, num]

omit [MeasurableSpace I] in
theorem num_push (e : CycEntry I d) (ρ : CycRec I d) : (ρ.push e).num = ρ.num + 1 := by
  rcases ρ with ⟨n, f⟩ | f
  · simp [push, num]
  · simp [push, num]

open scoped Classical in
omit [MeasurableSpace I] in
theorem coord_push (junk : CycEntry I d) (e : CycEntry I d) (ρ : CycRec I d) (j : ℕ) :
    (ρ.push e).coord junk j = if (j : ℕ∞) = ρ.num then e else ρ.coord junk j := by
  rcases ρ with ⟨n, f⟩ | f
  · have hn : CycRec.num (Sum.inl ⟨n, f⟩ : CycRec I d) = (n : ℕ∞) := rfl
    rw [hn]
    simp only [push, coord, nth]
    by_cases hjn : (j : ℕ∞) = n
    · have hjn' : j = n := Nat.cast_injective hjn
      subst hjn'
      simp [CycRec.snoc, Fin.snoc]
    · have hjn' : j ≠ n := fun h => hjn (by rw [h])
      simp only [hjn, ite_false]
      by_cases hj : j < n
      · have hj1 : j < n + 1 := by omega
        simp [hj, hj1, CycRec.snoc, Fin.snoc]
      · have hj1 : ¬ j < n + 1 := by omega
        simp [hj, hj1]
  · simp [push, coord, nth, num]

end CycRec

/-! ### Measurability -/

theorem measurable_lastIdx : Measurable (CycRec.lastIdx : CycRec I d → ℕ) :=
  (measurable_of_countable (fun n : ℕ∞ => n.toNat - 1)).comp CycRec.measurable_num

theorem measurable_lastEntry (junk : CycEntry I d) :
    Measurable (CycRec.lastEntry junk : CycRec I d → CycEntry I d) :=
  measurable_index measurable_lastIdx (fun n => CycRec.measurable_coord junk n)

theorem measurable_setLast [Nonempty (CycEntry I d)] :
    Measurable fun q : CycRec I d × CycEntry I d => q.1.setLast q.2 := by
  obtain ⟨junk⟩ := ‹Nonempty (CycEntry I d)›
  have hnum : Measurable fun q : CycRec I d × CycEntry I d => q.1.num :=
    CycRec.measurable_num.comp measurable_fst
  refine measurable_cycRec_of_coords _ junk ?_ fun j => ?_
  · simp only [CycRec.num_setLast]; exact hnum
  · classical
    simp only [CycRec.coord_setLast]
    have hset : MeasurableSet {q : CycRec I d × CycEntry I d | (j : ℕ∞) + 1 = q.1.num} := by
      have := hnum (measurableSet_singleton ((j : ℕ∞) + 1))
      convert this using 1
      ext q; simp [eq_comm]
    exact Measurable.ite hset measurable_snd
      ((CycRec.measurable_coord junk j).comp measurable_fst)

theorem measurable_push [Nonempty (CycEntry I d)] :
    Measurable fun q : CycRec I d × CycEntry I d => q.1.push q.2 := by
  obtain ⟨junk⟩ := ‹Nonempty (CycEntry I d)›
  have hnum : Measurable fun q : CycRec I d × CycEntry I d => q.1.num :=
    CycRec.measurable_num.comp measurable_fst
  refine measurable_cycRec_of_coords _ junk ?_ fun j => ?_
  · simp only [CycRec.num_push]
    exact hnum.add measurable_const
  · classical
    simp only [CycRec.coord_push]
    have hset : MeasurableSet {q : CycRec I d × CycEntry I d | (j : ℕ∞) = q.1.num} := by
      have := hnum (measurableSet_singleton (j : ℕ∞))
      convert this using 1
      ext q; simp [eq_comm]
    exact Measurable.ite hset measurable_snd
      ((CycRec.measurable_coord junk j).comp measurable_fst)

/-! ### Plan data on a record -/

section Plan

variable {β : ℝ} (P : CycPlan I d β)

/-- `cycStart_{n+1}(ρ)` for a record of `n` entries; the junk data otherwise. -/
noncomputable def CycPlan.startOf : CycRec I d → CycData I d
  | Sum.inl ⟨n, f⟩ => P.start n f
  | Sum.inr _ => P.junk.data

/-- `cycdl_n(ρ)` for a record of `n + 1` entries; `0` otherwise. -/
noncomputable def CycPlan.dlOf : CycRec I d → ℝ≥0∞
  | Sum.inl ⟨n + 1, f⟩ => P.dl n f
  | _ => 0

/-- `cycst_n(ρ)` for a record of `n + 1` entries; `false` otherwise. -/
noncomputable def CycPlan.stOf : CycRec I d → Bool
  | Sum.inl ⟨n + 1, f⟩ => P.st n f
  | _ => false

theorem CycPlan.measurable_startOf : Measurable P.startOf := by
  refine measurable_fun_sum ?_ measurable_const
  exact measurable_sigma_of fun n => P.measurable_start n

theorem CycPlan.measurable_dlOf : Measurable P.dlOf := by
  refine measurable_fun_sum ?_ measurable_const
  refine measurable_sigma_of fun n => ?_
  cases n with
  | zero => exact measurable_const
  | succ n => exact P.measurable_dl n

theorem CycPlan.measurable_stOf : Measurable P.stOf := by
  refine measurable_fun_sum ?_ measurable_const
  refine measurable_sigma_of fun n => ?_
  cases n with
  | zero => exact measurable_const
  | succ n => exact P.measurable_st n

end Plan

/-- The world-line that starts a new walk: `(δ, 0, u(· ∧ 0))`. -/
noncomputable def CycData.newEntry (δ : CycData I d) : CycEntry I d :=
  (δ, (CycPath.const δ.start).cut 0)

theorem measurable_newEntry : Measurable (CycData.newEntry : CycData I d → CycEntry I d) := by
  refine measurable_id.prodMk ?_
  refine measurable_cycPath_cut.comp (?_ : Measurable fun δ : CycData I d =>
    (CycPath.const δ.start, (0 : ℝ≥0∞)))
  refine Measurable.prodMk ?_ measurable_const
  have : Measurable fun δ : CycData I d => δ.start := by
    exact (measurable_fst.comp (measurable_snd))
  exact measurable_of_countable (fun u : Fin d → ℤ => CycPath.const u) |>.comp this

theorem measurable_cycSigmaMk {ι : Type*} {γ : ι → Type*} [∀ i, MeasurableSpace (γ i)] (i : ι) :
    Measurable (Sigma.mk i : γ i → Σ i, γ i) :=
  fun _ hs => MeasurableSpace.measurableSet_iInf.mp hs i

theorem measurable_entry_len' : Measurable fun e : CycEntry I d => e.len :=
  CPath.measurable_len.comp (measurable_subtype_coe.comp measurable_snd)

theorem CycRec.measurable_total [Nonempty (CycEntry I d)] :
    Measurable (CycRec.total : CycRec I d → ℝ≥0∞) := by
  obtain ⟨junk⟩ := ‹Nonempty (CycEntry I d)›
  refine measurable_fun_sum ?_ ?_
  · refine measurable_sigma_of fun n => ?_
    exact (measurable_cum junk (n - 1)).comp (measurable_inl.comp (measurable_cycSigmaMk n))
  · exact Measurable.tsum fun k => measurable_entry_len'.comp (measurable_pi_apply k)

end ElboimSly.Cyclic

end
