/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Escape.Es52Loc
public import ElboimSly.Paper.Escape.Es54Meas
public import ElboimSly.Paper.Escape.Plan5Meas
public import Mathlib

/-!
# Measurability of the events `𝒦(β')` and `𝒜_i`

t' and escK(β'); 𝒜_i, 𝒜, 𝒢(β').

The sets `escKSet`, `escASet`, `escAUnion` of environments are measurable: on good environments
they are read off a coordinate of the (measurable) final record of the plan.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace ElboimSly.Paper.Escape

open ElboimSly ElboimSly.Cyclic ElboimSly.Cyclic.CycSchemeEnv ElboimSly.Paper

set_option linter.unusedSectionVars false

variable {k : ℕ} {β : ℝ} [Fact (0 < β)]

theorem measurable_cycFloor_e52 (β : ℝ) : Measurable (cycFloor β) := by
  unfold cycFloor
  have h1 : Measurable fun x : ℝ => ((⌊x / β⌋ : ℤ) : ℝ) :=
    (measurable_from_top (f := fun z : ℤ => (z : ℝ))).comp
      (Int.measurable_floor.comp (measurable_id.div_const β))
  have h2 : Measurable fun x : ℝ => ((⌊x - β * ⌊x / β⌋⌋ : ℤ) : ℝ) :=
    (measurable_from_top (f := fun z : ℤ => (z : ℝ))).comp
      (Int.measurable_floor.comp (measurable_id.sub (h1.const_mul β)))
  exact (h1.const_mul β).add h2

theorem measurable_cycIntPhase (β : ℝ) : Measurable (cycIntPhase β) := by
  unfold cycIntPhase
  have h1 : Measurable fun x : ℝ => ((⌊x / β⌋ : ℤ) : ℝ) :=
    (measurable_from_top (f := fun z : ℤ => (z : ℝ))).comp
      (Int.measurable_floor.comp (measurable_id.div_const β))
  exact measurable_id.sub (h1.const_mul β)

theorem cycNgood_id_of_good {ν : Measure (CycS ℕ (k + 2) β)} (hν : CycGood ν) :
    cycNgood (id : Measure (CycS ℕ (k + 2) β) → _) ν = ν := by
  simp [cycNgood, hν]

/-- On a good environment the entries of the final record of a finite plan are the final entries. -/
theorem coord_envFinal_of_good (P : CycPlan ℕ (k + 2) β) (hP : PlanFin P)
    {ν : Measure (CycS ℕ (k + 2) β)} (hν : CycGood ν) {m : ℕ} (hm : (m : ℕ∞) < P.K) :
    (P.envFinal ν).coord P.junk m = P.E (rule P ν) m := by
  classical
  have h := CycPlan.cycFinal_nth_gen P (rule P ν) m
  rw [ite_eq_left ((hP.cont_iff hν m).2 hm)] at h
  unfold CycRec.coord
  have e : P.envFinal ν = P.cycFinal (rule P ν) := rfl
  rw [e, h]
  rfl

theorem measurableSet_escKEnt (β tn : ℝ) [Fact (0 < β)] (n : ℕ) (u : Fin (k + 2) → ℤ) (β' : ℕ) :
    MeasurableSet {e : CycEntry ℕ (k + 2) | EscKEnt β tn n u β' e} := by
  have h1 := measurableSet_of_end (k := k) (escBlockMinus (escJ n) u)
  have h2 : MeasurableSet {e : CycEntry ℕ (k + 2) | e.len ≤ ENNReal.ofReal tn} :=
    measurableSet_le measurable_entry_len' measurable_const
  have h3 : MeasurableSet {e : CycEntry ℕ (k + 2) |
      cycIntPhase β (cycFloor β (e.len.toReal + 4 ^ escJ n)) = (β' : ℝ)} := by
    have hm : Measurable fun e : CycEntry ℕ (k + 2) =>
        cycIntPhase β (cycFloor β (e.len.toReal + 4 ^ escJ n)) :=
      (measurable_cycIntPhase β).comp ((measurable_cycFloor_e52 β).comp
        ((ENNReal.measurable_toReal.comp measurable_entry_len').add_const _))
    exact hm (measurableSet_singleton _)
  exact h1.inter (h2.inter h3)

theorem measurableSet_escKSet (n : ℕ) (tn : ℝ) (u : Fin (k + 2) → ℤ) (β' : ℕ)
    (hlog : 1 < Real.log β) (hadm : EscAdmissible (escJ n) u) (htn : 0 < tn) :
    MeasurableSet (escKSet β tn n β' u) := by
  have hR := measurable_envFinal_cycNgood (plan5 n β tn u β' 1 hlog)
    (N := (id : Measure (CycS ℕ (k + 2) β) → _)) measurable_id
  have hm : Measurable fun ν : Measure (CycS ℕ (k + 2) β) =>
      ((plan5 n β tn u β' 1 hlog).envFinal (cycNgood id ν)).coord
        (plan5 n β tn u β' 1 hlog).junk 0 := (CycRec.measurable_coord _ 0).comp hR
  have hset : escKSet β tn n β' u = {ν | CycGood ν} ∩
      (fun ν => ((plan5 n β tn u β' 1 hlog).envFinal (cycNgood id ν)).coord
        (plan5 n β tn u β' 1 hlog).junk 0) ⁻¹' {e | EscKEnt β tn n u β' e} := by
    ext ν
    rw [escK_iff_ent5 n tn u β' 1 hlog hadm htn]
    simp only [mem_inter_iff, mem_ofPred_eq, mem_preimage]
    refine and_congr_right fun hν => ?_
    rw [cycNgood_id_of_good hν, coord_envFinal_of_good _ (plan5_planFin _ _ _ _ _ _ _) hν
      (by show ((0 : ℕ) : ℕ∞) < ((escIstar n (escJ n) + 2 : ℕ) : ℕ∞)
          exact_mod_cast Nat.succ_pos _)]
    rfl
  rw [hset]
  exact measurableSet_cycGood.inter (hm (measurableSet_escKEnt β tn n u β'))

theorem measurableSet_escASet (n : ℕ) (u : Fin (k + 2) → ℤ) (β' : ℕ) (hlog : 1 < Real.log β)
    {i : ℕ} (hi1 : 1 ≤ i) (hiI : i ≤ escIstar n (escJ n)) :
    MeasurableSet (escASet n u β' hlog i) := by
  have hA := measurableSet_A (n := n) (u := u) (b := β') (hlog := hlog)
    (N := (id : Measure (CycS ℕ (k + 2) β) → _)) measurable_id (ℓ := i - 1) (by omega)
  have hset : escASet n u β' hlog i = {ν | CycGood ν} ∩
      EscAEv n u β' hlog (id : Measure (CycS ℕ (k + 2) β) → _) (i - 1) := by
    ext ν
    simp only [escASet, EscAEv, mem_inter_iff, mem_ofPred_eq]
    refine and_congr_right fun hν => ?_
    rw [cycNgood_id_of_good hν]
  rw [hset]
  exact measurableSet_cycGood.inter hA

theorem measurableSet_escAUnion (n : ℕ) (u : Fin (k + 2) → ℤ) (β' : ℕ) (hlog : 1 < Real.log β) :
    MeasurableSet (escAUnion n u β' hlog) := by
  have hset : escAUnion n u β' hlog = {ν | CycGood ν} ∩
      ⋃ ℓ ∈ Finset.range (escIstar n (escJ n)),
        EscAEv n u β' hlog (id : Measure (CycS ℕ (k + 2) β) → _) ℓ := by
    ext ν
    simp only [escAUnion, EscAEv, mem_inter_iff, mem_ofPred_eq, mem_iUnion, Finset.mem_range,
      exists_prop]
    refine and_congr_right fun hν => ?_
    rw [cycNgood_id_of_good hν]
  rw [hset]
  refine measurableSet_cycGood.inter (MeasurableSet.biUnion (Finset.countable_toSet _) fun ℓ hℓ => ?_)
  exact measurableSet_A (n := n) (u := u) (b := β') (hlog := hlog)
    (N := (id : Measure (CycS ℕ (k + 2) β) → _)) measurable_id (Finset.mem_range.1 hℓ)

end ElboimSly.Paper.Escape
