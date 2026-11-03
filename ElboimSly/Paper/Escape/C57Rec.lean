/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Escape.Plan5Entries
public import ElboimSly.Paper.Escape.RegionLam
public import ElboimSly.Foundations.Cyclic.CycRegionMeas
public import ElboimSly.Foundations.Cyclic.CycMultiRecStop
public import Mathlib

/-!
# The avoided set `A₇` as a function of the record `cycRec(S₂)`

ES22 Claim 5.7 ("`A₇ := {y : ‖y - p_i‖ ≥ L₇, d(y, V) ≤ 1}`... an `ℱ^{(i)}_{S₂}`-measurable
set").

* `recAvoid`: the set `A₇` as a function of a record `σ`; it is a measurable function of `σ`;
* `coord_cycRecStop_lam`: the entries `0, …, k - 1` of `cycRec(Λ_k)` are the final entries `E m`;
* hence `A₇` is the value of `recAvoid` at `cycRec(S₂)`, an `ℱ_{S₂}`-measurable random set.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Escape

open ElboimSly ElboimSly.Cyclic ElboimSly.Cyclic.CycSchemeEnv ElboimSly.Paper

set_option linter.unusedSectionVars false

variable {k : ℕ}

/-- The set `A₇` as a function (a predicate on `ℤ^d`) of a record. -/
def recAvoid (junk : CycEntry ℕ (k + 2)) (p : EscV k) (L : ℝ) (I : ℕ) (σ : CycRec ℕ (k + 2)) :
    EscV k → Prop :=
  fun y => L ≤ ‖y - p‖ ∧ ∃ m, 1 ≤ m ∧ m ≤ I ∧ ∃ a : ℕ,
    (σ.coord junk m).path.jt a ≤ (σ.coord junk m).len ∧
      ‖y - (σ.coord junk m).path.jv a‖ ≤ 1

theorem recAvoid_iff (junk : CycEntry ℕ (k + 2)) (p : EscV k) (L : ℝ) (I : ℕ)
    (E : ℕ → CycEntry ℕ (k + 2)) (σ : CycRec ℕ (k + 2))
    (hE : ∀ m, 1 ≤ m → m ≤ I → σ.coord junk m = E m) (y : EscV k) :
    recAvoid junk p L I σ y ↔ y ∈ avoidSet p L E I := by
  unfold recAvoid avoidSet entVisited
  simp only [mem_ofPred_eq]
  refine and_congr_right fun _ => ?_
  constructor
  · rintro ⟨m, hm1, hmI, a, h1, h2⟩
    rw [hE m hm1 hmI] at h1 h2
    exact ⟨m, hm1, hmI, _, ⟨a, h1, rfl⟩, h2⟩
  · rintro ⟨m, hm1, hmI, v, ⟨a, h1, rfl⟩, h2⟩
    exact ⟨m, hm1, hmI, a, by rw [hE m hm1 hmI]; exact h1, by rw [hE m hm1 hmI]; exact h2⟩

theorem measurable_recAvoid (junk : CycEntry ℕ (k + 2)) (p : EscV k) (L : ℝ) (I : ℕ) :
    Measurable (recAvoid junk p L I) := by
  refine measurable_pi_iff.2 fun y => measurable_to_prop ?_
  have hc : ∀ m : ℕ, Measurable fun σ : CycRec ℕ (k + 2) => σ.coord junk m :=
    fun m => CycRec.measurable_coord junk m
  have e : (fun σ : CycRec ℕ (k + 2) => recAvoid junk p L I σ y) ⁻¹' {True} =
      {σ | L ≤ ‖y - p‖ ∧ ∃ m, 1 ≤ m ∧ m ≤ I ∧ ∃ a : ℕ,
        (σ.coord junk m).path.jt a ≤ (σ.coord junk m).len ∧
          ‖y - (σ.coord junk m).path.jv a‖ ≤ 1} := by
    ext σ; simp [recAvoid]
  rw [e]
  by_cases hL : L ≤ ‖y - p‖
  · have : {σ : CycRec ℕ (k + 2) | L ≤ ‖y - p‖ ∧ ∃ m, 1 ≤ m ∧ m ≤ I ∧ ∃ a : ℕ,
        (σ.coord junk m).path.jt a ≤ (σ.coord junk m).len ∧
          ‖y - (σ.coord junk m).path.jv a‖ ≤ 1} =
        ⋃ m ∈ Finset.Icc 1 I, ⋃ a : ℕ, ({σ | (σ.coord junk m).path.jt a ≤ (σ.coord junk m).len} ∩
          {σ | ‖y - (σ.coord junk m).path.jv a‖ ≤ 1}) := by
      ext σ; simp [hL, and_assoc]
    rw [this]
    refine MeasurableSet.biUnion (Finset.Icc 1 I).countable_toSet fun m _ => MeasurableSet.iUnion fun a => ?_
    refine MeasurableSet.inter ?_ ?_
    · exact measurableSet_le ((measurable_entry_jt a).comp (hc m)) (measurable_entry_len'.comp (hc m))
    · exact (MeasurableSet.of_discrete (s := {v : EscV k | ‖y - v‖ ≤ 1})).preimage
        ((measurable_entry_jv a).comp (hc m))
  · have : {σ : CycRec ℕ (k + 2) | L ≤ ‖y - p‖ ∧ ∃ m, 1 ≤ m ∧ m ≤ I ∧ ∃ a : ℕ,
        (σ.coord junk m).path.jt a ≤ (σ.coord junk m).len ∧
          ‖y - (σ.coord junk m).path.jv a‖ ≤ 1} = ∅ := by
      ext σ; simp [hL]
    rw [this]; exact MeasurableSet.empty

variable {β : ℝ} [Fact (0 < β)]

/-- The entries `0, …, k - 1` of `cycRec(Λ_k)` are the final entries. -/
theorem coord_trunc_lam {P : CycPlan ℕ (k + 2) β} (hP : PlanFin P) {ν : Measure (CycS ℕ (k + 2) β)}
    (hν : CycGood ν) {K : ℕ} (hK : (K : ℕ∞) ≤ P.K) {m : ℕ} (hm : m < K) :
    (CycRec.trunc (lam P ν K).toNNReal (P.envFinal ν)).coord P.junk m = P.E (rule P ν) m := by
  have hlamfin : lam P ν K ≠ ⊤ :=
    lam_ne_top (fun i hi => hP ν hν i (lt_of_lt_of_le (by exact_mod_cast hi) hK))
  set s := (lam P ν K).toNNReal with hs
  have hse : (s : ℝ≥0∞) = lam P ν K := ENNReal.coe_toNNReal hlamfin
  have hnth := trunc_envFinal_nth (P := P) (ν := ν) P.junk s m
  have hc : P.Cont (rule P ν) m ∧ lam P ν m ≤ (s : ℝ≥0∞) :=
    ⟨(hP.cont_iff hν m).2 (lt_of_lt_of_le (by exact_mod_cast hm) hK),
      by rw [hse]; exact lam_mono hm.le⟩
  rw [ite_eq_left hc] at hnth
  have : tgt P ν s m = P.E (rule P ν) m := by
    unfold tgt; rw [ite_eq_left]
    rw [← lam_succ, hse]; exact lam_mono (Nat.succ_le_of_lt hm)
  unfold CycRec.coord
  rw [hnth, this]; rfl

end ElboimSly.Paper.Escape
