/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycMeasurable
public import ElboimSly.Frozen.Defs.CycClosesBy
public import ElboimSly.Foundations.Interchange.TargetEvents
import Mathlib

/-!
# Measurability of the events of the cyclic walk

Measurability (`π_s`, `π_β^k`, `W_{u,q}(t)`, `t_reg`, closing, `Fin₀`, `Inf`).

Statements about good configurations only: a property `P` holds on a measurable set of good
configurations if `{ν | Good ν ∧ P ν}` is measurable (`measurableSet_good_and`).
-/

@[expose] public section

open MeasureTheory Set ElboimSly.Interchange
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

variable {d : ℕ} {β : ℝ} [Fact (0 < β)]

theorem measurableSet_good_and {P : Measure (RingSpace d β) → Prop}
    (h : MeasurableSet {ν : GoodSet d β | P ν.1}) :
    MeasurableSet {ν : Measure (RingSpace d β) | Good ν ∧ P ν} := by
  obtain ⟨U, hU, hUe⟩ := (MeasurableSpace.measurableSet_comap).1 h
  have : {ν : Measure (RingSpace d β) | Good ν ∧ P ν} = {ν | Good ν} ∩ U := by
    ext ν
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff]
    refine and_congr_right fun hν => ?_
    have := Set.ext_iff.mp hUe ⟨ν, hν⟩
    simpa using this.symm
  rw [this]
  exact measurableSet_good.inter hU

theorem measurable_interchangePi (s : ℝ≥0) :
    Measurable (fun p : GoodSet d β × (Fin d → ℤ) => interchangePi p.1.1 s p.2) := by
  refine measurable_from_prod_countable_left fun x => ?_
  have e : (fun p : GoodSet d β => interchangePi p.1 s x) = fun p => fwdTraj p.2 x 0 (s : ℝ) :=
    funext fun p => interchangePi_eq p.2 s x
  show Measurable (fun p : GoodSet d β => interchangePi p.1 s x)
  rw [e]
  exact (measurable_fwdTraj (β := β) x).comp
    (measurable_id.prodMk (measurable_const.prodMk measurable_const))

theorem measurable_interchangePi_iterate (s : ℝ≥0) (k : ℕ) (x : Fin d → ℤ) :
    Measurable (fun ν : GoodSet d β => (interchangePi ν.1 s)^[k] x) := by
  induction k with
  | zero => exact measurable_const
  | succ k ih =>
    have : (fun ν : GoodSet d β => (interchangePi ν.1 s)^[k + 1] x) =
        fun ν => interchangePi ν.1 s ((interchangePi ν.1 s)^[k] x) :=
      funext fun ν => Function.iterate_succ_apply' _ _ _
    rw [this]
    exact (measurable_interchangePi s).comp (measurable_id.prodMk ih)

/-- Measurability; the event `Fin₀` is measurable. -/
theorem measurableSet_finZeroEvent : MeasurableSet (finZeroEvent d β) := by
  have : finZeroEvent d β = {ν | Good ν ∧ ∃ k : ℕ, 1 ≤ k ∧
      (interchangePi ν (betaNN β))^[k] 0 = 0} := rfl
  rw [this]
  refine measurableSet_good_and ?_
  have : {ν : GoodSet d β | ∃ k : ℕ, 1 ≤ k ∧ (interchangePi ν.1 (betaNN β))^[k] 0 = 0} =
      ⋃ k : ℕ, ({_ν : GoodSet d β | 1 ≤ k} ∩
        {ν | (interchangePi ν.1 (betaNN β))^[k] 0 = 0}) := by
    ext ν; simp
  rw [this]
  exact MeasurableSet.iUnion fun k => (MeasurableSet.const _).inter
    (measurableSet_eq_fun (measurable_interchangePi_iterate _ k 0) measurable_const)

/-- The event `Inf` is measurable. -/
theorem measurableSet_infEvent : MeasurableSet (infEvent d β) := by
  have : infEvent d β = {ν | Good ν ∧ ∃ x : Fin d → ℤ, ∀ k : ℕ, 1 ≤ k →
      (interchangePi ν (betaNN β))^[k] x ≠ x} := rfl
  rw [this]
  refine measurableSet_good_and ?_
  have : {ν : GoodSet d β | ∃ x : Fin d → ℤ, ∀ k : ℕ, 1 ≤ k →
      (interchangePi ν.1 (betaNN β))^[k] x ≠ x} =
      ⋃ x : Fin d → ℤ, ⋂ k : ℕ, ({_ν : GoodSet d β | k = 0} ∪
        {ν | (interchangePi ν.1 (betaNN β))^[k] x = x}ᶜ) := by
    ext ν
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_iInter, Set.mem_union, Set.mem_compl_iff]
    refine exists_congr fun x => forall_congr' fun k => ?_
    constructor
    · intro h; by_cases hk : k = 0
      · exact Or.inl hk
      · exact Or.inr (h (by omega))
    · rintro (h | h) hk
      · omega
      · exact h
  rw [this]
  exact MeasurableSet.iUnion fun x => MeasurableSet.iInter fun k =>
    (MeasurableSet.const _).union
      (measurableSet_eq_fun (measurable_interchangePi_iterate _ k x) measurable_const).compl

/-- `W^ν_{u,q}(s)` for `s ≥ 0` is a measurable function of the good configuration. -/
theorem measurable_cycWalk (u : Fin d → ℤ) (q : ℝ) {s : ℝ} (hs : 0 ≤ s) :
    Measurable (fun ν : GoodSet d β => cycWalk ν.1 u q s) := by
  have e : (fun ν : GoodSet d β => cycWalk ν.1 u q s) = fun ν => fwdTraj ν.2 u q (q + s) :=
    funext fun ν => cycWalk_of_nonneg ν.2 u q hs
  rw [e]
  exact (measurable_fwdTraj (β := β) u).comp
    (measurable_id.prodMk (measurable_const.prodMk measurable_const))

/-- `{t_reg < ∞} = Fin₀` on `Good`, so it is measurable. -/
theorem measurableSet_cycTreg_lt_top :
    MeasurableSet {ν : Measure (RingSpace d β) | Good ν ∧ cycTreg ν < ⊤} := by
  have : {ν : Measure (RingSpace d β) | Good ν ∧ cycTreg ν < ⊤} = finZeroEvent d β := by
    ext ν
    simp only [Set.mem_ofPred_eq]
    exact ⟨fun h => (cycTreg_lt_top_iff_mem_finZeroEvent h.1).mp h.2,
      fun h => ⟨h.1, (cycTreg_lt_top_iff_mem_finZeroEvent h.1).mpr h⟩⟩
  rw [this]
  exact measurableSet_finZeroEvent

/-- `{t_reg ≤ t}` is measurable (on `Good`). -/
theorem measurableSet_cycTreg_le (t : ℝ) :
    MeasurableSet {ν : Measure (RingSpace d β) | Good ν ∧ cycTreg ν ≤ ENNReal.ofReal t} := by
  have hβ : 0 < β := Fact.out
  have key : ∀ ν : Measure (RingSpace d β), Good ν → (cycTreg ν ≤ ENNReal.ofReal t ↔
      ∃ n : ℕ, 1 ≤ n ∧ (n : ℝ) * β ≤ t ∧ cycWalk ν 0 0 ((n : ℝ) * β) = 0) := by
    intro ν hν
    constructor
    · intro h
      have hlt : cycTreg ν < ⊤ := lt_of_le_of_lt h ENNReal.ofReal_lt_top
      obtain ⟨n, hn, h0, he⟩ := exists_cycTreg_eq hlt
      rw [he, ENNReal.ofReal_le_ofReal_iff'] at h
      refine ⟨n, hn, ?_, h0⟩
      rcases h with h | h
      · exact h
      · exfalso
        have : (0 : ℝ) < n * β := by
          have : (1 : ℝ) ≤ n := by exact_mod_cast hn
          nlinarith
        linarith
    · rintro ⟨n, hn, hnt, h0⟩
      exact (cycTreg_le hn h0).trans (ENNReal.ofReal_le_ofReal hnt)
  have : {ν : Measure (RingSpace d β) | Good ν ∧ cycTreg ν ≤ ENNReal.ofReal t} =
      {ν | Good ν ∧ ∃ n : ℕ, 1 ≤ n ∧ (n : ℝ) * β ≤ t ∧ cycWalk ν 0 0 ((n : ℝ) * β) = 0} := by
    ext ν
    simp only [Set.mem_ofPred_eq]
    exact and_congr_right fun hν => key ν hν
  rw [this]
  refine measurableSet_good_and ?_
  have : {ν : GoodSet d β | ∃ n : ℕ, 1 ≤ n ∧ (n : ℝ) * β ≤ t ∧
      cycWalk ν.1 0 0 ((n : ℝ) * β) = 0} =
      ⋃ n : ℕ, ({_ν : GoodSet d β | 1 ≤ n ∧ (n : ℝ) * β ≤ t} ∩
        {ν | cycWalk ν.1 0 0 ((n : ℝ) * β) = 0}) := by
    ext ν; simp [and_assoc]
  rw [this]
  refine MeasurableSet.iUnion fun n => (MeasurableSet.const _).inter ?_
  exact measurableSet_eq_fun (measurable_cycWalk 0 0 (by positivity)) measurable_const

/-- "`W_{u,q}` closes by time `t'`" is a measurable event (on `Good`). -/
theorem measurableSet_cycClosesBy (u : Fin d → ℤ) (q t' : ℝ) :
    MeasurableSet {ν : Measure (RingSpace d β) | Good ν ∧ cycClosesBy ν u q t'} := by
  have hβ : 0 < β := Fact.out
  refine measurableSet_good_and ?_
  have : {ν : GoodSet d β | cycClosesBy ν.1 u q t'} =
      ⋃ n : ℕ, ({_ν : GoodSet d β | 1 ≤ n ∧ (n : ℝ) * β ≤ t'} ∩
        {ν | cycWalk ν.1 u q ((n : ℝ) * β) = u}) := by
    ext ν; simp [cycClosesBy, and_assoc]
  rw [this]
  refine MeasurableSet.iUnion fun n => (MeasurableSet.const _).inter ?_
  exact measurableSet_eq_fun (measurable_cycWalk u q (by positivity)) measurable_const

end ElboimSly.Cyclic

end
