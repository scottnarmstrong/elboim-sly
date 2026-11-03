/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Escape.Plan53Env
public import ElboimSly.Foundations.Cyclic.CycMultiMain
public import ElboimSly.Foundations.Cyclic.CycMultiCond
public import Mathlib

/-!
# The final record of `planA`, and the stopping times `Λ_m`

The walks W_i and the stopping times tau_i (`Λ_i = τ_1 + ⋯ + τ_i`, "a.s. finite stopping times").

* `envFinal_nth`: entry `j` of the final record of `planA` is `escEntry j` for `j < I`, and absent
  otherwise (all stopping lengths are `≤ 4^n`, hence finite);
* `num_envFinal`: the final record has `I` entries;
* `escLam`: `Λ_m = Σ_{ℓ < m} τ_{ℓ+1}`, and `isStoppingTime_escLam`: it is a stopping time of the joint
  exploration filtration.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Escape

open ElboimSly ElboimSly.Cyclic ElboimSly.Paper

variable {k : ℕ} {β : ℝ} [Fact (0 < β)] {n : ℕ} {u : Fin (k + 2) → ℤ} {b : ℕ}
  {hlog : 1 < Real.log β}

theorem envFinal_nth (ν : Measure (CycS ℕ (k + 2) β)) (j : ℕ) :
    ((planA n β u b hlog).envFinal ν).nth j =
      if j < escIstar n (escJ n) then some (escEntry n u b hlog ν j) else none := by
  classical
  have h := CycPlan.cycFinal_nth_gen (planA n β u b hlog) (envRuleA n u b hlog ν) j
  have e : (planA n β u b hlog).envFinal ν =
      (planA n β u b hlog).cycFinal (envRuleA n u b hlog ν) := rfl
  rw [e, h]
  have hc : (planA n β u b hlog).Cont (envRuleA n u b hlog ν) j ↔ j < escIstar n (escJ n) := by
    unfold CycPlan.Cont CycPlan.AllFin
    constructor
    · rintro ⟨h1, -⟩
      have hK : (planA n β u b hlog).K = ((escIstar n (escJ n) : ℕ) : ℕ∞) := rfl
      rw [hK] at h1
      exact_mod_cast h1
    · intro hj
      have hK : (planA n β u b hlog).K = ((escIstar n (escJ n) : ℕ) : ℕ∞) := rfl
      refine ⟨by rw [hK]; exact_mod_cast hj, fun i _ => ?_⟩
      exact lt_top_iff_ne_top.2 (escEntry_len_ne_top i)
  simp only [hc]
  rfl

theorem num_eq_of_nth {d : ℕ} {ρ : CycRec ℕ d} {I : ℕ} {f : ℕ → CycEntry ℕ d}
    (h : ∀ j, ρ.nth j = if j < I then some (f j) else none) : ρ.num = I := by
  rcases ρ with ⟨m, g⟩ | g
  · have h1 : ∀ j, j < m ↔ j < I := fun j => by
      constructor
      · intro hj
        by_contra hI
        have := h j
        simp [CycRec.nth, hj, hI] at this
      · intro hI
        by_contra hj
        have := h j
        simp [CycRec.nth, hj, hI] at this
    have : m = I := by
      by_contra hne
      rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
      · exact absurd ((h1 m).2 hlt) (lt_irrefl _)
      · exact absurd ((h1 I).1 hlt) (lt_irrefl _)
    simp [CycRec.num, this]
  · have := h I
    simp [CycRec.nth] at this

theorem num_envFinal (ν : Measure (CycS ℕ (k + 2) β)) :
    ((planA n β u b hlog).envFinal ν).num = (escIstar n (escJ n) : ℕ∞) :=
  num_eq_of_nth (envFinal_nth ν)

theorem cum_envFinal (ν : Measure (CycS ℕ (k + 2) β)) {m : ℕ} (hm : m ≤ escIstar n (escJ n)) :
    ((planA n β u b hlog).envFinal ν).cum m =
      ∑ i ∈ Finset.range m, (escEntry n u b hlog ν i).len := by
  unfold CycRec.cum
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i < escIstar n (escJ n) := lt_of_lt_of_le (Finset.mem_range.1 hi) hm
  unfold CycRec.lenAt
  rw [envFinal_nth, ite_eq_left hi']
  rfl

theorem cum_envFinal_ne_top (ν : Measure (CycS ℕ (k + 2) β)) {m : ℕ}
    (hm : m ≤ escIstar n (escJ n)) :
    ((planA n β u b hlog).envFinal ν).cum m ≠ ⊤ := by
  rw [cum_envFinal ν hm]
  exact ENNReal.sum_ne_top.2 fun i _ => escEntry_len_ne_top i

/-- `Λ_m = τ_1 + ⋯ + τ_m` as a function of the environment. -/
noncomputable def escLam (n : ℕ) (u : Fin (k + 2) → ℤ) (b : ℕ) (hlog : 1 < Real.log β)
    {Ω : Type*} (N : Ω → Measure (CycS ℕ (k + 2) β)) (m : ℕ) (ω : Ω) : WithTop ℝ≥0 :=
  (((planA n β u b hlog).envFinal (cycNgood N ω)).cum m).toNNReal

section stopping

variable {Ω : Type*} (𝒢₀ : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] {Pr : Measure Ω}
  {N N' : Ω → Measure (CycS ℕ (k + 2) β)}
  (hN : IsPoissonPointProcess N (cycIntensity ℕ (k + 2) β) Pr)

theorem isStoppingTime_escLam (h𝒢 : 𝒢₀ ≤ mΩ) {m : ℕ} (hm : m < escIstar n (escJ n)) :
    IsStoppingTime (cycMultiFilt (planA n β u b hlog) 𝒢₀ hN.measurable h𝒢 Pr)
      (escLam n u b hlog N m) := by
  intro s
  have hR := measurable_envFinal_cycNgood (planA n β u b hlog) hN.measurable
  have htr := measurable_trunc_multiFilt (planA n β u b hlog) 𝒢₀ h𝒢 Pr hR s
  have hset : {ω | escLam n u b hlog N m ω ≤ (s : WithTop ℝ≥0)} =
      (fun ω => CycRec.trunc s ((planA n β u b hlog).envFinal (cycNgood N ω))) ⁻¹'
        {ρ | (m : ℕ∞) < ρ.num} := by
    ext ω
    simp only [mem_ofPred_eq, mem_preimage]
    set R := (planA n β u b hlog).envFinal (cycNgood N ω) with hRdef
    obtain ⟨mm, hmm, hiff, -, -⟩ := CycRec.trunc_spec (planA n β u b hlog).junk s R
    rw [hmm, hiff m]
    have hnum : R.num = (escIstar n (escJ n) : ℕ∞) := num_envFinal _
    have hfin : R.cum m ≠ ⊤ := cum_envFinal_ne_top _ hm.le
    unfold CycRec.surv
    simp only [mem_ofPred_eq]
    rw [hnum]
    have hmI : (m : ℕ∞) < (escIstar n (escJ n) : ℕ∞) := by exact_mod_cast hm
    simp only [hmI, true_and]
    unfold escLam
    rw [← hRdef]
    rw [show ((R.cum m).toNNReal : WithTop ℝ≥0) ≤ (s : WithTop ℝ≥0) ↔ (R.cum m).toNNReal ≤ s from
      WithTop.coe_le_coe]
    rw [← ENNReal.coe_le_coe, ENNReal.coe_toNNReal hfin]
  rw [hset]
  exact htr (CycRec.measurable_num (MeasurableSet.of_discrete (s := {x : ℕ∞ | (m : ℕ∞) < x})))

end stopping

end ElboimSly.Paper.Escape
