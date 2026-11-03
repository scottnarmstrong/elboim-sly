/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Escape.Plan53Rec
public import ElboimSly.Foundations.Cyclic.CycMultiCond
public import Mathlib

/-!
# `𝒜_ℓ ∈ 𝒢_ℓ`

ES22 Corollary 5.4 ("`𝒜_ℓ ∈ 𝒢_ℓ ⊆ 𝒢_{i-1}` for `ℓ < i`").  The event `𝒜_ℓ = {τ_ℓ = 4^n}` is measurable
for the stopped σ-algebra `ℱ_{Λ_ℓ}` (`measurableSet_A_stopped`) and for the ambient σ-algebra
(`measurableSet_A`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace ElboimSly.Paper.Escape

open ElboimSly ElboimSly.Cyclic ElboimSly.Paper

variable {k : ℕ} {β : ℝ} [Fact (0 < β)] {n : ℕ} {u : Fin (k + 2) → ℤ} {b : ℕ}
  {hlog : 1 < Real.log β}

theorem trunc_coord_complete (junk : CycEntry ℕ (k + 2)) (ρ : CycRec ℕ (k + 2)) (s : ℝ≥0)
    {j : ℕ} (hj : (j : ℕ∞) < ρ.num) (hc : ρ.cum (j + 1) ≤ s) :
    (CycRec.trunc s ρ).coord junk j = ρ.coord junk j := by
  obtain ⟨mm, hmm, hiff, hcoord, -⟩ := CycRec.trunc_spec junk s ρ
  have hsurv : j ∈ ρ.surv s := ⟨hj, (CycRec.cum_mono ρ (Nat.le_succ j)).trans hc⟩
  rw [hcoord j hsurv]
  unfold CycRec.truncEntry
  rw [ite_eq_left hc]

/-- The event `𝒜_ℓ`: the walk `ℓ + 1` runs to `4^n`. -/
def EscAEv (n : ℕ) (u : Fin (k + 2) → ℤ) (b : ℕ) (hlog : 1 < Real.log β) {Ω : Type*}
    (N : Ω → Measure (CycS ℕ (k + 2) β)) (ℓ : ℕ) : Set Ω :=
  {ω | (escEntry n u b hlog (cycNgood N ω) ℓ).len = (4 : ℝ≥0∞) ^ n}

theorem escEntry_len_eq_coord (ν : Measure (CycS ℕ (k + 2) β)) {ℓ : ℕ}
    (hℓ : ℓ < escIstar n (escJ n)) :
    (escEntry n u b hlog ν ℓ).len =
      (((planA n β u b hlog).envFinal ν).coord (planA n β u b hlog).junk ℓ).len := by
  unfold CycRec.coord
  rw [envFinal_nth, ite_eq_left hℓ]; rfl

theorem measurableSet_A {Ω : Type*} [MeasurableSpace Ω] {N : Ω → Measure (CycS ℕ (k + 2) β)}
    (hNm : Measurable N) {ℓ : ℕ} (hℓ : ℓ < escIstar n (escJ n)) :
    MeasurableSet (EscAEv n u b hlog N ℓ) := by
  have hR := measurable_envFinal_cycNgood (planA n β u b hlog) hNm
  have hlen : Measurable fun ω => (((planA n β u b hlog).envFinal (cycNgood N ω)).coord
      (planA n β u b hlog).junk ℓ).len :=
    measurable_entry_len'.comp ((CycRec.measurable_coord (planA n β u b hlog).junk ℓ).comp hR)
  have : EscAEv n u b hlog N ℓ = {ω | (((planA n β u b hlog).envFinal (cycNgood N ω)).coord
      (planA n β u b hlog).junk ℓ).len = (4 : ℝ≥0∞) ^ n} := by
    ext ω
    simp only [EscAEv, mem_ofPred_eq]
    rw [escEntry_len_eq_coord _ hℓ]
  rw [this]
  exact hlen (measurableSet_singleton _)

section stopped

variable {Ω : Type*} (𝒢₀ : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] {Pr : Measure Ω}
  {N : Ω → Measure (CycS ℕ (k + 2) β)}
  (hN : IsPoissonPointProcess N (cycIntensity ℕ (k + 2) β) Pr)

theorem measurableSet_A_stopped (h𝒢 : 𝒢₀ ≤ mΩ) {ℓ : ℕ} (hℓ : ℓ + 1 < escIstar n (escJ n)) :
    MeasurableSet[(isStoppingTime_escLam (u := u) (b := b) (hlog := hlog) 𝒢₀ hN h𝒢
      hℓ).measurableSpace] (EscAEv n u b hlog N ℓ) := by
  have hT := isStoppingTime_escLam (u := u) (b := b) (hlog := hlog) 𝒢₀ hN h𝒢 hℓ
  have hℓ' : ℓ < escIstar n (escJ n) := by omega
  have hR := measurable_envFinal_cycNgood (planA n β u b hlog) hN.measurable
  -- the key set identity at every time `t`
  have key : ∀ t : ℝ≥0, MeasurableSet[cycMultiFilt (planA n β u b hlog) 𝒢₀ hN.measurable h𝒢 Pr t]
      (EscAEv n u b hlog N ℓ ∩ {ω | escLam n u b hlog N (ℓ + 1) ω ≤ (t : WithTop ℝ≥0)}) := by
    intro t
    have htr := measurable_trunc_multiFilt (planA n β u b hlog) 𝒢₀ h𝒢 Pr hR t
    have hset : EscAEv n u b hlog N ℓ ∩ {ω | escLam n u b hlog N (ℓ + 1) ω ≤ (t : WithTop ℝ≥0)} =
        ((fun ω => (((CycRec.trunc t ((planA n β u b hlog).envFinal (cycNgood N ω))).coord
          (planA n β u b hlog).junk ℓ).len)) ⁻¹' {(4 : ℝ≥0∞) ^ n}) ∩
          {ω | escLam n u b hlog N (ℓ + 1) ω ≤ (t : WithTop ℝ≥0)} := by
      ext ω
      simp only [mem_inter_iff, mem_preimage, mem_singleton_iff, EscAEv, mem_ofPred_eq]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨?_, h2⟩
        set R := (planA n β u b hlog).envFinal (cycNgood N ω) with hRdef
        have hfin : R.cum (ℓ + 1) ≠ ⊤ := cum_envFinal_ne_top _ hℓ.le
        have hc : R.cum (ℓ + 1) ≤ (t : ℝ≥0∞) := by
          have : (R.cum (ℓ + 1)).toNNReal ≤ t := WithTop.coe_le_coe.1 h2
          rw [← ENNReal.coe_toNNReal hfin]; exact_mod_cast this
        rw [trunc_coord_complete _ R t (by rw [hRdef, num_envFinal]; exact_mod_cast hℓ') hc]
        rw [← escEntry_len_eq_coord _ hℓ']; exact h1
      · rintro ⟨h1, h2⟩
        refine ⟨?_, h2⟩
        set R := (planA n β u b hlog).envFinal (cycNgood N ω) with hRdef
        have hfin : R.cum (ℓ + 1) ≠ ⊤ := cum_envFinal_ne_top _ hℓ.le
        have hc : R.cum (ℓ + 1) ≤ (t : ℝ≥0∞) := by
          have : (R.cum (ℓ + 1)).toNNReal ≤ t := WithTop.coe_le_coe.1 h2
          rw [← ENNReal.coe_toNNReal hfin]; exact_mod_cast this
        rw [trunc_coord_complete _ R t (by rw [hRdef, num_envFinal]; exact_mod_cast hℓ') hc] at h1
        rw [escEntry_len_eq_coord _ hℓ']; exact h1
    rw [hset]
    refine MeasurableSet.inter ?_ (hT t)
    exact ((measurable_entry_len'.comp
      ((CycRec.measurable_coord (planA n β u b hlog).junk ℓ).comp htr))
      (measurableSet_singleton _))
  refine ⟨?_, fun t => key t⟩
  -- `𝒜_ℓ` is measurable for `⨆ ℱ_t`: it is `𝒜_ℓ ∩ {Λ ≤ t₀}` for `t₀ = I 4^n`
  set t₀ : ℝ≥0 := (escIstar n (escJ n) : ℝ≥0) * 4 ^ n with ht₀
  have hall : ∀ ω, escLam n u b hlog N (ℓ + 1) ω ≤ (t₀ : WithTop ℝ≥0) := by
    intro ω
    unfold escLam
    refine WithTop.coe_le_coe.2 ?_
    rw [← ENNReal.coe_le_coe, ENNReal.coe_toNNReal (cum_envFinal_ne_top _ hℓ.le)]
    rw [cum_envFinal _ hℓ.le]
    calc ∑ i ∈ Finset.range (ℓ + 1), (escEntry n u b hlog (cycNgood N ω) i).len
        ≤ ∑ i ∈ Finset.range (ℓ + 1), (4 : ℝ≥0∞) ^ n :=
          Finset.sum_le_sum fun i _ => escEntry_len_le i
      _ = ((ℓ + 1 : ℕ) : ℝ≥0∞) * 4 ^ n := by simp
      _ ≤ (escIstar n (escJ n) : ℝ≥0∞) * 4 ^ n := by
          gcongr
      _ = _ := by rw [ht₀]; push_cast; rfl
  have h1 := key t₀
  have : EscAEv n u b hlog N ℓ ∩ {ω | escLam n u b hlog N (ℓ + 1) ω ≤ (t₀ : WithTop ℝ≥0)} =
      EscAEv n u b hlog N ℓ := by
    ext ω; exact ⟨fun h => h.1, fun h => ⟨h, hall ω⟩⟩
  rw [this] at h1
  exact (le_iSup (cycMultiFilt (planA n β u b hlog) 𝒢₀ hN.measurable h𝒢 Pr) t₀) _ h1

end stopped

end ElboimSly.Paper.Escape
