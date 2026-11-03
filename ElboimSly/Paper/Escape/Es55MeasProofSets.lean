/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Escape.Es55MeasProofExit
public import ElboimSly.Paper.Escape.Es55MeasProofStop
public import Mathlib

/-!
# `𝒦(β') ∩ 𝒜_i` and the exit event as events of the first entries

ES22 Lemma 5.5 (measurability data).

`exists_phi_KA`, `exists_phi_KAE`: the events `𝒦(β') ∩ 𝒜_i` and `𝒦(β') ∩ 𝒜_i ∩ {exit}` are
`CycGood` and a measurable property of the first `I + 1`, respectively `I + 2`, final entries of
`plan5`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace ElboimSly.Paper.Escape

open ElboimSly ElboimSly.Cyclic ElboimSly.Cyclic.CycSchemeEnv ElboimSly.Paper

set_option linter.unusedSectionVars false

variable {k : ℕ} {β : ℝ} [Fact (0 < β)]

theorem measurable_cycIntPhase_floor (β : ℝ) (c : ℝ) :
    Measurable fun x : ℝ => cycIntPhase β (cycFloor β (x + c)) := by
  unfold cycIntPhase cycFloor
  fun_prop

theorem measurableSet_escG0 (β tn : ℝ) (j : ℕ) (Bm : Set (EscV k)) (β' : ℕ) :
    MeasurableSet {e : CycEntry ℕ (k + 2) | EscG0 β tn j Bm β' e} := by
  have h1 : MeasurableSet {e : CycEntry ℕ (k + 2) | e.len ≤ ENNReal.ofReal tn} :=
    measurableSet_le measurable_entry_len' measurable_const
  have h2 : MeasurableSet {e : CycEntry ℕ (k + 2) | entEnd e ∈ Bm} :=
    measurable_entEnd (Set.to_countable Bm).measurableSet
  have h3 : MeasurableSet {e : CycEntry ℕ (k + 2) | closeSt β e.2 = false} :=
    ((measurable_closeSt β).comp measurable_snd) (measurableSet_singleton false)
  have h4 : MeasurableSet {e : CycEntry ℕ (k + 2) |
      cycIntPhase β (cycFloor β (e.len.toReal + 4 ^ j)) = (β' : ℝ)} :=
    ((measurable_cycIntPhase_floor β ((4 : ℝ) ^ j)).comp
      (ENNReal.measurable_toReal.comp measurable_entry_len')) (measurableSet_singleton _)
  have : {e : CycEntry ℕ (k + 2) | EscG0 β tn j Bm β' e} = {e | e.len ≤ ENNReal.ofReal tn} ∩
      ({e | entEnd e ∈ Bm} ∩ ({e | closeSt β e.2 = false} ∩
        {e | cycIntPhase β (cycFloor β (e.len.toReal + 4 ^ j)) = (β' : ℝ)})) := by
    ext e; simp [EscG0]
  rw [this]
  exact h1.inter (h2.inter (h3.inter h4))

theorem measurableSet_escH (j : ℕ) (u : EscV k) (S : ℝ≥0) :
    MeasurableSet {e : CycEntry ℕ (k + 2) | EscH j u S e} := by
  have h1 : MeasurableSet {e : CycEntry ℕ (k + 2) | e.path.fn 0 ∈ escQ j u} :=
    (measurable_entEval 0) (Set.to_countable _).measurableSet
  have h2 : MeasurableSet {e : CycEntry ℕ (k + 2) | e.len ≤ (S : ℝ≥0∞)} :=
    measurableSet_le measurable_entry_len' measurable_const
  have h3 : MeasurableSet {e : CycEntry ℕ (k + 2) | entEnd e ∈ escFace j u} :=
    measurable_entEnd (Set.to_countable _).measurableSet
  have : {e : CycEntry ℕ (k + 2) | EscH j u S e} = {e | e.path.fn 0 ∈ escQ j u} ∩
      ({e | e.len ≤ (S : ℝ≥0∞)} ∩ {e | entEnd e ∈ escFace j u}) := by
    ext e; simp [EscH]
  rw [this]
  exact h1.inter (h2.inter h3)

section KA

variable (n : ℕ) (tn : ℝ) (u : EscV k) (β' i : ℕ) (hlog : 1 < Real.log β)

theorem mem_KA_iff (hi1 : 1 ≤ i) (hiI : i ≤ escIstar n (escJ n))
    (ν : Measure (CycS ℕ (k + 2) β)) :
    ν ∈ escKSet β tn n β' u ∩ escASet n u β' hlog i ↔
      CycGood ν ∧ (EscG0 β tn (escJ n) (escBlockMinus (escJ n) u) β'
        (ent5 n tn u β' i hlog ν 0) ∧ (ent5 n tn u β' i hlog ν i).len = (4 : ℝ≥0∞) ^ n) := by
  have hent := ent5_succ_eq_escEntry n tn u β' i hlog ν (i - 1) (by omega)
  rw [show i - 1 + 1 = i by omega] at hent
  simp only [mem_inter_iff, escKSet, escASet, mem_ofPred_eq]
  constructor
  · rintro ⟨⟨hν, hK⟩, -, hA⟩
    exact ⟨hν, (escK_iff_G0 n tn u β' i hlog ν hν).1 hK, by rw [hent]; exact hA⟩
  · rintro ⟨hν, hG, hA⟩
    exact ⟨⟨hν, (escK_iff_G0 n tn u β' i hlog ν hν).2 hG⟩, hν, by rw [← hent]; exact hA⟩

theorem exists_phi_KA (hi1 : 1 ≤ i) (hiI : i ≤ escIstar n (escJ n)) :
    ∃ Φ : Set (Fin (escIstar n (escJ n) + 1) → CycEntry ℕ (k + 2)), MeasurableSet Φ ∧
      ∀ ν : Measure (CycS ℕ (k + 2) β), ν ∈ escKSet β tn n β' u ∩ escASet n u β' hlog i ↔
        CycGood ν ∧ (fun m : Fin (escIstar n (escJ n) + 1) =>
          (plan5 n β tn u β' i hlog).E (rule (plan5 n β tn u β' i hlog) ν) m) ∈ Φ := by
  refine ⟨{f | EscG0 β tn (escJ n) (escBlockMinus (escJ n) u) β' (f ⟨0, by omega⟩) ∧
    (f ⟨i, by omega⟩).len = (4 : ℝ≥0∞) ^ n}, ?_, fun ν => ?_⟩
  · have h1 : MeasurableSet ((fun f : Fin (escIstar n (escJ n) + 1) → CycEntry ℕ (k + 2) =>
        f ⟨0, by omega⟩) ⁻¹' {e | EscG0 β tn (escJ n) (escBlockMinus (escJ n) u) β' e}) :=
      (measurable_pi_apply (⟨0, by omega⟩ : Fin (escIstar n (escJ n) + 1)))
        (measurableSet_escG0 β tn (escJ n) (escBlockMinus (escJ n) u) β')
    have h2 : MeasurableSet {f : Fin (escIstar n (escJ n) + 1) → CycEntry ℕ (k + 2) |
        (f ⟨i, by omega⟩).len = (4 : ℝ≥0∞) ^ n} :=
      (measurable_entry_len'.comp
        (measurable_pi_apply (⟨i, by omega⟩ : Fin (escIstar n (escJ n) + 1))))
        (measurableSet_singleton _)
    exact h1.inter h2
  · rw [mem_KA_iff n tn u β' i hlog hi1 hiI ν]
    rfl

theorem mem_KAE_iff (hi1 : 1 ≤ i) (hiI : i ≤ escIstar n (escJ n)) (hj : 1 ≤ escJ n)
    (ν : Measure (CycS ℕ (k + 2) β)) :
    ν ∈ (escKSet β tn n β' u ∩ escASet n u β' hlog i) ∩ es55Exit β n u β' i ↔
      CycGood ν ∧ (EscG0 β tn (escJ n) (escBlockMinus (escJ n) u) β'
        (ent5 n tn u β' i hlog ν 0) ∧ (ent5 n tn u β' i hlog ν i).len = (4 : ℝ≥0∞) ^ n ∧
        EscH (escJ n) u (Real.toNNReal (((2 : ℝ) ^ escJ n) ^ 2 / 4))
          (ent5 n tn u β' i hlog ν (escIstar n (escJ n) + 1))) := by
  constructor
  · rintro ⟨hKA, hE⟩
    obtain ⟨hν, hG, hA⟩ := (mem_KA_iff n tn u β' i hlog hi1 hiI ν).1 hKA
    exact ⟨hν, hG, hA, (mem_es55Exit_iff n tn u β' i hlog ν hν hj).1 hE⟩
  · rintro ⟨hν, hG, hA, hH⟩
    exact ⟨(mem_KA_iff n tn u β' i hlog hi1 hiI ν).2 ⟨hν, hG, hA⟩,
      (mem_es55Exit_iff n tn u β' i hlog ν hν hj).2 hH⟩

theorem exists_phi_KAE (hi1 : 1 ≤ i) (hiI : i ≤ escIstar n (escJ n)) (hj : 1 ≤ escJ n) :
    ∃ Φ : Set (Fin (escIstar n (escJ n) + 2) → CycEntry ℕ (k + 2)), MeasurableSet Φ ∧
      ∀ ν : Measure (CycS ℕ (k + 2) β),
        ν ∈ (escKSet β tn n β' u ∩ escASet n u β' hlog i) ∩ es55Exit β n u β' i ↔
        CycGood ν ∧ (fun m : Fin (escIstar n (escJ n) + 2) =>
          (plan5 n β tn u β' i hlog).E (rule (plan5 n β tn u β' i hlog) ν) m) ∈ Φ := by
  refine ⟨{f | EscG0 β tn (escJ n) (escBlockMinus (escJ n) u) β' (f ⟨0, by omega⟩) ∧
    (f ⟨i, by omega⟩).len = (4 : ℝ≥0∞) ^ n ∧
    EscH (escJ n) u (Real.toNNReal (((2 : ℝ) ^ escJ n) ^ 2 / 4))
      (f ⟨escIstar n (escJ n) + 1, by omega⟩)}, ?_, fun ν => ?_⟩
  · have h1 : MeasurableSet ((fun f : Fin (escIstar n (escJ n) + 2) → CycEntry ℕ (k + 2) =>
        f ⟨0, by omega⟩) ⁻¹' {e | EscG0 β tn (escJ n) (escBlockMinus (escJ n) u) β' e}) :=
      (measurable_pi_apply (⟨0, by omega⟩ : Fin (escIstar n (escJ n) + 2)))
        (measurableSet_escG0 β tn (escJ n) (escBlockMinus (escJ n) u) β')
    have h2 : MeasurableSet {f : Fin (escIstar n (escJ n) + 2) → CycEntry ℕ (k + 2) |
        (f ⟨i, by omega⟩).len = (4 : ℝ≥0∞) ^ n} :=
      (measurable_entry_len'.comp
        (measurable_pi_apply (⟨i, by omega⟩ : Fin (escIstar n (escJ n) + 2))))
        (measurableSet_singleton _)
    have h3 : MeasurableSet ((fun f : Fin (escIstar n (escJ n) + 2) → CycEntry ℕ (k + 2) =>
        f ⟨escIstar n (escJ n) + 1, by omega⟩) ⁻¹'
        {e | EscH (escJ n) u (Real.toNNReal (((2 : ℝ) ^ escJ n) ^ 2 / 4)) e}) :=
      (measurable_pi_apply (⟨escIstar n (escJ n) + 1, by omega⟩ :
        Fin (escIstar n (escJ n) + 2))) (measurableSet_escH _ _ _)
    exact h1.inter (h2.inter h3)
  · rw [mem_KAE_iff n tn u β' i hlog hi1 hiI hj ν]
    rfl

end KA

end ElboimSly.Paper.Escape
