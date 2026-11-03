/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Escape.Es52Meas
public import ElboimSly.Paper.Heavy.Entrance
public import ElboimSly.Paper.Heavy.RegenCyclic
public import ElboimSly.Foundations.Cyclic.CycRegenCoupleDef
public import ElboimSly.Foundations.Cyclic.CycEvents
public import Mathlib

/-!
# Measurability of the event `Con_i`

ES22 Lemma 5.5.

On good environments `escWalk ν s = regW ν s` (a measurable function of `ν`), the first entrance
time is measurable (`escXi` is the entrance time of a cyclic path, determined by rational times),
and `t' = cycFloor β (ξ + 4^j)` takes values in the countable set `{β m + z}`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace ElboimSly.Paper.Escape

open ElboimSly ElboimSly.Cyclic ElboimSly.Paper

set_option linter.unusedSectionVars false

variable {k : ℕ} {β : ℝ} [Fact (0 < β)]

theorem escXi_eq_entranceTime (W : ℝ → Fin (k + 2) → ℤ) (B : Set (Fin (k + 2) → ℤ)) :
    escXi W B = entranceTime W B := by
  apply le_antisymm
  · refine le_iInf₂ fun t ht => ?_
    refine iInf₂_le_of_le t.toNNReal ?_ le_rfl
    rw [Real.coe_toNNReal t ht.1]; exact ht.2
  · refine le_iInf₂ fun t ht => ?_
    refine iInf₂_le_of_le (t : ℝ) ⟨t.2, ht⟩ ?_
    rw [ENNReal.ofReal_coe_nnreal]

theorem escWalk_eq_regW {ν : Measure (CycS ℕ (k + 2) β)} (hν : CycGood ν) (s : ℝ≥0) :
    escWalk ν (s : ℝ) = regW ν s := by
  rw [regW_eq_regenWalk hν]
  unfold escWalk
  congr 2
  funext i
  exact copyEnv_eq_cycSlice ν i

theorem escWalk_eq_regW' {ν : Measure (CycS ℕ (k + 2) β)} (hν : CycGood ν) {s : ℝ}
    (hs : 0 ≤ s) : escWalk ν s = regW ν s.toNNReal := by
  rw [← escWalk_eq_regW hν, Real.coe_toNNReal s hs]

theorem isCyclicPath_escWalk {ν : Measure (CycS ℕ (k + 2) β)} (hν : CycGood ν) :
    IsCyclicPath (escWalk ν) := by
  refine ElboimSly.Paper.Heavy.isCyclicPath_regenWalk fun i => ?_
  rw [copyEnv_eq_cycSlice]
  exact hν i

theorem measurable_regW_apply (s : ℝ≥0) :
    Measurable fun ν : Measure (CycS ℕ (k + 2) β) => regW ν s :=
  (measurable_pi_apply s).comp measurable_regW

theorem measurableSet_regW_mem (s : ℝ≥0) (B : Set (Fin (k + 2) → ℤ)) :
    MeasurableSet {ν : Measure (CycS ℕ (k + 2) β) | regW ν s ∈ B} :=
  measurable_regW_apply s (Set.to_countable B).measurableSet

theorem measurableSet_xi_le (B : Set (Fin (k + 2) → ℤ)) {t : ℝ} (ht : 0 ≤ t) :
    MeasurableSet {ν : Measure (CycS ℕ (k + 2) β) |
      CycGood ν ∧ escXi (escWalk ν) B ≤ ENNReal.ofReal t} := by
  have hset : {ν : Measure (CycS ℕ (k + 2) β) |
      CycGood ν ∧ escXi (escWalk ν) B ≤ ENNReal.ofReal t} =
      {ν | CycGood ν} ∩ ({ν | regW ν t.toNNReal ∈ B} ∪
        ⋃ q : ℚ, ⋃ (_ : 0 ≤ (q : ℝ) ∧ (q : ℝ) < t), {ν | regW ν (q : ℝ).toNNReal ∈ B}) := by
    ext ν
    simp only [mem_ofPred_eq, mem_inter_iff, mem_union, mem_iUnion, exists_prop]
    refine and_congr_right fun hν => ?_
    rw [escXi_eq_entranceTime, entranceTime_le_iff (isCyclicPath_escWalk hν) ht,
      escWalk_eq_regW' hν ht]
    refine or_congr Iff.rfl ?_
    constructor
    · rintro ⟨q, h0, h1, h2⟩
      exact ⟨q, ⟨h0, h1⟩, by rwa [escWalk_eq_regW' hν h0] at h2⟩
    · rintro ⟨q, ⟨h0, h1⟩, h2⟩
      exact ⟨q, h0, h1, by rwa [escWalk_eq_regW' hν h0]⟩
  rw [hset]
  refine measurableSet_cycGood.inter ((measurableSet_regW_mem _ B).union ?_)
  exact MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun _ => measurableSet_regW_mem _ B

open Classical in
/-- `ξ_B`, totalized by `0` off the good environments. -/
noncomputable def escXiTot (B : Set (Fin (k + 2) → ℤ)) (ν : Measure (CycS ℕ (k + 2) β)) : ℝ≥0∞ :=
  if CycGood ν then escXi (escWalk ν) B else 0

theorem escXiTot_eq {B : Set (Fin (k + 2) → ℤ)} {ν : Measure (CycS ℕ (k + 2) β)}
    (hν : CycGood ν) : escXiTot B ν = escXi (escWalk ν) B := by
  simp [escXiTot, hν]

theorem measurable_escXiTot (B : Set (Fin (k + 2) → ℤ)) :
    Measurable (escXiTot (β := β) B) := by
  refine measurable_of_Iic fun a => ?_
  by_cases ha : a = ⊤
  · subst ha; simp
  · have h0 : 0 ≤ a.toReal := ENNReal.toReal_nonneg
    have hset : escXiTot (β := β) B ⁻¹' Iic a =
        {ν | CycGood ν ∧ escXi (escWalk ν) B ≤ ENNReal.ofReal a.toReal} ∪ {ν | CycGood ν}ᶜ := by
      ext ν
      by_cases hν : CycGood ν
      · simp [escXiTot_eq hν, hν, ENNReal.ofReal_toReal ha]
      · simp [escXiTot, hν]
    rw [hset]
    exact (measurableSet_xi_le B h0).union measurableSet_cycGood.compl

/-- If `P · c` is measurable for each real `c`, then so is `P · (cycFloor β (x ·))`. -/
theorem measurableSet_cycFloor_comp {α : Type*} [MeasurableSpace α] {x : α → ℝ}
    (hx : Measurable x) (P : α → ℝ → Prop) (hP : ∀ c : ℝ, MeasurableSet {a | P a c}) :
    MeasurableSet {a | P a (cycFloor β (x a))} := by
  have hset : {a | P a (cycFloor β (x a))} = ⋃ p : ℤ × ℤ,
      {a | cycFloor β (x a) = β * p.1 + p.2} ∩ {a | P a (β * p.1 + p.2)} := by
    ext a
    simp only [mem_ofPred_eq, mem_iUnion, mem_inter_iff]
    constructor
    · intro h
      refine ⟨(⌊x a / β⌋, ⌊x a - β * ⌊x a / β⌋⌋), ?_, ?_⟩
      · simp [cycFloor]
      · have : cycFloor β (x a) = β * ((⌊x a / β⌋ : ℤ) : ℝ) + ((⌊x a - β * ⌊x a / β⌋⌋ : ℤ) : ℝ) :=
          rfl
        simpa [this] using h
    · rintro ⟨p, h1, h2⟩
      rw [h1]; exact h2
  rw [hset]
  refine MeasurableSet.iUnion fun p => MeasurableSet.inter ?_ (hP _)
  exact (measurable_cycFloor_e52 β |>.comp hx) (measurableSet_singleton _)

theorem measurableSet_escConSet (n : ℕ) (u : Fin (k + 2) → ℤ) (i : ℕ) :
    MeasurableSet (escConSet β n u i) := by
  set B := escBlock (escJ n) u with hB
  set x : Measure (CycS ℕ (k + 2) β) → ℝ := fun ν => (escXiTot B ν).toReal + 4 ^ escJ n with hx
  have hxm : Measurable x :=
    (ENNReal.measurable_toReal.comp (measurable_escXiTot B)).add_const _
  set P : Measure (CycS ℕ (k + 2) β) → ℝ → Prop := fun ν c =>
    CycGood ν ∧ ENNReal.ofReal c < cycTreg (copyEnv ν 0) ∧
      regW ν c.toNNReal = escPoint n (escJ n) u i with hP
  have hPm : ∀ c : ℝ, MeasurableSet {ν | P ν c} := by
    intro c
    have h1 : MeasurableSet {ν : Measure (CycS ℕ (k + 2) β) |
        CycGood ν ∧ ENNReal.ofReal c < cycTreg (copyEnv ν 0)} := by
      have hle : MeasurableSet {ν : Measure (CycS ℕ (k + 2) β) |
          Good (cycSlice 0 ν) ∧ cycTreg (cycSlice 0 ν) ≤ ENNReal.ofReal c} :=
        (measurable_cycSlice (I := ℕ) (d := k + 2) (β := β) 0) (measurableSet_cycTreg_le c)
      have : {ν : Measure (CycS ℕ (k + 2) β) |
          CycGood ν ∧ ENNReal.ofReal c < cycTreg (copyEnv ν 0)} =
          {ν | CycGood ν} \ {ν | Good (cycSlice 0 ν) ∧ cycTreg (cycSlice 0 ν) ≤ ENNReal.ofReal c} := by
        ext ν
        simp only [mem_ofPred_eq, mem_sdiff, copyEnv_eq_cycSlice]
        constructor
        · rintro ⟨h1, h2⟩; exact ⟨h1, fun h => absurd h.2 (not_le.2 h2)⟩
        · rintro ⟨h1, h2⟩
          exact ⟨h1, not_le.1 fun h => h2 ⟨h1 0, h⟩⟩
      rw [this]
      exact measurableSet_cycGood.diff hle
    have h2 : MeasurableSet {ν : Measure (CycS ℕ (k + 2) β) |
        regW ν c.toNNReal = escPoint n (escJ n) u i} :=
      measurableSet_regW_mem _ {escPoint n (escJ n) u i}
    have : {ν | P ν c} = {ν : Measure (CycS ℕ (k + 2) β) |
        CycGood ν ∧ ENNReal.ofReal c < cycTreg (copyEnv ν 0)} ∩
        {ν | regW ν c.toNNReal = escPoint n (escJ n) u i} := by
      ext ν; simp [hP, and_assoc]
    rw [this]
    exact h1.inter h2
  have hset : escConSet β n u i = {ν | CycGood ν} ∩ {ν | escXiTot B ν ≠ ⊤} ∩
      {ν | P ν (cycFloor β (x ν))} := by
    ext ν
    simp only [escConSet, mem_inter_iff, mem_ofPred_eq]
    constructor
    · rintro ⟨hν, h1, h2, h3⟩
      have hX := escXiTot_eq (B := B) hν
      have hnn : 0 ≤ (escXi (escWalk ν) B).toReal + 4 ^ escJ n := by positivity
      have hf : 0 ≤ cycFloor β ((escXi (escWalk ν) B).toReal + 4 ^ escJ n) :=
        (cycFloor_mem (Fact.out : 0 < β) hnn).1
      refine ⟨⟨hν, by rw [hX]; exact h1⟩, hν, ?_, ?_⟩
      · simpa [hx, hX] using h2
      · simp only [hx, hX]
        rw [← escWalk_eq_regW' hν hf]; exact h3
    · rintro ⟨⟨hν, h1⟩, -, h2, h3⟩
      have hX := escXiTot_eq (B := B) hν
      have hnn : 0 ≤ (escXi (escWalk ν) B).toReal + 4 ^ escJ n := by positivity
      have hf : 0 ≤ cycFloor β ((escXi (escWalk ν) B).toReal + 4 ^ escJ n) :=
        (cycFloor_mem (Fact.out : 0 < β) hnn).1
      refine ⟨hν, by rwa [hX] at h1, ?_, ?_⟩
      · simpa [hx, hX] using h2
      · simp only [hx, hX] at h3
        rw [escWalk_eq_regW' hν hf]; exact h3
  rw [hset]
  exact (measurableSet_cycGood.inter (measurable_escXiTot B (measurableSet_singleton ⊤).compl)).inter
    (measurableSet_cycFloor_comp hxm P hPm)

end ElboimSly.Paper.Escape
