/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Escape.C57Jump
public import ElboimSly.Paper.Escape.C57Rec
public import ElboimSly.Paper.Escape.PointGeom
public import ElboimSly.Foundations.Cyclic.CycEnvMeas
public import ElboimSly.Foundations.Cyclic.CycPlanCouplingDef
public import Mathlib

/-!
# The exit event of ES22 Claim 5.7 as a set of environments

The box escQ, the backward walks and zeta_i; ES22 Claim 5.7.

* `escPoint_mem_escQ`: `p_i ∈ 𝒬` (as `i λ_n ≤ 3·2^{j-4}`);
* `exitSet`: the set of environments `ν` for which the backward walk
  `W_i^← = P^ν_{(0, p_i, β', -1)}` leaves `𝒬` at the `a`-th jump, at a time `≤ 4^{j-1}`, at a point
  of `F_B` (the event `{r_i ≤ 4^{j-1}, W_i^←(r_i) ∈ F_B}`); it is defined through the
  good version `cycNgood` of `ν` and is measurable.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Escape

open ElboimSly ElboimSly.Cyclic ElboimSly.Paper

set_option linter.unusedSectionVars false

variable {k : ℕ}

theorem escPoint_mem_escQ {n j : ℕ} (hj : 4 ≤ j) {u : EscV k} {i : ℕ}
    (hi : 16 * (i * escLambda n) ≤ 3 * 2 ^ j) : escPoint n j u i ∈ escQ j u := by
  obtain ⟨m, rfl⟩ : ∃ m, j = m + 4 := ⟨j - 4, by omega⟩
  have hp : (2 : ℤ) ^ (m + 4) = 16 * 2 ^ m := by ring
  have hm : (1 : ℤ) ≤ 2 ^ m := one_le_pow₀ (by norm_num)
  have hi' : (16 : ℤ) * ((i : ℤ) * (escLambda n : ℤ)) ≤ 3 * 2 ^ (m + 4) := by exact_mod_cast hi
  have hi0 : (0 : ℤ) ≤ (i : ℤ) * (escLambda n : ℤ) := by positivity
  rw [hp] at hi'
  refine ⟨?_, fun c hc => ?_⟩
  · simp only [escPoint, ite_true, ite_eq_right (show (0 : Fin (k + 2)) ≠ 1 from by simp), hp]
    generalize (2 : ℤ) ^ m = X at *
    constructor <;> omega
  · by_cases hc1 : c = 1
    · subst hc1
      simp only [escPoint, ite_eq_right hc, ite_true, hp]
      generalize (2 : ℤ) ^ m = X at *
      constructor <;> omega
    · simp only [escPoint, ite_eq_right hc, ite_eq_right hc1, hp]
      generalize (2 : ℤ) ^ m = X at *
      constructor <;> omega

variable {β : ℝ} [Fact (0 < β)]

/-- The environment path of the backward walk in the good version of `ν`. -/
noncomputable def exitPath (δ : CycData ℕ (k + 2)) (ν : Measure (CycS ℕ (k + 2) β)) :
    CycPath (k + 2) :=
  envPath (cycNgood (fun ν : Measure (CycS ℕ (k + 2) β) => ν) ν) δ

theorem measurable_exitPath (δ : CycData ℕ (k + 2)) :
    Measurable (fun ν : Measure (CycS ℕ (k + 2) β) => (exitPath δ ν).1) := by
  have hg : Measurable fun ν : Measure (CycS ℕ (k + 2) β) =>
      (⟨cycNgood (fun ν : Measure (CycS ℕ (k + 2) β) => ν) ν, cycGood_cycNgood _ _⟩ :
        CycGoodSet ℕ (k + 2) β) :=
    Measurable.subtype_mk (measurable_cycNgood measurable_id)
  have h1 := (measurable_envPath (I := ℕ) (d := k + 2) (β := β)).comp
    (hg.prodMk (measurable_const (a := δ)))
  have h2 := measurable_subtype_coe.comp h1
  exact h2

/-- The set of environments for which the backward walk exits `𝒬` at the `a`-th jump, at a time
`≤ S`, at a point of `F_B`. -/
def exitSet (j : ℕ) (u : EscV k) (S : ℝ≥0) (δ : CycData ℕ (k + 2)) :
    Set (Measure (CycS ℕ (k + 2) β)) :=
  {ν | ExitJ (escQ j u) (escFace j u) (S : ℝ≥0∞) (exitPath δ ν).1}

theorem measurableSet_exitSet (j : ℕ) (u : EscV k) (S : ℝ≥0) (δ : CycData ℕ (k + 2)) :
    MeasurableSet (exitSet (β := β) j u S δ) := by
  have hpath := measurable_exitPath (β := β) δ
  have e : exitSet (β := β) j u S δ = ⋃ a : ℕ, {ν | 1 ≤ a ∧ (exitPath δ ν).1.jt a ≤ (S : ℝ≥0∞) ∧
      (exitPath δ ν).1.jv a ∈ escFace j u ∧ ∀ b < a, (exitPath δ ν).1.jv b ∈ escQ j u} := by
    ext ν; simp [exitSet, ExitJ]
  rw [e]
  refine MeasurableSet.iUnion fun a => ?_
  by_cases ha : 1 ≤ a
  · have h1 : MeasurableSet {ν : Measure (CycS ℕ (k + 2) β) |
        (exitPath δ ν).1.jt a ≤ (S : ℝ≥0∞)} :=
      measurableSet_le ((CPath.measurable_jt a).comp hpath) measurable_const
    have h2 : MeasurableSet {ν : Measure (CycS ℕ (k + 2) β) |
        (exitPath δ ν).1.jv a ∈ escFace j u} :=
      (MeasurableSet.of_discrete (s := escFace j u)).preimage ((CPath.measurable_jv a).comp hpath)
    have h3 : MeasurableSet {ν : Measure (CycS ℕ (k + 2) β) |
        ∀ b < a, (exitPath δ ν).1.jv b ∈ escQ j u} := by
      have : {ν : Measure (CycS ℕ (k + 2) β) | ∀ b < a, (exitPath δ ν).1.jv b ∈ escQ j u} =
          ⋂ b ∈ Finset.range a, {ν | (exitPath δ ν).1.jv b ∈ escQ j u} := by
        ext ν; simp
      rw [this]
      exact MeasurableSet.biInter (Finset.range a).countable_toSet fun b _ =>
        (MeasurableSet.of_discrete (s := escQ j u)).preimage ((CPath.measurable_jv b).comp hpath)
    exact (h1.inter (h2.inter h3)).congr (by ext ν; simp [ha])
  · have : {ν : Measure (CycS ℕ (k + 2) β) | 1 ≤ a ∧ (exitPath δ ν).1.jt a ≤ (S : ℝ≥0∞) ∧
        (exitPath δ ν).1.jv a ∈ escFace j u ∧ ∀ b < a, (exitPath δ ν).1.jv b ∈ escQ j u} = ∅ := by
      ext ν; simp [ha]
    rw [this]; exact MeasurableSet.empty

end ElboimSly.Paper.Escape
