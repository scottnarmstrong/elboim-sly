/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycSchemeEnvAe
public import ElboimSly.Foundations.Cyclic.CycSchemeMeas3
public import Mathlib

/-!
# The environment scheme (c): the ending index is a stopping index

The environment scheme (c), first sentence. `kappa run ω = inf {j : ε_j(H_j) = 1}` is a
`𝒢`-stopping index (`isStopping_kappa`): `{κ = j} = {ε_j(H_j) = 1, ε_{j-1}(H_{j-1}) = 0} ∈ 𝒢_j`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic
namespace CycSchemeEnv
variable {I : Type*} [MeasurableSpace I] [Countable I] [MeasurableSingletonClass I] {d : ℕ} {β : ℝ}
  [Fact (0 < β)] {P : CycPlan I d β} {sc : ℝ≥0∞}
variable {U : Type*} [MeasurableSpace U] {Ω : Type*} [MeasurableSpace Ω] {Pr : Measure Ω}

open scoped Classical in
/-- `κ = inf {j : ε_j(H_j) = 1}` (The environment scheme (c)). -/
noncomputable def kappa (run : ExplRun (cycScheme P sc U) Pr) (ω : Ω) : ℕ∞ :=
  if h : ∃ j : ℕ, (CycScheme.stateAt P sc j (run.H j ω)).2 = true then (Nat.find h : ℕ∞) else ⊤

theorem ended_mono (run : ExplRun (cycScheme P sc U) Pr) (ω : Ω) {i j : ℕ} (hij : i ≤ j)
    (h : (CycScheme.stateAt P sc i (run.H i ω)).2 = true) :
    (CycScheme.stateAt P sc j (run.H j ω)).2 = true := by
  induction hij with
  | refl => exact h
  | step _ ih =>
    rw [stateAt_H_succ]
    unfold CycScheme.upd
    rw [ite_eq_left ih]
    exact ih

theorem kappa_eq_iff (run : ExplRun (cycScheme P sc U) Pr) (ω : Ω) (k : ℕ) :
    kappa run ω = k ↔ (CycScheme.stateAt P sc k (run.H k ω)).2 = true ∧
      ∀ i < k, (CycScheme.stateAt P sc i (run.H i ω)).2 = false := by
  classical
  unfold kappa
  by_cases h : ∃ j : ℕ, (CycScheme.stateAt P sc j (run.H j ω)).2 = true
  · rw [dite_eq_left h]
    rw [Nat.cast_inj]
    constructor
    · rintro rfl
      refine ⟨Nat.find_spec h, fun i hi => ?_⟩
      have := Nat.find_min h hi
      simpa using this
    · rintro ⟨h1, h2⟩
      refine le_antisymm (Nat.find_min' h h1) ?_
      by_contra hlt
      push Not at hlt
      have := h2 _ hlt
      rw [Nat.find_spec h] at this
      exact absurd this (by simp)
  · rw [dite_eq_right h]
    constructor
    · intro hk; exact absurd hk (by simp)
    · rintro ⟨h1, -⟩; exact absurd ⟨k, h1⟩ h

/-- The environment scheme (c): `κ` is a `𝒢`-stopping index. -/
theorem isStopping_kappa (run : ExplRun (cycScheme P sc U) Pr) : run.IsStopping (kappa run) := by
  intro k
  cases k with
  | zero =>
    refine ⟨{η | (CycScheme.stateAt P sc 0 η).2 = true}, ?_, ?_⟩
    · exact (measurableSet_eq_fun ((CycScheme.measurable_stateAt P sc 0).snd) measurable_const)
    · ext ω
      simp only [mem_ofPred_eq, mem_preimage]
      rw [show ((0 : ℕ) : ℕ∞) = ((0 : ℕ) : ℕ∞) from rfl, kappa_eq_iff]
      simp
  | succ m =>
    refine ⟨{η | (CycScheme.stateAt P sc (m + 1) η).2 = true ∧
        (CycScheme.stateAt P sc m η.init).2 = false}, ?_, ?_⟩
    · exact (measurableSet_eq_fun ((CycScheme.measurable_stateAt P sc (m + 1)).snd) measurable_const).inter
        (measurableSet_eq_fun (((CycScheme.measurable_stateAt P sc m).comp
          (Hist.measurable_init m)).snd) measurable_const)
    · ext ω
      simp only [mem_ofPred_eq, mem_preimage]
      rw [kappa_eq_iff]
      have hinit : (run.H (m + 1) ω).init = run.H m ω := (cycScheme P sc U).Hfun_init m _
      rw [hinit]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨h1, h2 m (Nat.lt_succ_self m)⟩
      · rintro ⟨h1, h2⟩
        refine ⟨h1, fun i hi => ?_⟩
        by_contra hne
        have hT : (CycScheme.stateAt P sc i (run.H i ω)).2 = true := by simpa using hne
        have := ended_mono run ω (Nat.le_of_lt_succ hi) hT
        rw [h2] at this
        exact absurd this (by simp)

end CycSchemeEnv
end ElboimSly.Cyclic

end
