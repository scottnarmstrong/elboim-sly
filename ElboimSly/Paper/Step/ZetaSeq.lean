/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Step.RelaxedStoppingApp
public import ElboimSly.Paper.Step.ThitStopping
public import ElboimSly.Paper.Step.WeakThit
public import Mathlib

/-!
# The stopping times `ζ_i`, `ζ'_i` of Lemma 7.1

ES22 Lemma 7.1, Step 1.

For two adapted right-continuous lattice processes `(w₁, α₁)` and `(w₂, α₂)` (the second one is
`W̃^∞`'s second piece, written on the global time axis) put `U = 𝒯₁ ∩ 𝒯₂`, `ζ'_0 = s₀`,
`ζ_{i+1} = inf {t > ζ'_i : t ∈ U}` and `ζ'_{i+1} = thit₁(ζ_{i+1}) ∧ thit₂(ζ_{i+1})`.
All are stopping times (`isStoppingTime_zetaN`, `isStoppingTime_zetaP`).
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Step

open ElboimSly.Paper

variable {d : ℕ} {Ω : Type*} {m : MeasurableSpace Ω}

/-- The hypotheses on one process of the sequence: adapted, right-continuous, with finitely many
events. -/
structure ZetaProc (f : Filtration ℝ≥0 m) (w : ℝ≥0 → Ω → Fin d → ℤ) (α : ℝ≥0 → Ω → ℝ≥0) : Prop where
  adapted : ∀ t, Measurable[f t] (w t)
  alpha : ∀ t, Measurable[f t] (α t)
  rc : ∀ ω t, ∀ᶠ u in 𝓝[≥] t, w u ω = w t ω
  fin : ∀ ω, StepEventsFiniteW (stepExt fun s => w s ω) (fun r => ((α r.toNNReal ω : ℝ≥0) : ℝ))

/-- `U = 𝒯₁ ∩ 𝒯₂`. -/
def zetaU (β : ℝ) (w₁ : ℝ≥0 → Ω → Fin d → ℤ) (α₁ : ℝ≥0 → Ω → ℝ≥0)
    (w₂ : ℝ≥0 → Ω → Fin d → ℤ) (α₂ : ℝ≥0 → Ω → ℝ≥0) (ω : Ω) : Set ℝ :=
  stepRelaxedSetOf β w₁ α₁ ω ∩ stepRelaxedSetOf β w₂ α₂ ω

/-- `thit₁(R) ∧ thit₂(R)`. -/
noncomputable def zetaHit (β : ℝ) (w₁ : ℝ≥0 → Ω → Fin d → ℤ) (α₁ : ℝ≥0 → Ω → ℝ≥0)
    (w₂ : ℝ≥0 → Ω → Fin d → ℤ) (α₂ : ℝ≥0 → Ω → ℝ≥0) (R : Ω → WithTop ℝ≥0) (ω : Ω) :
    WithTop ℝ≥0 :=
  min (stepThitStop β w₁ α₁ R ω : WithTop ℝ≥0) (stepThitStop β w₂ α₂ R ω : WithTop ℝ≥0)

/-- `ζ'_i`. -/
noncomputable def zetaP (β : ℝ) (w₁ : ℝ≥0 → Ω → Fin d → ℤ) (α₁ : ℝ≥0 → Ω → ℝ≥0)
    (w₂ : ℝ≥0 → Ω → Fin d → ℤ) (α₂ : ℝ≥0 → Ω → ℝ≥0) (s₀ : ℝ≥0) : ℕ → Ω → WithTop ℝ≥0
  | 0 => fun _ => (s₀ : WithTop ℝ≥0)
  | i + 1 => zetaHit β w₁ α₁ w₂ α₂
      (stepNextIn (zetaU β w₁ α₁ w₂ α₂) (zetaP β w₁ α₁ w₂ α₂ s₀ i))

/-- `ζ_{i+1}`. -/
noncomputable def zetaN (β : ℝ) (w₁ : ℝ≥0 → Ω → Fin d → ℤ) (α₁ : ℝ≥0 → Ω → ℝ≥0)
    (w₂ : ℝ≥0 → Ω → Fin d → ℤ) (α₂ : ℝ≥0 → Ω → ℝ≥0) (s₀ : ℝ≥0) (i : ℕ) : Ω → WithTop ℝ≥0 :=
  stepNextIn (zetaU β w₁ α₁ w₂ α₂) (zetaP β w₁ α₁ w₂ α₂ s₀ i)

variable {f : Filtration ℝ≥0 m} {β : ℝ} {w₁ w₂ : ℝ≥0 → Ω → Fin d → ℤ} {α₁ α₂ : ℝ≥0 → Ω → ℝ≥0}

theorem zetaU_adapted (_hd : 1 ≤ d) (hβ : 1 < β) (h₁ : ZetaProc f w₁ α₁) (h₂ : ZetaProc f w₂ α₂)
    (t : ℝ≥0) : MeasurableSet[f t] {ω | (t : ℝ) ∈ zetaU β w₁ α₁ w₂ α₂ ω} := by
  have k₁ := measurableSet_stepRelaxed_adapted (by linarith) f w₁ α₁ h₁.adapted h₁.rc h₁.alpha t
  have k₂ := measurableSet_stepRelaxed_adapted (by linarith) f w₂ α₂ h₂.adapted h₂.rc h₂.alpha t
  have e : {ω | (t : ℝ) ∈ zetaU β w₁ α₁ w₂ α₂ ω} =
      {ω | IsRelaxedTimeWrt β (stepExt fun s => w₁ s ω) (α₁ t ω) t} ∩
        {ω | IsRelaxedTimeWrt β (stepExt fun s => w₂ s ω) (α₂ t ω) t} := by
    ext ω
    simp only [zetaU, stepRelaxedSetOf, stepRelaxedSet, Real.toNNReal_coe, mem_inter_iff,
      mem_ofPred_eq]
    simp
  rw [e]
  exact k₁.inter k₂

theorem zetaU_loc (hd : 1 ≤ d) (hβ : 1 < β) (h₁ : ZetaProc f w₁ α₁) (h₂ : ZetaProc f w₂ α₂)
    (ω : Ω) : IsLocIco (zetaU β w₁ α₁ w₂ α₂ ω) :=
  (isLocIco_stepRelaxedSet' hd hβ (h₁.fin ω)).inter (isLocIco_stepRelaxedSet' hd hβ (h₂.fin ω))

theorem isStoppingTime_zetaHit (hβ : 1 < β) (h₁ : ZetaProc f w₁ α₁) (h₂ : ZetaProc f w₂ α₂)
    {R : Ω → WithTop ℝ≥0} (hR : IsStoppingTime f R) :
    IsStoppingTime f (zetaHit β w₁ α₁ w₂ α₂ R) := by
  have a₁ := isStoppingTime_stepThit' hβ f w₁ α₁ h₁.adapted h₁.alpha h₁.fin hR
  have a₂ := isStoppingTime_stepThit' hβ f w₂ α₂ h₂.adapted h₂.alpha h₂.fin hR
  intro t
  have : {ω | zetaHit β w₁ α₁ w₂ α₂ R ω ≤ t} =
      {ω | (stepThitStop β w₁ α₁ R ω : WithTop ℝ≥0) ≤ t} ∪
        {ω | (stepThitStop β w₂ α₂ R ω : WithTop ℝ≥0) ≤ t} := by
    ext ω
    simp only [zetaHit, mem_ofPred_eq, mem_union]
    exact min_le_iff
  rw [this]
  exact (a₁ t).union (a₂ t)

theorem isStoppingTime_zetaP (hd : 1 ≤ d) (hβ : 1 < β) (h₁ : ZetaProc f w₁ α₁)
    (h₂ : ZetaProc f w₂ α₂) (s₀ : ℝ≥0) (i : ℕ) :
    IsStoppingTime f (zetaP β w₁ α₁ w₂ α₂ s₀ i) := by
  induction i with
  | zero =>
    intro t
    show MeasurableSet[f t] {ω | (s₀ : WithTop ℝ≥0) ≤ t}
    by_cases h : (s₀ : WithTop ℝ≥0) ≤ t
    · simp only [h, ofPred_true]; exact @MeasurableSet.univ _ (f t)
    · simp only [h, ofPred_false]; exact @MeasurableSet.empty _ (f t)
  | succ i ih =>
    exact isStoppingTime_zetaHit hβ h₁ h₂ (isStoppingTime_stepNextIn f
      (zetaU_adapted hd hβ h₁ h₂) (zetaU_loc hd hβ h₁ h₂) ih)

theorem isStoppingTime_zetaN (hd : 1 ≤ d) (hβ : 1 < β) (h₁ : ZetaProc f w₁ α₁)
    (h₂ : ZetaProc f w₂ α₂) (s₀ : ℝ≥0) (i : ℕ) :
    IsStoppingTime f (zetaN β w₁ α₁ w₂ α₂ s₀ i) :=
  isStoppingTime_stepNextIn f (zetaU_adapted hd hβ h₁ h₂) (zetaU_loc hd hβ h₁ h₂)
    (isStoppingTime_zetaP hd hβ h₁ h₂ s₀ i)

end ElboimSly.Paper.Step
