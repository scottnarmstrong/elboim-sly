/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Step.ZetaSeq
public import ElboimSly.Paper.Step.StopHit
public import Mathlib

/-!
# Pathwise facts about `ζ_i`, `ζ'_i`

ES22 Lemma 7.1, Step 1.

* `zetaP i ≤ zetaN i ≤...`: the chain `ζ'_0 ≤ ζ_1 < ζ'_1 ≤ ζ_2 < ⋯` (on finiteness);
* a finite `ζ_{i+1}` lies in `U = 𝒯₁ ∩ 𝒯₂`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ElboimSly.SRW
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Step

open ElboimSly.Paper

variable {d : ℕ} {Ω : Type*}

theorem le_stepNextIn (U : Ω → Set ℝ) (R : Ω → WithTop ℝ≥0) (ω : Ω) : R ω ≤ stepNextIn U R ω := by
  unfold stepNextIn
  exact le_iInf₂ fun u hu => hu.2.le

/-- A finite `inf {t > R : t ∈ U}` is attained. -/
theorem stepNextIn_mem {U : Ω → Set ℝ} (hloc : ∀ ω, IsLocIco (U ω)) {R : Ω → WithTop ℝ≥0}
    {ω : Ω} (h : stepNextIn U R ω ≠ ⊤) :
    ((stopReal (stepNextIn U R) ω : ℝ≥0) : ℝ) ∈ U ω := by
  obtain ⟨z, hz⟩ := WithTop.ne_top_iff_exists.1 h
  have hzR : stopReal (stepNextIn U R) ω = z := by unfold stopReal; rw [← hz]; rfl
  rw [hzR]
  have hle : stepNextIn U R ω ≤ (z : WithTop ℝ≥0) := hz ▸ le_rfl
  obtain ⟨u, huU, hRu, huz⟩ := (stepNextIn_le_iff (hloc ω) (R ω) z).1 hle
  rcases eq_or_lt_of_le huz with rfl | hlt
  · exact huU
  exfalso
  have key : ∀ u' : ℝ≥0, (u' : ℝ) ∈ U ω → R ω < u' → z ≤ u' := fun u' hu' hR => by
    have : stepNextIn U R ω ≤ (u' : WithTop ℝ≥0) := iInf₂_le u' ⟨hu', hR⟩
    rw [← hz] at this
    exact WithTop.coe_le_coe.1 this
  rcases hRu.lt_or_eq with hR | hR
  · exact absurd (key u huU hR) (not_le.2 hlt)
  · obtain ⟨ε, hε, hsub⟩ := (hloc ω).exists_Ico u.2 huU
    obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = min ε ((z : ℝ) - u) / 2 := ⟨_, rfl⟩
    have hzu : (u : ℝ) < z := by exact_mod_cast hlt
    have hδ0 : 0 < δ := by rw [hδ]; exact half_pos (lt_min hε (by linarith))
    have hδ1 : δ < ε := by
      have := min_le_left ε ((z : ℝ) - u); rw [hδ]; linarith
    have hδ2 : δ < (z : ℝ) - u := by
      have := min_le_right ε ((z : ℝ) - u); rw [hδ]; linarith
    obtain ⟨u', hu'r⟩ : ∃ u' : ℝ≥0, (u' : ℝ) = u + δ := ⟨(u + δ).toNNReal, Real.coe_toNNReal _ (by linarith [NNReal.coe_nonneg u])⟩
    have h1 : (u' : ℝ) ∈ U ω := hsub ⟨by rw [hu'r]; exact le_add_of_nonneg_right hδ0.le, by rw [hu'r]; exact add_lt_add_right hδ1 _⟩
    have h2 : R ω < u' := by
      rw [hR]
      exact WithTop.coe_lt_coe.2 (by rw [← NNReal.coe_lt_coe, hu'r]; exact lt_add_of_pos_right _ hδ0)
    have := key u' h1 h2
    have h3 : (z : ℝ) ≤ u' := by exact_mod_cast this
    rw [hu'r] at h3
    linarith

section chain

variable {m : MeasurableSpace Ω} {f : Filtration ℝ≥0 m} {β : ℝ} {w₁ w₂ : ℝ≥0 → Ω → Fin d → ℤ}
  {α₁ α₂ : ℝ≥0 → Ω → ℝ≥0}

theorem zetaP_le_zetaN (s₀ : ℝ≥0) (i : ℕ) (ω : Ω) :
    zetaP β w₁ α₁ w₂ α₂ s₀ i ω ≤ zetaN β w₁ α₁ w₂ α₂ s₀ i ω :=
  le_stepNextIn _ _ ω

theorem zetaN_mem (hd : 1 ≤ d) (hβ : 1 < β) (h₁ : ZetaProc f w₁ α₁) (h₂ : ZetaProc f w₂ α₂)
    (s₀ : ℝ≥0) (i : ℕ) {ω : Ω} (h : zetaN β w₁ α₁ w₂ α₂ s₀ i ω ≠ ⊤) :
    ((stopReal (zetaN β w₁ α₁ w₂ α₂ s₀ i) ω : ℝ≥0) : ℝ) ∈ zetaU β w₁ α₁ w₂ α₂ ω :=
  stepNextIn_mem (zetaU_loc hd hβ h₁ h₂) h

theorem stepThitStop_of_ne {β : ℝ} {w : ℝ≥0 → Ω → Fin d → ℤ} {α : ℝ≥0 → Ω → ℝ≥0}
    {R : Ω → WithTop ℝ≥0} {ω : Ω} (h : R ω ≠ ⊤) :
    stepThitStop β w α R ω = stepThit β (stepExt fun s => w s ω)
      (fun r => ((α r.toNNReal ω : ℝ≥0) : ℝ)) (stopReal R ω : ℝ) := by
  unfold stepThitStop; rw [ite_eq_right h]

theorem zetaN_lt_zetaP (hd : 1 ≤ d) (hβ : 1 < β) (h₁ : ZetaProc f w₁ α₁) (h₂ : ZetaProc f w₂ α₂)
    (s₀ : ℝ≥0) (i : ℕ) {ω : Ω} (h : zetaN β w₁ α₁ w₂ α₂ s₀ i ω ≠ ⊤) :
    zetaN β w₁ α₁ w₂ α₂ s₀ i ω < zetaP β w₁ α₁ w₂ α₂ s₀ (i + 1) ω := by
  have hmem := zetaN_mem hd hβ h₁ h₂ s₀ i h
  have g1 := stepThit_gt_of_relaxed (d := d) hd hβ
    (w := stepExt fun s => w₁ s ω) (α := fun r => ((α₁ r.toNNReal ω : ℝ≥0) : ℝ))
    (exists_Ico_const_stepExt (h₁.rc ω)) (NNReal.coe_nonneg (stopReal (zetaN β w₁ α₁ w₂ α₂ s₀ i) ω)) hmem.1.2
  have g2 := stepThit_gt_of_relaxed (d := d) hd hβ
    (w := stepExt fun s => w₂ s ω) (α := fun r => ((α₂ r.toNNReal ω : ℝ≥0) : ℝ))
    (exists_Ico_const_stepExt (h₂.rc ω)) (NNReal.coe_nonneg (stopReal (zetaN β w₁ α₁ w₂ α₂ s₀ i) ω)) hmem.2.2
  rw [ENNReal.ofReal_coe_nnreal] at g1 g2
  have hRz : zetaN β w₁ α₁ w₂ α₂ s₀ i ω =
      ((stopReal (zetaN β w₁ α₁ w₂ α₂ s₀ i) ω : ℝ≥0) : WithTop ℝ≥0) := by
    obtain ⟨y, hy⟩ := WithTop.ne_top_iff_exists.1 h
    unfold stopReal; rw [← hy]; rfl
  show zetaN β w₁ α₁ w₂ α₂ s₀ i ω < min (stepThitStop β w₁ α₁ (zetaN β w₁ α₁ w₂ α₂ s₀ i) ω :
    WithTop ℝ≥0) (stepThitStop β w₂ α₂ (zetaN β w₁ α₁ w₂ α₂ s₀ i) ω : WithTop ℝ≥0)
  rw [stepThitStop_of_ne h, stepThitStop_of_ne h, hRz]
  exact lt_min g1 g2

end chain

end ElboimSly.Paper.Step
