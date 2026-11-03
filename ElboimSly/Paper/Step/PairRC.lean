/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Step.PairMeas
public import ElboimSly.Paper.Step.RegenPath
public import ElboimSly.Paper.Step.StepRegEvents
public import ElboimSly.Paper.Induction.RelaxedMeasRegen2
public import Mathlib

/-!
# Right-local constancy of the pair `(W, α)`

Regenerated cyclic walk; The driven regenerated walk.

The pair `(t ↦ W(t), t ↦ α(t))` of the regenerated walk and its regeneration function is
right-locally constant, both in the environment picture (for a good environment) and for a driven
walk (for a driving path).  This is the regularity needed by `measurableSet_not_winOK`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Step

open ElboimSly ElboimSly.Paper ElboimSly.Cyclic

/-- Right-constancy of a function of a real variable, from plateaus, at points of `ℝ≥0`. -/
theorem eventually_nhdsGE_of_ico {V : Type*} {g : ℝ → V} {s : ℝ≥0} {ε : ℝ} (hε : 0 < ε)
    (h : ∀ s' ∈ Ico (s : ℝ) (s + ε), g s' = g s) :
    ∀ᶠ u : ℝ≥0 in 𝓝[≥] s, g (u : ℝ) = g (s : ℝ) := by
  have h1 : ∀ᶠ u : ℝ≥0 in 𝓝[≥] s, u < s + ε.toNNReal :=
    (show ∀ᶠ u in 𝓝 s, u < s + ε.toNNReal from Iio_mem_nhds (by
      have : (0 : ℝ≥0) < ε.toNNReal := Real.toNNReal_pos.2 hε
      exact lt_add_of_pos_right _ this)).filter_mono nhdsWithin_le_nhds
  filter_upwards [h1, self_mem_nhdsWithin] with u hu hsu
  refine h _ ⟨by exact_mod_cast hsu, ?_⟩
  have : (u : ℝ) < s + ε.toNNReal := by exact_mod_cast hu
  rwa [Real.coe_toNNReal _ hε.le] at this

section Env

variable {d : ℕ} {β : ℝ} [Fact (0 < β)]

/-- The regeneration count is right-locally constant. -/
theorem regenCount_rlc (ν : ℕ → Measure (RingSpace d β)) {s : ℝ} (hs : 0 ≤ s) :
    ∃ ε > 0, ∀ s' ∈ Ico s (s + ε), regenCount ν s' = regenCount ν s := by
  obtain ⟨h1, h2⟩ := regenCount_spec ν hs
  set i := regenCount ν s with hi
  have hε₁ : ∃ ε₁ > 0, ENNReal.ofReal (s + ε₁) ≤ regenSigma ν (i + 1) := by
    by_cases htop : regenSigma ν (i + 1) = ⊤
    · exact ⟨1, one_pos, by simp [htop]⟩
    · refine ⟨(regenSigma ν (i + 1)).toReal - s, ?_, ?_⟩
      · have := ENNReal.toReal_strict_mono htop h2
        rw [ENNReal.toReal_ofReal hs] at this
        linarith
      · rw [add_sub_cancel]; exact (ENNReal.ofReal_toReal htop).le
  obtain ⟨ε₁, hε₁, hle⟩ := hε₁
  refine ⟨ε₁, hε₁, fun s' hs' => ?_⟩
  have hs'0 : 0 ≤ s' := hs.trans hs'.1
  rw [regenCount_eq_iff ν hs'0]
  refine ⟨h1.trans (ENNReal.ofReal_le_ofReal hs'.1), ?_⟩
  exact lt_of_lt_of_le ((ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 (by linarith [hs'.2])) hle

/-- The pair `(regenWalk, regenStart)` is right-locally constant for a good environment. -/
theorem regen_pair_rc {ν : ℕ → Measure (RingSpace d β)} (hg : ∀ k, Good (ν k)) (s : ℝ≥0) :
    (∀ᶠ u : ℝ≥0 in 𝓝[≥] s, regenWalk ν (u : ℝ) = regenWalk ν (s : ℝ)) ∧
      (∀ᶠ u : ℝ≥0 in 𝓝[≥] s, regenStart ν (u : ℝ) = regenStart ν (s : ℝ)) := by
  have hs : (0 : ℝ) ≤ s := s.2
  obtain ⟨ε₁, hε₁, h₁⟩ := regenWalk_rlc hg hs
  obtain ⟨ε₂, hε₂, h₂⟩ := regenCount_rlc ν hs
  refine ⟨eventually_nhdsGE_of_ico hε₁ h₁, eventually_nhdsGE_of_ico hε₂ fun s' hs' => ?_⟩
  simp only [regenStart, h₂ s' hs']

end Env

section Driven

variable {d : ℕ} {β : ℝ} [Fact (0 < β)]

/-- The pair `(stepReg, stepAlpha)` is right-locally constant for a driving path. -/
theorem step_pair_rc {x : ℝ≥0 → Fin d → ℤ} (hx : x ∈ StepPath d) (s : ℝ≥0) :
    (∀ᶠ u : ℝ≥0 in 𝓝[≥] s, stepReg β x u = stepReg β x s) ∧
      (∀ᶠ u : ℝ≥0 in 𝓝[≥] s, (stepAlpha β x u : ℝ) = (stepAlpha β x s : ℝ)) := by
  have hb : 0 < β.toNNReal := toNNReal_pos'
  refine ⟨(isRegPath_stepReg hx.toIsRegPath).rc s, ?_⟩
  obtain ⟨hs1, hs2⟩ := gluedCount_spec' hb x s
  set N := gluedCount (drivenSigma β.toNNReal x) s with hN
  have hev : ∀ᶠ u : ℝ≥0 in 𝓝[≥] s, (u : ℝ≥0∞) < drivenSigma β.toNNReal x (N + 1) :=
    (ENNReal.continuous_coe.continuousAt.eventually (Iio_mem_nhds hs2)).filter_mono
      nhdsWithin_le_nhds
  filter_upwards [hev, self_mem_nhdsWithin] with u hu hsu
  have hcu : gluedCount (drivenSigma β.toNNReal x) u = N :=
    gluedCount_eq (drivenSigma_mono β.toNNReal x) (hs1.trans (by exact_mod_cast hsu)) hu
  have : stepAlpha β x u = stepAlpha β x s := by
    unfold stepAlpha drivenRegenAlpha
    rw [hcu]
  rw [this]

end Driven

end ElboimSly.Paper.Step

end
