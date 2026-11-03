/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Step.StopMarkov
public import Mathlib

/-!
# The strong Markov law of the driven walk, for an arbitrary SRW

ES22 Lemma 4.1 (independence), ES22 Lemma 2.1 (e) for a
general SRW with driving paths.
-/

@[expose] public section

open MeasureTheory Set ElboimSly.Cyclic ElboimSly.SRW
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Step

open ElboimSly.Paper

variable {d : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {Y : Ω → PathSpace d}
  {F : ℝ≥0 → MeasurableSpace Ω}

omit mΩ in
theorem isRegPath_thetaAt' (hYp : ∀ ω, Y ω ∈ StepPath d) {T : Ω → WithTop ℝ≥0} {ω : Ω}
    (hω : T ω < ⊤) : IsRegPath (thetaAt T Y ω) := by
  have hne : T ω ≠ ⊤ := ne_of_lt hω
  unfold thetaAt
  rw [ite_eq_right hne]
  exact isRegPath_shiftPath (hYp ω).toIsRegPath _

/-- The strong Markov law of the driven walk at a stopping time. -/
theorem stepReg_strong_markov {β : ℝ} [Fact (0 < β)] (hY : IsSRW P Y)
    (hYp : ∀ ω, Y ω ∈ StepPath d) (hF : IsAdmissible P Y F) {T : Ω → WithTop ℝ≥0}
    (hT : IsStoppingTime hF.filtration T) {A : Set Ω}
    (hA : MeasurableSet[hT.measurableSpace] A) {Γ : Set (PathSpace d)} (hΓ : MeasurableSet Γ) :
    P (A ∩ {ω | T ω < ⊤} ∩ {ω | stepReg β (thetaAt T Y ω) ∈ Γ}) =
      P (A ∩ {ω | T ω < ⊤}) * P {ω | stepReg β (Y ω) ∈ Γ} := by
  have hb : 0 < β.toNNReal := toNNReal_pos'
  have hΦ : Measurable fun x : {x : ℝ≥0 → Fin d → ℤ // IsRegPath x} =>
      drivenRegenFrom β.toNNReal x.1 :=
    measurable_pi_iff.2 (measurable_drivenRegenFrom_subtype hb)
  obtain ⟨Γ'', hΓ'', hEq⟩ := (MeasurableSpace.measurableSet_comap).1 (hΦ hΓ)
  have key : ∀ y, IsRegPath y → (y ∈ Γ'' ↔ drivenRegenFrom β.toNNReal y ∈ Γ) := fun y hy => by
    have := Set.ext_iff.1 hEq ⟨y, hy⟩
    simpa using this
  have sm := hY.strong_markov hF hT hA hΓ''
  rw [Measure.map_apply hY.1 hΓ''] at sm
  have e1 : A ∩ {ω | T ω < ⊤} ∩ {ω | stepReg β (thetaAt T Y ω) ∈ Γ} =
      A ∩ {ω | T ω < ⊤} ∩ {ω | thetaAt T Y ω ∈ Γ''} := by
    ext ω
    simp only [mem_inter_iff, mem_ofPred_eq]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨⟨h1, h2⟩, (key _ (isRegPath_thetaAt' hYp h2)).2 h3⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨⟨h1, h2⟩, (key _ (isRegPath_thetaAt' hYp h2)).1 h3⟩
  have e2 : Y ⁻¹' Γ'' = {ω | stepReg β (Y ω) ∈ Γ} := by
    ext ω
    exact key _ (hYp ω).toIsRegPath
  rw [e1, sm, e2]

end ElboimSly.Paper.Step
