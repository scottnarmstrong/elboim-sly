/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Step.StopMarkov
public import Mathlib

/-!
# Subtracting the offset `s₀` from a stopping time

ES22 Lemma 7.1, Step 4: for a `𝒢`-stopping time `S ≥ s₀` (with `𝒢_t = F_{a+t}`), `S - s₀` is a
stopping time of `𝒢^{(2)}_u = F_{a+s₀+u}` and `𝒢_S ⊆ 𝒢^{(2)}_{S - s₀}`.
-/

@[expose] public section

open MeasureTheory Set ElboimSly.SRW
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Step

open ElboimSly.Paper

variable {d : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {Y : Ω → PathSpace d}
  {F : ℝ≥0 → MeasurableSpace Ω}

/-- `S - s₀` (`⊤` stays `⊤`). -/
def stepSubShift (s₀ : ℝ≥0) (S : Ω → WithTop ℝ≥0) : Ω → WithTop ℝ≥0 :=
  fun ω => WithTop.map (fun z => z - s₀) (S ω)

omit mΩ in
theorem stepSubShift_le_iff (s₀ : ℝ≥0) (S : Ω → WithTop ℝ≥0) (u : ℝ≥0) :
    {ω | stepSubShift s₀ S ω ≤ WithTop.some u} = {ω | S ω ≤ WithTop.some (s₀ + u)} := by
  ext ω
  simp only [mem_ofPred_eq, stepSubShift]
  cases S ω using WithTop.recTopCoe with
  | top =>
    have h : ∀ x : ℝ≥0, ¬ (⊤ : WithTop ℝ≥0) ≤ WithTop.some x := fun x h =>
      WithTop.coe_ne_top (top_le_iff.1 h)
    rw [WithTop.map_top]
    exact ⟨fun hh => absurd hh (h u), fun hh => absurd hh (h _)⟩
  | coe z =>
    change WithTop.some (z - s₀) ≤ WithTop.some u ↔ WithTop.some z ≤ WithTop.some (s₀ + u)
    rw [WithTop.coe_le_coe, WithTop.coe_le_coe, tsub_le_iff_left]

theorem isStoppingTime_stepSubShift (hF : IsAdmissible P Y F) (a s₀ : ℝ≥0)
    {S : Ω → WithTop ℝ≥0} (hS : IsStoppingTime (stepShiftFilt hF a) S) :
    IsStoppingTime (stepShiftFilt hF (a + s₀)) (stepSubShift s₀ S) := by
  intro u
  show MeasurableSet[F (a + s₀ + u)] {ω | stepSubShift s₀ S ω ≤ WithTop.some u}
  rw [stepSubShift_le_iff, add_assoc]
  exact hS (s₀ + u)

theorem measurableSet_stepSubShift (hF : IsAdmissible P Y F) (a s₀ : ℝ≥0)
    {S : Ω → WithTop ℝ≥0} (hS : IsStoppingTime (stepShiftFilt hF a) S) {A : Set Ω}
    (hA : MeasurableSet[hS.measurableSpace] A) :
    MeasurableSet[(isStoppingTime_stepSubShift hF a s₀ hS).measurableSpace] A := by
  refine ⟨?_, fun u => ?_⟩
  · have hle : (⨆ t, (stepShiftFilt hF a) t) ≤ ⨆ u, (stepShiftFilt hF (a + s₀)) u := by
      refine iSup_le fun t => ?_
      refine le_trans ?_ (le_iSup (fun u => (stepShiftFilt hF (a + s₀)) u) (t - s₀))
      show F (a + t) ≤ F (a + s₀ + (t - s₀))
      refine hF.mono ?_
      rw [add_assoc]
      exact add_le_add le_rfl le_add_tsub
    exact hle A hA.1
  · have h1 := hA.2 (s₀ + u)
    show MeasurableSet[F (a + s₀ + u)] (A ∩ {ω | stepSubShift s₀ S ω ≤ WithTop.some u})
    rw [stepSubShift_le_iff, add_assoc]
    exact h1

end ElboimSly.Paper.Step
