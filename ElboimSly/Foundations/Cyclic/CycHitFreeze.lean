/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.PPP.Indep
public import ElboimSly.Foundations.Cyclic.CycMultiDef
public import Mathlib

/-!
# Freezing on a stopping-time event

Independence tools (e) applied under `Q = P(· | T < ∞)` in ES22 Lemma 2.1,
Step 1, and plan-level coupling after a stopping time, proof of (a).

If `E ∈ m` and a random measure `Y` satisfies `P(E ∩ A ∩ {Y ∈ B}) = P(E ∩ A) Π(B)` for all `A ∈ m`,
then `E[1_E G(·, Y)] = E[1_E ∫ G(·, ν) Lw(dν)]` for `m ⊗ 𝔊`-measurable `G ≥ 0`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace ElboimSly.Cyclic

set_option linter.unusedSectionVars false

variable {S : Type*} [MeasurableSpace S] {Ω : Type*} (m : MeasurableSpace Ω)
  [mΩ : MeasurableSpace Ω]

theorem lintegral_freeze_restrict {Pr : Measure Ω} [IsProbabilityMeasure Pr]
    (hm : m ≤ mΩ) {E : Set Ω} (hE : MeasurableSet[m] E)
    {Y : Ω → Measure S} (hY : Measurable Y) (Lw : Measure (Measure S)) [SFinite Lw]
    (hstep : ∀ {A : Set Ω}, MeasurableSet[m] A → ∀ {B : Set (Measure S)}, MeasurableSet B →
      Pr (E ∩ A ∩ Y ⁻¹' B) = Pr (E ∩ A) * Lw B)
    {G : Ω × Measure S → ℝ≥0∞} (hG : Measurable[m.prod inferInstance] G) :
    ∫⁻ ω in E, G (ω, Y ω) ∂Pr = ∫⁻ ω in E, ∫⁻ ν, G (ω, ν) ∂Lw ∂Pr := by
  have hEm : MeasurableSet E := hm _ hE
  by_cases h0 : Pr E = 0
  · rw [Measure.restrict_eq_zero.2 h0]; simp
  have hQ : IsProbabilityMeasure (cond Pr E) := cond_isProbabilityMeasure h0
  have hQapp : ∀ s : Set Ω, cond Pr E s = (Pr E)⁻¹ * Pr (E ∩ s) := fun s => cond_apply hEm Pr s
  have hPrE : Pr E ≠ ⊤ := measure_ne_top Pr E
  have hQ1 : ∀ B : Set (Measure S), MeasurableSet B → cond Pr E (Y ⁻¹' B) = Lw B := by
    intro B hB
    have := hstep MeasurableSet.univ hB
    rw [inter_univ] at this
    rw [hQapp, this, ← mul_assoc, ENNReal.inv_mul_cancel h0 hPrE, one_mul]
  have hX : Measurable (GSpace.mk m) := fun _ hs => hm _ hs
  have hind : IndepFun (GSpace.mk m) Y (cond Pr E) := by
    rw [indepFun_iff_measure_inter_preimage_eq_mul]
    intro A B hA hB
    have hA' : MeasurableSet[m] (GSpace.mk m ⁻¹' A) := hA
    rw [hQapp, ← inter_assoc, hstep hA' hB, hQapp, hQ1 B hB, mul_assoc]
  have hmapY : (cond Pr E).map Y = Lw := by
    ext B hB
    rw [Measure.map_apply hY hB, hQ1 B hB]
  have : IsProbabilityMeasure ((cond Pr E).map Y) :=
    ⟨by
      rw [hmapY]
      have := hQ1 univ MeasurableSet.univ
      rw [preimage_univ, measure_univ] at this
      exact this.symm⟩
  have hGm : Measurable (fun p : GSpace m × Measure S => G (p.1, p.2)) := hG
  have hfr := ElboimSly.lintegral_freeze (P := cond Pr E) hX hY hind hGm
  rw [hmapY] at hfr
  have hmeas_outer : Measurable fun x : GSpace m => ∫⁻ y, G (x, y) ∂Lw := by
    have : SFinite Lw := inferInstance
    exact measurable_lintegral_freeze Lw hGm
  rw [lintegral_map hmeas_outer hX] at hfr
  have hQint : ∀ g : Ω → ℝ≥0∞, ∫⁻ ω, g ω ∂(cond Pr E) = (Pr E)⁻¹ * ∫⁻ ω in E, g ω ∂Pr := by
    intro g
    show ∫⁻ ω, g ω ∂((Pr E)⁻¹ • Pr.restrict E) = _
    rw [lintegral_smul_measure]
    rfl
  have hLq : ∫⁻ ω, G (ω, Y ω) ∂(cond Pr E) = ∫⁻ ω, ∫⁻ y, G (ω, y) ∂Lw ∂(cond Pr E) := hfr
  rw [hQint, hQint] at hLq
  have hc0 : (Pr E)⁻¹ ≠ 0 := ENNReal.inv_ne_zero.2 hPrE
  have hct : (Pr E)⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.2 h0
  exact (ENNReal.mul_right_inj hc0 hct).1 hLq

end ElboimSly.Cyclic

end
