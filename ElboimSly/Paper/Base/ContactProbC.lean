/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Base.ContactProbB
public import Mathlib

/-!
# The probability of the escape scenario (continued)

Contacts are few (ii).

* `prob_escB`: `P(θ₁ X̄ ∈ B) ≥ c_esc(d)`, by transience: escape from the unit box for the difference of the independent
  walks `θ₁X₂`, `θ₁X₁`.
* `prob_contactGamma`: `P(X̄ ∈ Γ_{y₀}) ≥ c₁(d)`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Paper

open ElboimSly.Cyclic ElboimSly.Paper.Base ElboimSly.SRW

variable {d : ℕ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {Ñ : Ω → Measure ((Dir d × Fin 2) × ℝ)}

section

variable [NeZero d] (h : IsPoissonPointProcess Ñ (clockIntensity (Dir d × Fin 2)) P)
include h

theorem prob_escB (hd : 3 ≤ d) {y₀ : Fin d → ℤ} (h0 : y₀ ≠ 0) (h1 : ‖y₀‖ ≤ 1) :
    ENNReal.ofReal (es8CEsc d) ≤ P {ω | theta 1 (drvPair Ñ ω) ∈ escB y₀} := by
  have := (drivers_isSRW h 0).isProbabilityMeasure
  have hX1 := (drivers_isSRW h 1).theta 1
  have hX0 := (drivers_isSRW h 0).theta 1
  have hind : IndepFun (fun ω => theta 1 (drvX Ñ 1 ω)) (fun ω => theta 1 (drvX Ñ 0 ω)) P :=
    ((drivers_indep h).indepFun (by decide : (1 : Fin 2) ≠ 0)).comp (measurable_theta 1)
      (measurable_theta 1)
  have hx := two_le_norm_add_escDir h0 h1
  have hesc := escape_diff hX1 hX0 hind hd hx
  have hsub : {ω | ∀ s : ℝ≥0, 2 ≤ ‖fun i => (((y₀ + (escDir y₀).vec) i +
      (theta 1 (drvX Ñ 1 ω) s i - theta 1 (drvX Ñ 0 ω) s i) : ℤ) : ℝ)‖} ⊆
      {ω | theta 1 (drvPair Ñ ω) ∈ escB y₀} := by
    intro ω hω q hq
    have := hω (ratNN q)
    rw [norm_cast_vec] at this
    have e : sndP (theta 1 (drvPair Ñ ω)) (ratNN q) - fstP (theta 1 (drvPair Ñ ω)) (ratNN q) =
        theta 1 (drvX Ñ 1 ω) (ratNN q) - theta 1 (drvX Ñ 0 ω) (ratNN q) := by
      rw [sndP_theta_drvPair, fstP_theta_drvPair]; rfl
    rw [e]; exact this
  calc ENNReal.ofReal (es8CEsc d) ≤ ENNReal.ofReal (P.real _) := ENNReal.ofReal_le_ofReal hesc
    _ = P _ := ofReal_measureReal (measure_ne_top P _)
    _ ≤ _ := measure_mono hsub

theorem prob_contactGamma (hd : 3 ≤ d) {y₀ : Fin d → ℤ} (h0 : y₀ ≠ 0) (h1 : ‖y₀‖ ≤ 1) :
    ENNReal.ofReal (es8C1 d) ≤ P {ω | drvPair Ñ ω ∈ contactGamma y₀} := by
  have := (drivers_isSRW h 0).isProbabilityMeasure
  have hind := (drivers_pair_admissible h).indep 1
  rw [Indep_iff] at hind
  have hB : MeasurableSet[MeasurableSpace.comap (fun ω => theta 1 (drvPair Ñ ω)) inferInstance]
      {ω | theta 1 (drvPair Ñ ω) ∈ escB y₀} :=
    MeasurableSpace.measurableSet_comap.2 ⟨escB y₀, measurableSet_escB y₀, rfl⟩
  have hmul := hind _ _ hB (measurableSet_pair_escA y₀)
  have e : {ω | drvPair Ñ ω ∈ contactGamma y₀} =
      {ω | theta 1 (drvPair Ñ ω) ∈ escB y₀} ∩ {ω | drvPair Ñ ω ∈ escA y₀} := by
    ext ω; simp only [mem_ofPred_eq, mem_inter_iff, mem_escGamma_iff]; tauto
  rw [e, hmul]
  have hF := measure_mono_ae (ae_single_point_subset h y₀)
  rw [prob_single_point (drvPoint_ppp h)] at hF
  have hB' := prob_escB h hd h0 h1
  have e2 : (2 * (d + d) : ℕ) = 4 * d := by ring
  rw [e2] at hF
  calc ENNReal.ofReal (es8C1 d) = ENNReal.ofReal (Real.exp (-(4 * d : ℕ))) *
        ENNReal.ofReal (es8CEsc d) := by
        unfold es8C1
        rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
        congr 2
        push_cast; ring_nf
    _ ≤ _ := by
        rw [mul_comm]
        exact mul_le_mul' hB' hF

end

end ElboimSly.Paper
