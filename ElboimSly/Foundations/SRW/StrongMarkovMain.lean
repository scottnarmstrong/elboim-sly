/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.SRW.StrongMarkovCyl
public import Mathlib

/-!
# The strong Markov property

Strong Markov property.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

namespace ElboimSly
namespace SRW

variable {d : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {Z : Ω → PathSpace d}
  {F : ℝ≥0 → MeasurableSpace Ω} {T : Ω → WithTop ℝ≥0}

/-- Strong Markov property: for an SRW `Z`, an admissible filtration, a stopping time
`T`, `A ∈ ℱ_T` and measurable `Γ`,
`P(A ∩ {T < ∞} ∩ {θ_T Z ∈ Γ}) = P(A ∩ {T < ∞}) · P(Z ∈ Γ)`. -/
theorem IsSRW.strong_markov (hZ : IsSRW P Z) (hF : IsAdmissible P Z F)
    (hT : IsStoppingTime hF.filtration T) {A : Set Ω} (hA : MeasurableSet[hT.measurableSpace] A)
    {Γ : Set (PathSpace d)} (hΓ : MeasurableSet Γ) :
    P (A ∩ {ω | T ω < ⊤} ∩ {ω | thetaAt T Z ω ∈ Γ}) =
      P (A ∩ {ω | T ω < ⊤}) * P.map Z Γ := by
  have := hZ.isProbabilityMeasure
  set B : Set Ω := A ∩ {ω | T ω < ⊤} with hBdef
  have hth : Measurable (thetaAt T Z) :=
    measurable_thetaAt hT (fun s => (measurable_pi_apply s).comp hZ.1) hZ.2.1
  have hAm : MeasurableSet A := hT.measurableSpace_le A hA
  have hTtop : MeasurableSet {ω | T ω < ⊤} := by
    have : {ω | T ω < ⊤} = {ω | T ω = ⊤}ᶜ := by
      ext ω; simp [lt_top_iff_ne_top]
    rw [this]; exact hT.measurableSet_top.compl
  have hBm : MeasurableSet B := hAm.inter hTtop
  have : IsFiniteMeasure (P.restrict B) := inferInstance
  have key : (P.restrict B).map (thetaAt T Z) = P B • P.map Z := by
    refine ext_of_generate_finite (measurableCylinders fun _ : ℝ≥0 => Fin d → ℤ)
      generateFrom_measurableCylinders.symm isPiSystem_measurableCylinders ?_ ?_
    · intro s hs
      obtain ⟨I, S, hS, rfl⟩ := (mem_measurableCylinders _).1 hs
      have hc : MeasurableSet (cylinder I S) :=
        MeasurableSet.cylinder (α := fun _ : ℝ≥0 => Fin d → ℤ) I hS
      rw [Measure.map_apply hth hc, Measure.restrict_apply (hth hc), Measure.smul_apply,
        smul_eq_mul, inter_comm]
      exact hZ.strong_markov_cylinder hF hT hA I hS
    · rw [Measure.map_apply hth MeasurableSet.univ, Measure.smul_apply]
      simp
  have := congrArg (fun μ => μ Γ) key
  simp only [Measure.map_apply hth hΓ, Measure.restrict_apply (hth hΓ), Measure.smul_apply,
    smul_eq_mul] at this
  rw [inter_comm]; exact this

end SRW
end ElboimSly
