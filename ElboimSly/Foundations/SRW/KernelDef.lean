/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.SRW.ParamSets
public import ElboimSly.Foundations.SRW.AdmissibleSRW
public import ElboimSly.Foundations.SRW.Iid
public import ElboimSly.Foundations.PPP.ExistenceExamples
public import Mathlib

/-!
# Confined kernels: definition

Confined kernels.

We fix a model SRW (`srwModel`), whose existence comes from the existence of the Poisson point
process, and define the confined kernel through it.  `IsSRW.prob_kernelSet` shows that every SRW
gives the same probability to the kernel event (a regular event depends only on the law).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal

namespace ElboimSly
namespace SRW

variable {d : ℕ}

theorem exists_srw (d : ℕ) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (Z : Ω → PathSpace d), IsSRW P Z := by
  obtain ⟨Ω, mΩ, P, N, _, hN, _⟩ := exists_isPoissonPointProcess_clockIntensity (Dir d)
  exact ⟨Ω, mΩ, P, canonical d N, canonical_isSRW hN⟩

/-- The model probability space of the SRW used to define kernels. -/
noncomputable def srwΩ (d : ℕ) : Type := (exists_srw d).choose

noncomputable instance srwΩ.instMeasurableSpace (d : ℕ) : MeasurableSpace (srwΩ d) :=
  (exists_srw d).choose_spec.choose

/-- The model probability measure. -/
noncomputable def srwP (d : ℕ) : Measure (srwΩ d) := (exists_srw d).choose_spec.choose_spec.choose

/-- The model SRW. -/
noncomputable def srwZ (d : ℕ) : srwΩ d → PathSpace d :=
  (exists_srw d).choose_spec.choose_spec.choose_spec.choose

theorem srwZ_isSRW (d : ℕ) : IsSRW (srwP d) (srwZ d) :=
  (exists_srw d).choose_spec.choose_spec.choose_spec.choose_spec

/-- The canonical map from point configurations to paths. -/
noncomputable def canonMap (d : ℕ) (ν : Measure (Dir d × ℝ)) : PathSpace d :=
  fun s => walk d ν (s : ℝ)

theorem measurable_canonMap (d : ℕ) : Measurable (canonMap d) :=
  measurable_pi_iff.2 fun s => measurable_walk d s

/-- Every SRW has the law of the model SRW. -/
theorem IsSRW.map_eq_model {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {Z : Ω → PathSpace d}
    (hZ : IsSRW P Z) : P.map Z = (srwP d).map (srwZ d) := by
  obtain ⟨_, _, Ω', _, P', N', hN', hlaw⟩ := hZ
  obtain ⟨_, _, Ω'', _, P'', N'', hN'', hlaw'⟩ := srwZ_isSRW d
  rw [hlaw, hlaw']
  have e1 : canonical d N' = fun ω => canonMap d (N' ω) := rfl
  have e2 : canonical d N'' = fun ω => canonMap d (N'' ω) := rfl
  rw [e1, e2, IsPoissonPointProcess.map_comp hN'.measurable (measurable_canonMap d),
    IsPoissonPointProcess.map_comp hN''.measurable (measurable_canonMap d),
    hN'.map_eq_map hN'']

/-- A set of paths with a measurable version (agreeing with it on regular paths). -/
def IsRegSet (Γ : Set (PathSpace d)) : Prop :=
  ∃ Γ' : Set (PathSpace d), MeasurableSet Γ' ∧ ∀ γ, IsRegularPath γ → (γ ∈ Γ ↔ γ ∈ Γ')

/-- A regular event has the same probability for every SRW. -/
theorem IsSRW.prob_regSet {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {Z : Ω → PathSpace d}
    (hZ : IsSRW P Z) {Γ Γ' : Set (PathSpace d)} (hΓ' : MeasurableSet Γ')
    (h : ∀ γ, IsRegularPath γ → (γ ∈ Γ ↔ γ ∈ Γ')) :
    P {ω | Z ω ∈ Γ} = (srwP d).map (srwZ d) Γ' := by
  rw [← hZ.map_eq_model, Measure.map_apply hZ.1 hΓ']
  congr 1
  ext ω
  exact h _ (hZ.2.1 ω)

theorem IsSRW.prob_regSet_eq {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {Z : Ω → PathSpace d} {P' : Measure Ω'} {Z' : Ω' → PathSpace d}
    (hZ : IsSRW P Z) (hZ' : IsSRW P' Z') {Γ : Set (PathSpace d)} (hΓ : IsRegSet Γ) :
    P {ω | Z ω ∈ Γ} = P' {ω | Z' ω ∈ Γ} := by
  obtain ⟨Γ', h1, h2⟩ := hΓ
  rw [hZ.prob_regSet h1 h2, hZ'.prob_regSet h1 h2]

/-- The kernel event: from `x`, be at `z` at time `r`, staying in `Q` on `[0, r]`. -/
def kerSet (Q : Set (Fin d → ℤ)) (r : ℝ≥0) (x z : Fin d → ℤ) : Set (PathSpace d) :=
  {γ | x + γ r = z ∧ ∀ s : ℝ≥0, s ≤ r → x + γ s ∈ Q}

theorem isRegSet_kerSet (Q : Set (Fin d → ℤ)) (r : ℝ≥0) (x z : Fin d → ℤ) :
    IsRegSet (kerSet Q r x z) := by
  have h1 := isVersion_eval (E := Unit) (d := d) (α := fun _ => r)
    (K := {p : Unit × (Fin d → ℤ) | x + p.2 = z}) measurable_const
    (MeasurableSet.of_discrete)
  have h2 := isVersion_forall_Icc (E := Unit) (d := d) (α := fun _ => 0) (β := fun _ => r)
    (K := {p : Unit × (Fin d → ℤ) | x + p.2 ∈ Q}) measurable_const measurable_const
    (MeasurableSet.of_discrete)
  generalize {p : Unit × PathSpace d | (p.1, ev r p.2) ∈ {p : Unit × (Fin d → ℤ) | x + p.2 = z}} = A1
    at h1
  generalize ({p : Unit × PathSpace d | r < 0} ∪
      ({p | (p.1, ev r p.2) ∈ {p : Unit × (Fin d → ℤ) | x + p.2 ∈ Q}} ∩
        ⋂ r' : ℚ, ({p | ¬ (0 ≤ ratNN r' ∧ ratNN r' < r)} ∪
          {p | (p.1, p.2 (ratNN r')) ∈ {p : Unit × (Fin d → ℤ) | x + p.2 ∈ Q}}))) = A2 at h2
  refine ⟨(Prod.mk () ⁻¹' A1) ∩ (Prod.mk () ⁻¹' A2), ?_, fun γ hγ => ?_⟩
  · exact ((measurable_prodMk_left) h1.1).inter ((measurable_prodMk_left) h2.1)
  · have a := h1.2 () γ hγ
    have b := h2.2 () γ hγ
    have c : (∀ s : ℝ≥0, s ≤ r → x + γ s ∈ Q) ↔ ∀ s : ℝ≥0, 0 ≤ s → s ≤ r → x + γ s ∈ Q :=
      ⟨fun h s _ hs => h s hs, fun h s hs => h s (by positivity) hs⟩
    exact (and_congr Iff.rfl c).trans (and_congr a b)

/-- The confined kernel `q^Q_r(x, z)` (Confined kernels): the probability that
`x + X(r) = z` and `x + X(s) ∈ Q` for all `s ∈ [0, r]`, for the model SRW `X`. -/
noncomputable def kernel (Q : Set (Fin d → ℤ)) (r : ℝ≥0) (x z : Fin d → ℤ) : ℝ :=
  ((srwP d) {ω | srwZ d ω ∈ kerSet Q r x z}).toReal

/-- The kernel is the probability of its event for every SRW. -/
theorem IsSRW.prob_kerSet {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {Z : Ω → PathSpace d}
    (hZ : IsSRW P Z) (Q : Set (Fin d → ℤ)) (r : ℝ≥0) (x z : Fin d → ℤ) :
    P {ω | Z ω ∈ kerSet Q r x z} = ENNReal.ofReal (kernel Q r x z) := by
  have := (srwZ_isSRW d).isProbabilityMeasure
  rw [kernel, ENNReal.ofReal_toReal (measure_ne_top _ _)]
  exact hZ.prob_regSet_eq (srwZ_isSRW d) (isRegSet_kerSet Q r x z)

end SRW
end ElboimSly
