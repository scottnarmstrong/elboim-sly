/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.StrongApprox.StrongMarkovKey
public import Mathlib

/-!
# Strong Markov property for real Brownian motion

Strong Markov property at stopping times of the natural filtration (Part II).

If `β` is a standard real Brownian motion and `τ` a stopping time of its natural filtration with
`τ < ∞` a.s., then `β' = procShift τ β` is a standard real Brownian motion, and its path is
independent of the stopped `σ`-algebra `stoppedSigma`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace ElboimSly.StrongApprox

open ElboimSly.Brownian

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {β : ℝ≥0 → Ω → ℝ}

/-- Strong Markov property at stopping times of the natural filtration, cylinder events. -/
theorem measure_inter_cylinder_shift [IsProbabilityMeasure P] (hβ : IsStandardRealBM β P)
    {τ : Ω → ℝ≥0∞} (hτ : ∀ t : ℝ≥0, MeasurableSet[realFiltration β t] {ω | τ ω ≤ t})
    (hfin : ∀ᵐ ω ∂P, τ ω < ⊤) {A : Set Ω} (hAm : MeasurableSet A)
    (hA : ∀ t : ℝ≥0, MeasurableSet[realFiltration β t] (A ∩ {ω | τ ω ≤ t}))
    (I : Finset ℝ≥0) {S : Set (I → ℝ)} (hS : MeasurableSet S) :
    P (A ∩ {ω | (fun i : I => procShift τ β i ω) ∈ S}) =
      P A * P {ω | (fun i : I => β i ω) ∈ S} := by
  have hproc : IsProcess β := isProcess_of_realBM hβ
  have hτm : Measurable τ := measurable_of_stopping hproc.2 hτ
  have hsh : IsProcess (procShift τ β) := hproc.shift hτm
  have hg' : Measurable fun ω => (fun i : I => procShift τ β i ω) :=
    measurable_pi_iff.2 fun i => hsh.2 i
  have hg : Measurable fun ω => (fun i : I => β i ω) :=
    measurable_pi_iff.2 fun i => hproc.2 i
  have e : (P.restrict A).map (fun ω => (fun i : I => procShift τ β i ω)) =
      (P A) • P.map (fun ω => (fun i : I => β i ω)) := by
    have : IsFiniteMeasure ((P.restrict A).map fun ω => (fun i : I => procShift τ β i ω)) :=
      Measure.isFiniteMeasure_map _ _
    refine ext_of_forall_lintegral_eq_of_IsFiniteMeasure fun f => ?_
    have hfm : Measurable fun x => (f x : ℝ≥0∞) :=
      measurable_coe_nnreal_ennreal.comp f.continuous.measurable
    rw [lintegral_map hfm hg', lintegral_smul_measure,
      lintegral_map hfm hg, ← lintegral_indicator hAm]
    have := lintegral_stopped_shift hβ hτ hfin hAm hA I f
    simpa [smul_eq_mul] using this
  have := congrArg (fun m => m S) e
  simp only [Measure.map_apply hg' hS, Measure.restrict_apply (hg' hS), Measure.smul_apply,
    Measure.map_apply hg hS, smul_eq_mul] at this
  rw [Set.inter_comm]
  exact this

omit mΩ in
lemma univ_mem_stoppedSigma {β : ℝ≥0 → Ω → ℝ} {τ : Ω → ℝ≥0∞}
    (hτ : ∀ t : ℝ≥0, MeasurableSet[realFiltration β t] {ω | τ ω ≤ t}) :
    ∀ t : ℝ≥0, MeasurableSet[realFiltration β t] (Set.univ ∩ {ω | τ ω ≤ t}) := by
  intro t; simpa using hτ t

/-- Strong Markov property at stopping times of the natural filtration: the shifted process is a standard Brownian motion. -/
theorem isStandardRealBM_procShift [IsProbabilityMeasure P] (hβ : IsStandardRealBM β P)
    {τ : Ω → ℝ≥0∞} (hτ : ∀ t : ℝ≥0, MeasurableSet[realFiltration β t] {ω | τ ω ≤ t})
    (hfin : ∀ᵐ ω ∂P, τ ω < ⊤) : IsStandardRealBM (procShift τ β) P := by
  have hproc : IsProcess β := isProcess_of_realBM hβ
  have hτm : Measurable τ := measurable_of_stopping hproc.2 hτ
  have hsh : IsProcess (procShift τ β) := hproc.shift hτm
  refine isStandardRealBM_iff.2 ⟨hsh.2, fun ω => hsh.1 ω, ?_⟩
  refine IsPreBrownianReal.mk' fun I => ?_
  have hg' : Measurable fun ω => (fun i : I => procShift τ β i ω) :=
    measurable_pi_iff.2 fun i => hsh.2 i
  have hlaw := hβ.isPreBrownianReal.hasLaw I
  refine ⟨hg'.aemeasurable, ?_⟩
  rw [← hlaw.map_eq]
  refine Measure.ext fun S hS => ?_
  have hg : Measurable fun ω => (fun i : I => β i ω) :=
    measurable_pi_iff.2 fun i => hproc.2 i
  change Measure.map (fun ω => (fun i : I => procShift τ β i ω)) P S = _
  rw [Measure.map_apply hg' hS]
  have := measure_inter_cylinder_shift hβ hτ hfin MeasurableSet.univ
    (univ_mem_stoppedSigma hτ) I hS
  simp only [Set.univ_inter, measure_univ, one_mul] at this
  exact this.trans (Measure.map_apply hg hS).symm

/-- Strong Markov property at stopping times of the natural filtration: independence of the stopped `σ`-algebra and the path of the
shifted process. -/
theorem indep_stopped_procShift [IsProbabilityMeasure P] (hβ : IsStandardRealBM β P)
    {τ : Ω → ℝ≥0∞} (hτ : ∀ t : ℝ≥0, MeasurableSet[realFiltration β t] {ω | τ ω ≤ t})
    (hfin : ∀ᵐ ω ∂P, τ ω < ⊤) :
    Indep (stoppedSigma (realFiltration β) τ hτ)
      (MeasurableSpace.comap (fun ω s => procShift τ β s ω) inferInstance) P := by
  have hproc : IsProcess β := isProcess_of_realBM hβ
  have hτm : Measurable τ := measurable_of_stopping hproc.2 hτ
  have hsh : IsProcess (procShift τ β) := hproc.shift hτm
  have hpath : Measurable fun ω s => procShift τ β s ω := measurable_pi_iff.2 fun s => hsh.2 s
  set p₂ : Set (Set Ω) := (fun S => (fun ω s => procShift τ β s ω) ⁻¹' S) ''
    measurableCylinders (fun _ : ℝ≥0 => ℝ) with hp₂
  have hgen : MeasurableSpace.comap (fun ω s => procShift τ β s ω) inferInstance =
      MeasurableSpace.generateFrom p₂ := by
    rw [hp₂, ← MeasurableSpace.comap_generateFrom, generateFrom_measurableCylinders]
  refine IndepSets.indep (stoppedSigma_le) hpath.comap_le
    (@MeasurableSpace.isPiSystem_measurableSet Ω (stoppedSigma (realFiltration β) τ hτ)) ?_
    (@MeasurableSpace.generateFrom_measurableSet Ω (stoppedSigma (realFiltration β) τ hτ)).symm
    hgen ?_
  · exact (isPiSystem_measurableCylinders).comap _
  · rw [IndepSets_iff]
    rintro A B hA ⟨C, hC, rfl⟩
    obtain ⟨I, S, hS, rfl⟩ := (mem_measurableCylinders C).1 hC
    have h1 := measure_inter_cylinder_shift hβ hτ hfin hA.1 hA.2 I hS
    have h2 := measure_inter_cylinder_shift hβ hτ hfin MeasurableSet.univ
      (univ_mem_stoppedSigma hτ) I hS
    simp only [Set.univ_inter, measure_univ, one_mul] at h2
    show P (A ∩ {ω | (fun i : I => procShift τ β i ω) ∈ S}) =
      P A * P {ω | (fun i : I => procShift τ β i ω) ∈ S}
    rw [h1, h2]

end ElboimSly.StrongApprox
