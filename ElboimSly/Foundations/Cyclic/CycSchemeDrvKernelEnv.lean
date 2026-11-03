/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycSchemeDrvMask
public import ElboimSly.Foundations.Cyclic.CycSchemeInst
public import ElboimSly.Foundations.Cyclic.CycSchemeEnvPPP
public import ElboimSly.Foundations.PPP.Exploration.Segment
public import ElboimSly.Foundations.PPP.Exploration.ProbeMeas
public import Mathlib

/-!
# The driving scheme (b), the environment side: the first-point kernel of the environment scheme

The driving scheme (b), "By the environment scheme (a), the masked env probe at
`Ψ_j(η')` is the segment probe with mask `cycReg(ρ)`, case (i). Its kernel is the same formula...".

* `lintegral_probeKernel_comp_equiv'`: the first-point kernel is natural for a measure preserving
  measurable equivalence;
* `cycScheme_lintegral_kernelAt`: the explicit formula for the kernel of the environment scheme,
  with the segment data transported along `cycEquiv`.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace ElboimSly

variable {S T : Type*} [MeasurableSpace S] [MeasurableSpace T]

theorem lintegral_probeKernel_comp_equiv' (e : S ≃ᵐ T) {μ : Measure S} {ν : Measure T}
    (he : MeasurePreserving e μ ν) {R : T → ℝ≥0∞} {h : ℝ≥0} (hR : Measurable R)
    {g : Outcome S → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ o, g o ∂(probeKernel μ (R ∘ e) h) =
      ∫⁻ o, g (o.1, o.2.map e.symm) ∂(probeKernel ν R h) := by
  have hG : Measurable fun o : Outcome T => ((o.1, o.2.map e.symm) : Outcome S) :=
    measurable_fst.prodMk ((measurable_map_measure e.symm.measurable).comp measurable_snd)
  have h2 := lintegral_probeKernel ν R h hR (hg.comp hG)
  simp only [Function.comp_def] at h2
  rw [lintegral_probeKernel _ _ _ (hR.comp e.measurable) hg, h2]
  have hmass : ∀ r, probeMass μ (R ∘ e) r = probeMass ν R r := fun r => by
    unfold probeMass
    exact he.measure_preimage_equiv (probeRegion R r)
  simp only [hmass, Measure.map_zero]
  congr 1
  have hreg : probeRegion (R ∘ e) h = e ⁻¹' probeRegion R h := rfl
  rw [hreg]
  have hΦ : Measurable fun y : T => expNeg (probeMass ν R (R y)) *
      g (R y, (Measure.dirac y).map e.symm) := by
    refine (measurable_expNeg_mass_comp ν R hR).mul (hg.comp ?_)
    exact hR.prodMk ((measurable_map_measure e.symm.measurable).comp Measure.measurable_dirac)
  rw [← he.setLIntegral_comp_preimage_emb e.measurableEmbedding
    (fun y => expNeg (probeMass ν R (R y)) * g (R y, (Measure.dirac y).map e.symm))
    (probeRegion R h)]
  refine lintegral_congr fun x => ?_
  simp only [Function.comp]
  rw [Measure.map_dirac' e.symm.measurable, MeasurableEquiv.symm_apply_apply]

namespace Cyclic

variable {I : Type*} [MeasurableSpace I] [Countable I] [MeasurableSingletonClass I] {d : ℕ}
  {β : ℝ} [Fact (0 < β)] (P : CycPlan I d β) (sc : ℝ≥0∞) {U : Type*} [MeasurableSpace U]

/-- The driving scheme (b), the environment side: the explicit first-point kernel of the
environment scheme (segment probe of segment probes on E×mathbbT_β and E×mathbbR (i) with mask `cycReg(ρ)`), written on
`E × 𝕋` and transported along `cycEquiv`. -/
theorem cycScheme_lintegral_kernelAt (k : ℕ) (η : Hist U (CycS I d β) k)
    {g : Outcome (CycS I d β) → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ o, g o ∂((cycScheme P sc U).kernelAt k η) =
      expNeg (segM (CycScheme.probeA P (CycScheme.stateAt P sc k η))
          (circX (CycScheme.cur P (CycScheme.stateAt P sc k η)).frontT
            (CycScheme.cur P (CycScheme.stateAt P sc k η)).frontS) (fun _ _ => 1)
          (cycEquiv.symm ⁻¹' (CycScheme.stateAt P sc k η).1.region β)
          (CycScheme.hOf P sc (CycScheme.stateAt P sc k η))) *
        g ((CycScheme.hOf P sc (CycScheme.stateAt P sc k η) : ℝ≥0∞), 0) +
      ∑ e ∈ CycScheme.probeA P (CycScheme.stateAt P sc k η),
        ∫⁻ s in Set.Ioc (0 : ℝ) (CycScheme.hOf P sc (CycScheme.stateAt P sc k η)),
          segF (circX (CycScheme.cur P (CycScheme.stateAt P sc k η)).frontT
            (CycScheme.cur P (CycScheme.stateAt P sc k η)).frontS) (fun _ _ => 1)
            (cycEquiv.symm ⁻¹' (CycScheme.stateAt P sc k η).1.region β) e s *
          (expNeg (segM (CycScheme.probeA P (CycScheme.stateAt P sc k η))
              (circX (CycScheme.cur P (CycScheme.stateAt P sc k η)).frontT
                (CycScheme.cur P (CycScheme.stateAt P sc k η)).frontS) (fun _ _ => 1)
              (cycEquiv.symm ⁻¹' (CycScheme.stateAt P sc k η).1.region β) s) *
            g (ENNReal.ofReal s, Measure.dirac (e.1, (e.2,
              circX (CycScheme.cur P (CycScheme.stateAt P sc k η)).frontT
                (CycScheme.cur P (CycScheme.stateAt P sc k η)).frontS e s)))) := by
  classical
  have hZ : (cycScheme P sc U).Z k η = (CycScheme.stateAt P sc k η).1.region β :=
    CycScheme.Z_eq_region P sc (cycScheme P sc U) (fun _ _ => rfl) (fun _ _ => rfl) k η
  have hmask : MeasurableSet (cycEquiv.symm ⁻¹' (CycScheme.stateAt P sc k η).1.region β) := by
    rw [← hZ]; exact measurableSet_cycMask ((cycScheme P sc U).measurableSet_Zη k η)
  have hσ := (CycScheme.cur P (CycScheme.stateAt P sc k η)).frontS_cases
  have hh := CycScheme.hOf_le_beta P sc (CycScheme.stateAt P sc k η)
  have hS := segSetup_circle (β := β)
    (CycScheme.probeA P (CycScheme.stateAt P sc k η))
    (CycScheme.cur P (CycScheme.stateAt P sc k η)).frontT
    (CycScheme.cur P (CycScheme.stateAt P sc k η)).frontS hσ
    (CycScheme.hOf P sc (CycScheme.stateAt P sc k η)) hh
  have hRm := measurable_segR hS hmask
  have hG : Measurable fun o : Outcome (CycS I d β) => g (o.1, o.2) := hg
  unfold ExplScheme.kernelAt
  rw [cycScheme_Rt, hZ]
  have e1 : cycSegR (CycScheme.probeA P (CycScheme.stateAt P sc k η))
      (circX (CycScheme.cur P (CycScheme.stateAt P sc k η)).frontT
        (CycScheme.cur P (CycScheme.stateAt P sc k η)).frontS)
      (circS (CycScheme.cur P (CycScheme.stateAt P sc k η)).frontT
        (CycScheme.cur P (CycScheme.stateAt P sc k η)).frontS)
      (CycScheme.hOf P sc (CycScheme.stateAt P sc k η))
      ((CycScheme.stateAt P sc k η).1.region β) =
      segR (CycScheme.probeA P (CycScheme.stateAt P sc k η))
      (circX (CycScheme.cur P (CycScheme.stateAt P sc k η)).frontT
        (CycScheme.cur P (CycScheme.stateAt P sc k η)).frontS)
      (circS (CycScheme.cur P (CycScheme.stateAt P sc k η)).frontT
        (CycScheme.cur P (CycScheme.stateAt P sc k η)).frontS)
      (CycScheme.hOf P sc (CycScheme.stateAt P sc k η))
      (cycEquiv.symm ⁻¹' (CycScheme.stateAt P sc k η).1.region β) ∘ cycEquiv := rfl
  rw [e1, lintegral_probeKernel_comp_equiv' cycEquiv cycEquiv_measurePreserving hRm hg]
  have hGm : Measurable fun o : Outcome ((I × Edge d) × AddCircle β) =>
      g (o.1, o.2.map (cycEquiv (I := I) (d := d) (β := β)).symm) :=
    hg.comp (measurable_fst.prodMk ((measurable_map_measure
      (cycEquiv (I := I) (d := d) (β := β)).symm.measurable).comp measurable_snd))
  refine Eq.trans (lintegral_segKernel hS hmask hGm) ?_
  simp only [Measure.map_zero]
  congr 1
  refine Finset.sum_congr rfl fun e _ => ?_
  refine lintegral_congr fun s => ?_
  rw [Measure.map_dirac' (cycEquiv (I := I) (d := d) (β := β)).symm.measurable]
  rfl


end Cyclic

end ElboimSly

end
