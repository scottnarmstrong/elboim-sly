/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycSchemeDrvKernelEnv
public import ElboimSly.Foundations.Cyclic.CycSchemeDrvEdge
public import Mathlib

/-!
# The driving scheme (b), the driving side: the first-point kernel of the driving scheme

The driving scheme (b), "by segment probes on E×mathbbT_β and E×mathbbR (a) in case (ii),
`K'_j(η') = e^{-m(h)} δ_{(h,0)} + Σ_v ∫_0^h f'(v,t) e^{-m(t)} δ_{(t, δ_{(j_k,v,a_k+r+t)})} dt`".
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

open SRW

variable {I : Type*} [MeasurableSpace I] [Countable I] [MeasurableSingletonClass I] {d : ℕ}
  {β : ℝ} [Fact (0 < β)]
  {J : Type*} [MeasurableSpace J] [Countable J] [MeasurableSingletonClass J]
  {jx : ∀ k : ℕ, CycRecN I d k → J} (j0 : J) (P : CycPlan I d β) (sc : ℝ≥0∞)
  (U : Type*) [MeasurableSpace U] (hj : ∀ k, Measurable (jx k))

/-- The segment `x_e(s) = (a_k + r) + s` of the driving probe. -/
noncomputable def drvX (st : CycScheme.State I d) : Dir d × J → ℝ → ℝ := fun _ s => drvT jx P st + 1 * s

/-- The weight `w_e(s) = 1_{(0,∞)}(a_k + r + s)` of the driving probe. -/
noncomputable def drvW (st : CycScheme.State I d) : Dir d × J → ℝ → ℝ≥0∞ :=
  fun _ s => (Set.Ioi (0 : ℝ)).indicator (fun _ => (1 : ℝ≥0∞)) (drvT jx P st + 1 * s)

/-- The driving scheme (b), the driving side: the explicit first-point kernel of the
driving scheme (segment probe of segment probes on E×mathbbT_β and E×mathbbR (ii)). -/
theorem drvScheme_lintegral_kernelAt (k : ℕ) (η : Hist U (DrvS d J) k)
    {g : Outcome (DrvS d J) → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ o, g o ∂((drvScheme j0 P sc U hj).kernelAt k η) =
      (let st := CycScheme.stateAt P sc k (drvPsi jx j0 P sc U k η)
       expNeg (segM (drvA jx j0 st) (drvX (jx := jx) P st) (drvW (jx := jx) P st)
          (drvMask (β := β) jx P st) (CycScheme.hOf P sc st)) *
        g ((CycScheme.hOf P sc st : ℝ≥0∞), 0) +
      ∑ a ∈ drvA jx j0 st,
        ∫⁻ s in Set.Ioc (0 : ℝ) (CycScheme.hOf P sc st),
          segF (drvX (jx := jx) P st) (drvW (jx := jx) P st) (drvMask (β := β) jx P st) a s *
          (expNeg (segM (drvA jx j0 st) (drvX (jx := jx) P st) (drvW (jx := jx) P st)
              (drvMask (β := β) jx P st) s) *
            g (ENNReal.ofReal s, Measure.dirac (a, drvX (jx := jx) P st a s)))) := by
  classical
  dsimp only
  set st := CycScheme.stateAt P sc k (drvPsi jx j0 P sc U k η) with hst
  have hmask : MeasurableSet (drvMask (β := β) jx P st) :=
    measurable_prodMk_left (measurableSet_drvMask P hj)
  have hS := segSetup_real (E := Dir d × J) (drvA jx j0 st) (fun _ => drvT jx P st) (fun _ => 1)
    (fun _ => Or.inl rfl) (CycScheme.hOf P sc st) (I := Set.Ioi 0) measurableSet_Ioi
  unfold ExplScheme.kernelAt
  rw [drvScheme_Rt j0 P sc U hj]
  show ∫⁻ o, g o ∂(probeKernel (drvIntensity d J) (drvProbeR (β := β) jx j0 P sc st)
    (CycScheme.hOf P sc st)) = _
  rw [drvProbeR_eq_segR]
  exact lintegral_segKernel (lam := volume.restrict (Set.Ioi (0 : ℝ))) hS hmask hg

end ElboimSly.Cyclic

end
