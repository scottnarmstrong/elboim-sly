/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Brownian.Defs
import Mathlib

/-!
# Gaussian-process characterization: the "only if" direction

Gaussian-process characterization ("only if" direction; the "if" direction is
`isStandardBrownianMotion_of_gaussian` in `Existence.lean`).

A standard `d`-dimensional Brownian motion gives a Gaussian process indexed by
`Σ _ : Fin d, ℝ≥0`, centred, with covariance `δ_{ij} min(s,t)`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace ElboimSly.Brownian

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {d : ℕ}

/-- Gaussian-process characterization (Gaussian part of "only if"). -/
theorem _root_.ElboimSly.IsStandardBrownianMotion.isGaussianProcess [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → (Fin d → ℝ)} (hB : IsStandardBrownianMotion d B P) :
    IsGaussianProcess (fun (p : Σ _ : Fin d, ℝ≥0) ω => B p.2 ω p.1) P := by
  classical
  refine ⟨fun J => ?_⟩
  set I : Finset ℝ≥0 := J.image (fun p => p.2) with hI
  let V : Fin d → Ω → (I → ℝ) := fun i ω => I.restrict (fun t => B t ω i)
  have hVlaw : ∀ i, HasGaussianLaw (V i) P := fun i =>
    ((hB.isPreBrownianReal i).isGaussianProcess.hasGaussianLaw I)
  have hVind : iIndepFun V P :=
    hB.iIndepFun.comp (fun _ (w : ℝ≥0 → ℝ) => I.restrict w)
      (fun _ => measurable_pi_iff.2 fun t => measurable_pi_apply _)
  have hjoint := iIndepFun.hasGaussianLaw hVlaw hVind
  let L : (Fin d → I → ℝ) →L[ℝ] (J → ℝ) :=
    { toFun := fun x p => x p.1.1 ⟨p.1.2, Finset.mem_image_of_mem _ p.2⟩
      map_add' := fun x y => rfl
      map_smul' := fun c x => rfl }
  exact hjoint.map L

/-- Gaussian-process characterization (mean part of "only if"). -/
theorem _root_.ElboimSly.IsStandardBrownianMotion.integral_eval [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → (Fin d → ℝ)} (hB : IsStandardBrownianMotion d B P) (p : Σ _ : Fin d, ℝ≥0) :
    ∫ ω, B p.2 ω p.1 ∂P = 0 :=
  (hB.isPreBrownianReal p.1).integral_eval p.2

/-- Gaussian-process characterization (covariance part of "only if"). -/
theorem _root_.ElboimSly.IsStandardBrownianMotion.covariance_eval [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → (Fin d → ℝ)} (hB : IsStandardBrownianMotion d B P) (p q : Σ _ : Fin d, ℝ≥0) :
    cov[fun ω => B p.2 ω p.1, fun ω => B q.2 ω q.1; P] =
      if p.1 = q.1 then ((min p.2 q.2 : ℝ≥0) : ℝ) else 0 := by
  split_ifs with h
  · obtain ⟨i, s⟩ := p
    obtain ⟨j, t⟩ := q
    simp only at h
    subst h
    exact (hB.isPreBrownianReal i).covariance_fun_eval s t
  · have hind : IndepFun (fun ω => B p.2 ω p.1) (fun ω => B q.2 ω q.1) P := by
      have := hB.iIndepFun.indepFun h
      exact this.comp (measurable_pi_apply p.2) (measurable_pi_apply q.2)
    exact hind.covariance_eq_zero
      ((hB.isPreBrownianReal p.1).isGaussianProcess.hasGaussianLaw_eval p.2).memLp_two
      ((hB.isPreBrownianReal q.1).isGaussianProcess.hasGaussianLaw_eval q.2).memLp_two

end ElboimSly.Brownian
