/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.PPP.Exploration.ThmInduct
import Mathlib

/-!
# Sequential first-point exploration: the setting and parts (b), (d)

Sequential first-point exploration.

An `ExplRun` packages the premises of the theorem: `N ~ PPP(μ)`, an auxiliary random element `U`
independent of `N`, and `N' ~ PPP(μ)` independent of `(U, N)`, with `N` and `N'` taking values in
`𝓜^lf` (which is no restriction by finiteness and local finiteness(c)).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace ElboimSly

variable {S : Type*} [MeasurableSpace S] {U : Type*} [MeasurableSpace U] {μ : Measure S}
  [SigmaFinite μ] (sch : ExplScheme μ U) {Ω : Type*} [MeasurableSpace Ω]

/-- The premises of sequential first-point exploration. -/
structure ExplRun (sch : ExplScheme μ U) (P : Measure Ω) where
  /-- The auxiliary random element `U`. -/
  u : Ω → U
  /-- The configuration `N`. -/
  N : Ω → Measure S
  /-- The independent copy `N'`. -/
  N' : Ω → Measure S
  measurable_u : Measurable u
  isPPP : IsPoissonPointProcess N μ P
  indep : IndepFun u N P
  isPPP' : IsPoissonPointProcess N' μ P
  indep' : IndepFun N' (fun ω => (u ω, N ω)) P
  lf : ∀ ω, N ω ∈ lfSet μ
  lf' : ∀ ω, N' ω ∈ lfSet μ

variable {sch} {P : Measure Ω} (run : ExplRun sch P)

include run

namespace ExplRun

theorem prob : IsProbabilityMeasure P := run.isPPP.isProbabilityMeasure

/-- The pair `X = (U, N)`. -/
def X (ω : Ω) : U × Measure S := (run.u ω, run.N ω)

/-- The history `H_k` of the exploration. -/
noncomputable def H (k : ℕ) (ω : Ω) : Hist U S k := sch.Hfun k (run.X ω)

theorem measurable_X : Measurable run.X :=
  run.measurable_u.prodMk run.isPPP.measurable

theorem measurable_H (k : ℕ) : Measurable (run.H k) :=
  (sch.measurable_Hfun k).comp run.measurable_X

theorem isPPPLaw : IsPPPLaw μ (P.map run.N) := run.isPPP.isPPPLaw

theorem law_X : P.map run.X = (P.map run.u).prod (P.map run.N) := by
  have := run.prob
  exact (indepFun_iff_map_prod_eq_prod_map_map run.measurable_u.aemeasurable
    run.isPPP.measurable.aemeasurable).1 run.indep

theorem lintegral_X {φ : U × Measure S → ℝ≥0∞} (hφ : Measurable φ) :
    ∫⁻ ω, φ (run.X ω) ∂P = ∫⁻ x, φ x ∂((P.map run.u).prod (P.map run.N)) := by
  rw [← run.law_X, lintegral_map hφ run.measurable_X]

theorem unexpl_N (k : ℕ) (η : Hist U S k) (ω : Ω) :
    sch.unexpl k η (run.N ω) = (run.N ω).restrict (sch.Z k η)ᶜ := by
  unfold ExplScheme.unexpl
  rw [tau_of_mem μ (run.lf ω)]

/-- Sequential first-point exploration (b): the unexplored part is fresh. -/
theorem fresh {k : ℕ} {F : Hist U S k × Measure S → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ ω, F (run.H k ω, (run.N ω).restrict (sch.Z k (run.H k ω))ᶜ) ∂P =
      ∫⁻ ω, ∫⁻ ν, F (run.H k ω, sch.unexpl k (run.H k ω) ν) ∂(P.map run.N) ∂P := by
  have := run.prob
  have : IsProbabilityMeasure (P.map run.u) := ⟨by rw [Measure.map_apply run.measurable_u MeasurableSet.univ]; simp⟩
  have hm1 : Measurable fun x : U × Measure S =>
      F (sch.Hfun k x, sch.unexpl k (sch.Hfun k x) x.2) :=
    hF.comp ((sch.measurable_Hfun k).prodMk ((sch.measurable_unexpl k).comp
      ((sch.measurable_Hfun k).prodMk measurable_snd)))
  have hm2 : Measurable fun x : U × Measure S =>
      ∫⁻ ν, F (sch.Hfun k x, sch.unexpl k (sch.Hfun k x) ν) ∂(P.map run.N) :=
    Measurable.lintegral_prod_right' (f := fun p : (U × Measure S) × Measure S =>
      F (sch.Hfun k p.1, sch.unexpl k (sch.Hfun k p.1) p.2))
      (hF.comp (((sch.measurable_Hfun k).comp measurable_fst).prodMk ((sch.measurable_unexpl k).comp
        (((sch.measurable_Hfun k).comp measurable_fst).prodMk measurable_snd))))
  have h1 := sch.freshAt_all (P.map run.u) run.isPPPLaw k F hF
  have e1 : ∀ ω, F (run.H k ω, (run.N ω).restrict (sch.Z k (run.H k ω))ᶜ) =
      F (sch.Hfun k (run.X ω), sch.unexpl k (sch.Hfun k (run.X ω)) (run.X ω).2) := by
    intro ω
    show _ = F (run.H k ω, sch.unexpl k (run.H k ω) (run.N ω))
    rw [run.unexpl_N]
  simp_rw [e1]
  rw [run.lintegral_X hm1, h1]
  exact (run.lintegral_X hm2).symm

/-- Sequential first-point exploration (d): the one-step law. -/
theorem stepLaw {k : ℕ} {g : Hist U S (k + 1) → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ ω, g (run.H (k + 1) ω) ∂P =
      ∫⁻ ω, ∫⁻ o, g ((run.H k ω).snoc o) ∂(sch.kernelAt k (run.H k ω)) ∂P := by
  have := run.prob
  have : IsProbabilityMeasure (P.map run.u) := ⟨by rw [Measure.map_apply run.measurable_u MeasurableSet.univ]; simp⟩
  have hm1 : Measurable fun x : U × Measure S => g (sch.Hfun (k + 1) x) :=
    hg.comp (sch.measurable_Hfun (k + 1))
  have hm2 : Measurable fun x : U × Measure S =>
      ∫⁻ o, g ((sch.Hfun k x).snoc o) ∂(sch.kernelAt k (sch.Hfun k x)) := by
    have hk : Measurable fun η : Hist U S k => ∫⁻ o, g (η.snoc o) ∂(sch.kernelAt k η) :=
      measurable_lintegral_probeKernel μ (R := sch.Rt k) (h := sch.h k) (sch.measurable_Rt k)
        (sch.measurable_h k) (g := fun p : Hist U S k × Outcome S => g (p.1.snoc p.2))
        (hg.comp (Hist.measurable_snoc k))
    exact hk.comp (sch.measurable_Hfun k)
  have h1 := sch.stepLawAt_all (P.map run.u) run.isPPPLaw k g hg
  change ∫⁻ ω, (fun x => g (sch.Hfun (k + 1) x)) (run.X ω) ∂P =
    ∫⁻ ω, (fun x => ∫⁻ o, g ((sch.Hfun k x).snoc o) ∂(sch.kernelAt k (sch.Hfun k x))) (run.X ω) ∂P
  rw [run.lintegral_X hm1, run.lintegral_X hm2, h1]

end ExplRun

end ElboimSly
