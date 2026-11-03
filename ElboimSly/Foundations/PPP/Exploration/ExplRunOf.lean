/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.PPP.Exploration.SegmentReal
public import ElboimSly.Foundations.PPP.Exploration.ThmStop
import Mathlib

/-!
# Discharging the locally-finite premise of `ExplRun`

Sequential first-point exploration together with finiteness and local finiteness (c). `ExplRun` assumes that `N` and
`N'` take values in `𝓜^lf`. This is no restriction: `τ ∘ N` is a PPP, equals `N` almost surely, and
is `𝓜^lf`-valued. `ExplRun.ofPPP` builds the run for `τ ∘ N` and `τ ∘ N'` from arbitrary PPPs, and
the `ae_*` lemmas transfer the conclusions back to `N`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace ElboimSly

variable {S : Type*} [MeasurableSpace S] {U : Type*} [MeasurableSpace U] {μ : Measure S}
  [SigmaFinite μ] {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- Sequential first-point exploration with finiteness and local finiteness (c): the exploration run of `τ ∘ N` and
`τ ∘ N'` for arbitrary PPPs `N`, `N'` of intensity `μ`, with `u` independent of `N` and `N'`
independent of `(u, N)`. -/
noncomputable def ExplRun.ofPPP (sch : ExplScheme μ U) {u : Ω → U} (hu : Measurable u)
    {N N' : Ω → Measure S} (hN : IsPoissonPointProcess N μ P) (hind : IndepFun u N P)
    (hN' : IsPoissonPointProcess N' μ P) (hind' : IndepFun N' (fun ω => (u ω, N ω)) P) :
    ExplRun sch P where
  u := u
  N := fun ω => tau μ (N ω)
  N' := fun ω => tau μ (N' ω)
  measurable_u := hu
  isPPP := hN.tau_comp
  indep := hind.comp measurable_id (measurable_tau μ)
  isPPP' := hN'.tau_comp
  indep' := hind'.comp (measurable_tau μ) (measurable_id.prodMap (measurable_tau μ))
  lf := fun _ω => tau_mem_lfSet μ _
  lf' := fun _ω => tau_mem_lfSet μ _

namespace ExplRun

variable (sch : ExplScheme μ U) {u : Ω → U} (hu : Measurable u)
  {N N' : Ω → Measure S} (hN : IsPoissonPointProcess N μ P) (hind : IndepFun u N P)
  (hN' : IsPoissonPointProcess N' μ P) (hind' : IndepFun N' (fun ω => (u ω, N ω)) P)

include hu hN hind hN' hind'

end ExplRun

end ElboimSly
