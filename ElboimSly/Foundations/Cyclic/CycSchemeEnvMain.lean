/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycSchemeEnvC
public import ElboimSly.Foundations.Cyclic.CycSchemeEnvFinalFin
public import ElboimSly.Foundations.Cyclic.CycSchemeInst
public import ElboimSly.Foundations.Cyclic.CycSchemeEnvPPP
public import ElboimSly.Foundations.Cyclic.CycSchemeRegionZ
public import ElboimSly.Foundations.PPP.Exploration.Segment
public import ElboimSly.Foundations.PPP.Exploration.SegmentCircle
public import ElboimSly.Foundations.PPP.Exploration.ThmKernel
public import ElboimSly.Foundations.PPP.Exploration.ThmRun
public import Mathlib

/-!
# Summary of the Lean statements

The environment scheme (a), (b), (c), for a plan `P` with `0 < P.K` and any global horizon
`s_∘ = sc ∈ [0, ∞]`. All declarations are in the namespace `ElboimSly.Cyclic`.

**(a)** The scheme is `cycScheme P sc U` (`CycSchemeInst`); `η ↦ (ρ_j(η), ε_j(η))` is
`CycScheme.stateAt` (`CycScheme.measurable_stateAt`); the explored region is the region of the
record (`CycScheme.Z_eq_region`); the masked probe is the cyclic segment probe (`cycScheme_Rt`); the
first-point kernel is `lintegral_kernelAt_cycScheme`.

**(b)** `CycSchemeEnv.ae_inv`, `CycSchemeEnv.ae_initial_pieces` (initial pieces of the environment
world-lines, `N|_{𝒵_j} = cycRM(ρ_j)`); the records `ρ_j(H_j)` extend each other for every history
(`CycScheme.extends_stateAt_trunc`); and almost surely the limit of the records is `cycRec^𝒫(s_∘)`
(`CycSchemeEnv.ae_recLim_eq_cycRecAt`, `CycSchemeEnv.ae_recLim_eq_cycRecAt_ppp`), with
`cycRecAt P ν sc = ρ^𝒫(ν)` if `sc = ∞` and `Trunc_{sc}(ρ^𝒫(ν))` otherwise.

**(c)** `CycSchemeEnv.isStopping_kappa`, `CycSchemeEnv.ae_Zkappa_eq`,
`CycSchemeEnv.exists_gKappa_measurable_cycRec`; bundled in `cyc_env_scheme_c`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic
namespace CycSchemeEnv
variable {I : Type*} [MeasurableSpace I] [Countable I] [MeasurableSingletonClass I] {d : ℕ} {β : ℝ}
  [Fact (0 < β)] {P : CycPlan I d β} {sc : ℝ≥0∞}
variable {U : Type*} [MeasurableSpace U] {Ω : Type*} [MeasurableSpace Ω] {Pr : Measure Ω}

/-- The environment scheme (c): `κ` is a `𝒢`-stopping index; almost surely
`𝒵_κ = R^𝒫_{s_∘}` (the region of `cycRec^𝒫(s_∘)`, `𝒵_∞ = ⋃_j 𝒵_j`); and for every `s' ≤ s_∘`,
`cycRec^𝒫(s') = Trunc_{s'}(ρ^𝒫(N))` coincides almost surely with a `𝒢_κ`-measurable random
element. -/
theorem cyc_env_scheme_c (run : ExplRun (cycScheme P sc U) Pr) (hK : 0 < P.K) :
    run.IsStopping (kappa run) ∧
      (∀ᵐ ω ∂Pr, Zkappa run ω = (cycRecAt P (run.N ω) sc).region β) ∧
      ∀ s' : ℝ≥0, (s' : ℝ≥0∞) ≤ sc → ∃ Y : Ω → CycRec I d,
        (∀ B : Set (CycRec I d), MeasurableSet B → run.InGkappa (kappa run) (Y ⁻¹' B)) ∧
          ∀ᵐ ω ∂Pr, Y ω = CycRec.trunc s' (P.envFinal (run.N ω)) :=
  ⟨isStopping_kappa run, ae_Zkappa_eq run hK, fun _ hs => exists_gKappa_measurable_cycRec run hK hs⟩

end CycSchemeEnv
end ElboimSly.Cyclic

end
