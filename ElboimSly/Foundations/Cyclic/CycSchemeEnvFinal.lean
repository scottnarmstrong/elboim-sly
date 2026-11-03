/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycSchemeEnvLim
public import ElboimSly.Foundations.Cyclic.CycSchemeEnvAe
public import ElboimSly.Foundations.PPP.Exploration.ExplRunOf
public import Mathlib

/-!
# The environment scheme (b): almost sure statement, `s_∘ = ∞`

The environment scheme (b), last sentence. For a run of `cycScheme P ∞ U` (`K ≥ 1`), almost
surely the limit `recLim` of the records `ρ_j(H_j)` is the environment final record `ρ^𝒫(N)`
(`ae_recLim_eq`); `ae_recLim_eq_ppp` states this for the exploration of an arbitrary
`PPP(cycIntensity)` `N` (`ExplRun.ofPPP`). The records are made total by the empty record off the
good event (`recSeqΩ`), which is null (`goodEv_ae`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic
namespace CycSchemeEnv
variable {I : Type*} [MeasurableSpace I] [Countable I] [MeasurableSingletonClass I] {d : ℕ} {β : ℝ}
  [Fact (0 < β)] {P : CycPlan I d β} {sc : ℝ≥0∞}
variable {U : Type*} [MeasurableSpace U] {Ω : Type*} [MeasurableSpace Ω] {Pr : Measure Ω}
variable (run : ExplRun (cycScheme P sc U) Pr)

/-- The event on which the environment is good and all unfinished outcomes are good. -/
def GoodEv (ω : Ω) : Prop :=
  CycGood (run.N ω) ∧ ∀ j : ℕ, (CycScheme.stateAt P sc j (run.H j ω)).2 = false →
    StepGood P sc (run.N ω) (CycScheme.stateAt P sc j (run.H j ω)).1 (run.H (j + 1) ω).last

theorem goodEv_ae : ∀ᵐ ω ∂Pr, GoodEv run ω := by
  filter_upwards [ae_cycGood' run.isPPP, ae_stepGood run] with ω h1 h2
  exact ⟨h1, h2⟩

/-- The trajectory of the scheme along a history. -/
noncomputable def trajOf (ω : Ω) (hω : GoodEv run ω) : Traj P sc (run.N ω) where
  S j := CycScheme.stateAt P sc j (run.H j ω)
  O j := (run.H (j + 1) ω).last
  step j := stateAt_H_succ run j ω
  good j := hω.2 j

open scoped Classical in
/-- The records `ρ_j(H_j)` of the scheme (the empty record off the good event). -/
noncomputable def recSeqΩ (j : ℕ) (ω : Ω) : CycRec I d :=
  if GoodEv run ω then (CycScheme.stateAt P sc j (run.H j ω)).1 else CycRec.empty

theorem hextΩ (hK : 0 < P.K) : ∀ j ω, (recSeqΩ run j ω).Extends (recSeqΩ run (j + 1) ω) := by
  intro j ω
  classical
  by_cases hω : GoodEv run ω
  · unfold recSeqΩ
    rw [ite_eq_left hω, ite_eq_left hω]
    exact (trajOf run ω hω).extends hω.1 hK rfl j
  · unfold recSeqΩ
    rw [ite_eq_right hω, ite_eq_right hω]
    exact CycRec.Extends.refl _

omit [Countable I] [MeasurableSingletonClass I] in
omit [MeasurableSpace I] in
theorem recLim_congr_seq {ρ ρ' : ℕ → Unit → CycRec I d} (h : ρ = ρ') (junk : CycEntry I d)
    (hext : ∀ j ϑ, (ρ j ϑ).Extends (ρ (j + 1) ϑ)) (hext' : ∀ j ϑ, (ρ' j ϑ).Extends (ρ' (j + 1) ϑ)) :
    recLim junk hext () = recLim junk hext' () := by
  subst h; rfl

omit [Countable I] [MeasurableSingletonClass I] in
omit [MeasurableSpace I] in
theorem recLim_point {Θ : Type*} (ρ : ℕ → Θ → CycRec I d) (junk : CycEntry I d)
    (hext : ∀ j ϑ, (ρ j ϑ).Extends (ρ (j + 1) ϑ)) (ϑ : Θ) :
    recLim junk hext ϑ = recLim (ρ := fun j _ => ρ j ϑ) junk (fun j _ => hext j ϑ) () := rfl

/-- The environment scheme (b), last sentence (`s_∘ = ∞`): almost surely the limit of the
records `ρ_j(H_j)` of the scheme is the environment final record `ρ^𝒫(N)`. -/
theorem ae_recLim_eq (hK : 0 < P.K) (hsc : sc = ⊤) (junk : CycEntry I d) :
    ∀ᵐ ω ∂Pr, recLim junk (hextΩ run hK) ω = P.envFinal (run.N ω) := by
  filter_upwards [goodEv_ae run] with ω hω
  rw [recLim_point]
  have hseq : (fun j (_ : Unit) => recSeqΩ run j ω) = (trajOf run ω hω).recSeq := by
    funext j _
    classical
    unfold recSeqΩ
    rw [ite_eq_left hω]
    rfl
  rw [recLim_congr_seq hseq junk _ ((trajOf run ω hω).hext hω.1 hK rfl)]
  exact (trajOf run ω hω).recLim_eq junk hω.1 hK rfl hsc

/-- The environment scheme (b), last sentence (`s_∘ = ∞`), for an arbitrary
`PPP(cycIntensity)` `N` with `u` independent of `N` (and `N'` an independent copy): almost surely
the limit of the records `ρ_j(H_j)` of the exploration of `N` is `ρ^𝒫(N)`. -/
theorem ae_recLim_eq_ppp {u : Ω → U} (hu : Measurable u)
    {N N' : Ω → Measure (CycS I d β)} (hN : IsPoissonPointProcess N (cycIntensity I d β) Pr)
    (hind : IndepFun u N Pr) (hN' : IsPoissonPointProcess N' (cycIntensity I d β) Pr)
    (hind' : IndepFun N' (fun ω => (u ω, N ω)) Pr) (hK : 0 < P.K) (hsc : sc = ⊤)
    (junk : CycEntry I d) :
    ∀ᵐ ω ∂Pr, recLim junk (hextΩ (ExplRun.ofPPP (cycScheme P sc U) hu hN hind hN' hind') hK) ω =
      P.envFinal (N ω) := by
  filter_upwards [ae_recLim_eq (ExplRun.ofPPP (cycScheme P sc U) hu hN hind hN' hind') hK hsc junk,
    hN.tau_comp_ae_eq] with ω h1 h2
  rw [h1]
  exact congrArg P.envFinal h2

end CycSchemeEnv
end ElboimSly.Cyclic

end
