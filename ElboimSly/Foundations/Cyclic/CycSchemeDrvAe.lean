/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycSchemeDrvStep
public import ElboimSly.Foundations.Cyclic.CycSchemeDrvScheme
public import ElboimSly.Foundations.Cyclic.CycSchemeDrvMask
public import ElboimSly.Foundations.PPP.Exploration.ThmDirac
public import ElboimSly.Foundations.PPP.DissectingExamples
public import ElboimSly.Foundations.SRW.GoodAe
public import ElboimSly.Foundations.SRW.Iid
public import ElboimSly.Foundations.Cyclic.CycSchemeEnvPPP
public import Mathlib

/-!
# The driving scheme (c): the almost sure events of the driving exploration

The driving scheme (c), "Let `Ω'_1` be the event that every `X_j` is on its good event
(good event and path properties), `N'` is simple (simplicity) and, for every `j`, the form of
`(r̄'_j, V'_j)` given by sequential first-point exploration (d, f) holds".

* `ae_drvGood`: almost surely, for every `j`, the outcome of step `j` of the driving exploration is a
  good outcome (`DrvGood`) for the state `ρ_j(Ψ_j(H'_j))`;
* `ae_subGood`: almost surely every sub-process `N'^j` is on the good event of good event and path properties.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic
namespace CycSchemeGen
open SRW

variable {I : Type*} [MeasurableSpace I] [Countable I] [MeasurableSingletonClass I] {d : ℕ}
  {β : ℝ} [Fact (0 < β)] {J : Type} [MeasurableSpace J] [Countable J] [MeasurableSingletonClass J]
  {jx : ∀ k : ℕ, CycRecN I d k → J} (j0 : J) (P : CycPlan I d β) (sc : ℝ≥0∞)
  {U : Type*} [MeasurableSpace U] (hj : ∀ k, Measurable (jx k))
  {Ω : Type} [MeasurableSpace Ω] {Pr : Measure Ω}

omit [Countable J] [MeasurableSingletonClass J] in
theorem drvIntensity_singleton (x : DrvS d J) : drvIntensity d J {x} = 0 :=
  clockIntensity_singleton (D := Dir d × J) x

/-- The driving scheme (c): almost surely, at every step the outcome of the driving
exploration is a good outcome (sequential first-point exploration (d), (f)). -/
theorem ae_drvGood (run : ExplRun (drvScheme j0 P sc U hj) Pr) :
    ∀ᵐ ω ∂Pr, ∀ j : ℕ, DrvGood jx j0 P sc (run.N ω)
      (CycScheme.stateAt P sc j (drvPsi jx j0 P sc U j (run.H j ω))) (run.H (j + 1) ω).last := by
  rw [ae_all_iff]
  intro j
  filter_upwards [run.ae_front j, run.ae_dirac_front (clockSeq (Dir d × J))
    (clockSeq_isDissecting (Dir d × J)) drvIntensity_singleton j, run.ae_rho_eq_h j] with ω hfront
    hdirac hzero
  have hRt : (drvScheme j0 P sc U hj).Rt j (run.H j ω) = (drvScheme j0 P sc U hj).R j (run.H j ω) :=
    drvScheme_Rt j0 P sc U hj j (run.H j ω)
  have hl : (run.H (j + 1) ω).last =
      (drvScheme j0 P sc U hj).stepAt j (run.H j ω) (run.N ω) :=
    (drvScheme j0 P sc U hj).Hfun_last j (run.X ω)
  have h1 : (run.H (j + 1) ω).last.1 =
      probeRho (drvIntensity d J) ((drvScheme j0 P sc U hj).Rt j (run.H j ω))
        ((drvScheme j0 P sc U hj).h j (run.H j ω)) (run.N ω) := by rw [hl]; rfl
  have h2 : (run.H (j + 1) ω).last.2 = (run.N ω).restrict
      (probeRegion ((drvScheme j0 P sc U hj).Rt j (run.H j ω)) (run.H (j + 1) ω).last.1) := by
    rw [h1, hl]
    show probeV _ _ _ _ = _
    unfold probeV
    rw [tau_of_mem (drvIntensity d J) (run.lf ω)]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h2, hRt]; rfl
  · rw [h1]; exact probeRho_le_h
  · have := hfront
    rw [hRt] at this
    exact this
  · intro hne
    obtain ⟨x, hx1, -, hx3⟩ := hdirac hne
    rw [hRt] at hx3
    exact ⟨x, hx1, hx3⟩
  · intro hz; exact hzero hz
  · rw [h2]
    exact tau_of_mem (drvIntensity d J) (restrict_mem_lfSet (run.lf ω) _)

/-- Almost surely every sub-process `N'^j` is on the good event of good event and path properties. -/
theorem ae_subGood (run : ExplRun (drvScheme j0 P sc U hj) Pr) :
    ∀ᵐ ω ∂Pr, ∀ j : J, relabel {x : Dir d × J | x.2 = j} Prod.fst (run.N ω) ∈ goodSet d := by
  rw [ae_all_iff]
  intro j
  exact ae_good (subProcess_ppp run.isPPP j)

end CycSchemeGen
end ElboimSly.Cyclic

end
