/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycSchemeDrvAe
public import ElboimSly.Foundations.Cyclic.CycSchemeEnvZ
public import ElboimSly.Foundations.Cyclic.CycSchemeDrvLaw
public import Mathlib

/-!
# The driving scheme (c): the records of the driving exploration are the driven world-lines

The driving scheme (c). "On an event of probability one, for every `j`,
`ρ_j(Ψ_j(H'_j))` consists of initial pieces of the driven world-lines of `𝒫` driven by `(X_j)` with
the assignment `(𝖩_k)`" (`ae_drvInv`), and, with non-explosion, `Φ(Ψ_∞(H'_∞))` is the driven final
record `ρ^𝒫(X)` (`ae_recPhi_drvPsiInf`).

`drvTraj` is the trajectory `S_j = (ρ_j, ε_j)(Ψ_j(H'_j))`, `O_j = ψ_{H'_j}(o'_j)` of the environment
scheme; on the good event its steps are correct for the driven rule `drl` (`gstep_drv`), so that
`GTraj.recLim_eq` applies.
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
  (run : ExplRun (drvScheme j0 P sc U hj) Pr)

theorem stateAt_succ_drv (j : ℕ) (ω : Ω) :
    CycScheme.stateAt P sc (j + 1) (drvPsi jx j0 P sc U (j + 1) (run.H (j + 1) ω)) =
      CycScheme.upd P sc (CycScheme.stateAt P sc j (drvPsi jx j0 P sc U j (run.H j ω)))
        (drvPsiOut (jx := jx) (β := β) j0 P sc
          (CycScheme.stateAt P sc j (drvPsi jx j0 P sc U j (run.H j ω)))
          (run.H (j + 1) ω).last) := by
  have h1 := stateAt_drvPsi_succ (jx := jx) j0 P sc U j (run.H (j + 1) ω)
  rw [show (run.H (j + 1) ω).init = run.H j ω from
    (drvScheme j0 P sc U hj).Hfun_init j _] at h1
  exact h1

omit [MeasurableSpace U] in
theorem good_of_drvGood {rl : PathRule I d} {Ñ : Measure (DrvS d J)} (st : CycScheme.State I d)
    (o' : Outcome (DrvS d J))
    (key : ∀ ρ : CycRec I d, DrvGood jx j0 P sc Ñ (ρ, false) o' → ∀ k r, GAt P rl k r ρ →
      GStep P sc rl k r ρ (drvPsiOut (jx := jx) (β := β) j0 P sc (ρ, false) o'))
    (hst : st.2 = false) (hg : DrvGood jx j0 P sc Ñ st o') :
    ∀ k r, GAt P rl k r st.1 → GStep P sc rl k r st.1
      (drvPsiOut (jx := jx) (β := β) j0 P sc st o') := by
  obtain ⟨ρ, b⟩ := st
  simp only at hst
  subst hst
  exact key ρ hg

/-- The trajectory of the environment scheme along `Ψ_j(H'_j)`, on the good event. -/
noncomputable def drvTraj (ω : Ω)
    (hD : ∀ j : ℕ, DrvGood jx j0 P sc (run.N ω)
      (CycScheme.stateAt P sc j (drvPsi jx j0 P sc U j (run.H j ω))) (run.H (j + 1) ω).last)
    (hS : ∀ j : J, relabel {x : Dir d × J | x.2 = j} Prod.fst (run.N ω) ∈ goodSet d) :
    GTraj P sc (drl P jx (run.N ω)) where
  S j := CycScheme.stateAt P sc j (drvPsi jx j0 P sc U j (run.H j ω))
  O j := drvPsiOut (jx := jx) (β := β) j0 P sc
    (CycScheme.stateAt P sc j (drvPsi jx j0 P sc U j (run.H j ω))) (run.H (j + 1) ω).last
  step j := stateAt_succ_drv j0 P sc hj run j ω
  zero := zeroRule_drule P jx _
  good j hst := good_of_drvGood j0 P sc _ _
    (fun _ρ hg _k _r h => gstep_drv j0 hj hS h hg) hst (hD j)

variable (hK : 0 < P.K) (hsc : sc = ⊤)
include hK hsc

omit hsc in
/-- The driving scheme (c): almost surely, for every `j`, the state
`(ρ_j, ε_j)(Ψ_j(H'_j))` consists of the first `k` driven world-lines in full and an initial piece of
the driven world-line of walk `k` (`GInv`). -/
theorem ae_drvInv :
    ∀ᵐ ω ∂Pr, ∀ j : ℕ, GInv P sc (drl P jx (run.N ω))
      (CycScheme.stateAt P sc j (drvPsi jx j0 P sc U j (run.H j ω))) := by
  filter_upwards [ae_drvGood j0 P sc hj run, ae_subGood j0 P sc hj run] with ω hD hS j
  exact (drvTraj j0 P sc hj run ω hD hS).inv hK rfl j

/-- The driving scheme (c) with non-explosion, as used in several walks explored one after another
(b): almost surely `Φ(Ψ_∞(H'_∞)) = ρ^𝒫(X)`, the driven final record of `𝒫` driven by the canonical
walks `X_j` of the driving process. -/
theorem ae_recPhi_drvPsiInf :
    ∀ᵐ ω ∂Pr, CycSchemeEnv.recPhi P sc U P.junk
        (drvPsiInf (jx := jx) (β := β) j0 P sc (run.Hinf ω)) =
      P.drivenFinal jx (fun j => srwPath (run.N ω) j) := by
  filter_upwards [ae_drvGood j0 P sc hj run, ae_subGood j0 P sc hj run] with ω hD hS
  have hT := (drvTraj j0 P sc hj run ω hD hS).recLim_eq P.junk hK rfl hsc
  rw [drivenFinal_eq_cycFinal, ← hT]
  unfold CycSchemeEnv.recPhi
  rw [CycSchemeEnv.recLim_point (ρ := CycSchemeEnv.recSeqY P sc U)]
  refine CycSchemeEnv.recLim_congr_seq ?_ P.junk _ _
  funext j _
  show (CycScheme.stateAt P sc j (truncHist j (drvPsiInf (jx := jx) (β := β) j0 P sc
    (run.Hinf ω)))).1 = (CycScheme.stateAt P sc j (drvPsi jx j0 P sc U j (run.H j ω))).1
  rw [truncHist_drvPsiInf, run.H_eq_trunc j ω]

end CycSchemeGen
end ElboimSly.Cyclic

end
