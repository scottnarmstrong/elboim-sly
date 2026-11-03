/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycSchemeEnvTruncNth
public import ElboimSly.Foundations.Cyclic.CycSchemeEnvFinal
public import Mathlib

/-!
# The environment scheme (b): almost sure statement, every horizon `s_∘`

The environment scheme (b), last sentence. `cycRecAt P ν sc` is `cycRec^𝒫(s_∘)`: the
final record `ρ^𝒫(ν)` if `s_∘ = ∞` and the truncation `Trunc_{s_∘}(ρ^𝒫(ν))` otherwise.

* `Traj.recLim_eq_trunc`: for a trajectory with finite `s_∘`, the limit of the records is
  `Trunc_{s_∘}(ρ^𝒫(ν))`.
* `ae_recLim_eq_trunc`: almost surely, for a run of `cycScheme P sc U`, `sc ≠ ∞`, the limit of the
  records `ρ_j(H_j)` is `Trunc_{s_∘}(ρ^𝒫(N))`.
* `ae_recLim_eq_cycRecAt`, `ae_recLim_eq_cycRecAt_ppp`: both cases in one statement; the second for
  the exploration of an arbitrary `PPP(cycIntensity)` `N` (`ExplRun.ofPPP`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic
namespace CycSchemeEnv
variable {I : Type*} [MeasurableSpace I] [Countable I] [MeasurableSingletonClass I] {d : ℕ} {β : ℝ}
  [Fact (0 < β)] {P : CycPlan I d β} {ν : Measure (I × RingSpace d β)} {sc : ℝ≥0∞}

open scoped Classical in
/-- `cycRec^𝒫(s_∘)` for the environment `ν`: `ρ^𝒫(ν)` if `s_∘ = ∞`, and `Trunc_{s_∘}(ρ^𝒫(ν))`
otherwise (The environment scheme (b)). -/
noncomputable def cycRecAt (P : CycPlan I d β) (ν : Measure (I × RingSpace d β)) (sc : ℝ≥0∞) :
    CycRec I d :=
  if sc = ⊤ then P.envFinal ν else CycRec.trunc sc.toNNReal (P.envFinal ν)

variable (T : Traj P sc ν) (junk : CycEntry I d)

theorem Traj.thetaZero_fin (hν : CycGood ν) (hK : 0 < P.K) (h0 : T.S 0 = CycScheme.init P) :
    () ∈ _root_.ElboimSly.Cyclic.thetaZero T.recSeq junk := fun _ hk => T.limGood' junk hν hK h0 hk

/-- The environment scheme (b), finite horizon: the entries of the limit of the records are
those of `Trunc_{s_∘}(ρ^𝒫(ν))`. -/
theorem Traj.recLim_nth_fin (hν : CycGood ν) (hK : 0 < P.K) (h0 : T.S 0 = CycScheme.init P)
    (hsc : sc ≠ ⊤) (k : ℕ) :
    (recLim junk (T.hext hν hK h0) ()).nth k =
      (CycRec.trunc sc.toNNReal (P.envFinal ν)).nth k := by
  classical
  have hth := T.thetaZero_fin junk hν hK h0
  have hnum := num_recLim (ρ := T.recSeq) junk (T.hext hν hK h0) ()
  rw [ite_eq_left hth] at hnum
  rw [trunc_envFinal_nth junk, ENNReal.coe_toNNReal hsc]
  by_cases hcl : P.Cont (rule P ν) k ∧ lam P ν k ≤ sc
  · rw [ite_eq_left hcl]
    have hk := (T.lt_numLim_iff_fin hν hK h0 k).2 hcl
    rw [ElboimSly.Cyclic.recLim_nth junk (T.hext hν hK h0) hth hk,
      T.limEntry_fin junk hν hK h0 hsc hcl.1 hcl.2]
  · rw [ite_eq_right hcl]
    rcases h : (recLim junk (T.hext hν hK h0) ()).nth k with _ | e
    · rfl
    · exfalso
      have := lt_num_of_nth h
      rw [hnum] at this
      exact hcl ((T.lt_numLim_iff_fin hν hK h0 k).1 this)

/-- The environment scheme (b), finite horizon: the limit of the records of the scheme is
`Trunc_{s_∘}(ρ^𝒫(ν))`. -/
theorem Traj.recLim_eq_trunc (hν : CycGood ν) (hK : 0 < P.K) (h0 : T.S 0 = CycScheme.init P)
    (hsc : sc ≠ ⊤) :
    recLim junk (T.hext hν hK h0) () = CycRec.trunc sc.toNNReal (P.envFinal ν) :=
  CycRec.ext_nth' fun k => T.recLim_nth_fin junk hν hK h0 hsc k

/-- The environment scheme (b), every horizon: the limit of the records is `cycRec^𝒫(s_∘)`. -/
theorem Traj.recLim_eq_cycRecAt (hν : CycGood ν) (hK : 0 < P.K) (h0 : T.S 0 = CycScheme.init P) :
    recLim junk (T.hext hν hK h0) () = cycRecAt P ν sc := by
  unfold cycRecAt
  by_cases hsc : sc = ⊤
  · rw [ite_eq_left hsc]; exact T.recLim_eq junk hν hK h0 hsc
  · rw [ite_eq_right hsc]; exact T.recLim_eq_trunc junk hν hK h0 hsc

variable {U : Type*} [MeasurableSpace U] {Ω : Type*} [MeasurableSpace Ω] {Pr : Measure Ω}
variable (run : ExplRun (cycScheme P sc U) Pr)

/-- The environment scheme (b), last sentence (every horizon): almost surely the records of
the scheme converge coordinatewise to `cycRec^𝒫(s_∘)`. -/
theorem ae_recLim_eq_cycRecAt (hK : 0 < P.K) :
    ∀ᵐ ω ∂Pr, recLim junk (hextΩ run hK) ω = cycRecAt P (run.N ω) sc := by
  filter_upwards [goodEv_ae run] with ω hω
  rw [recLim_point]
  have hseq : (fun j (_ : Unit) => recSeqΩ run j ω) = (trajOf run ω hω).recSeq := by
    funext j _
    classical
    unfold recSeqΩ
    rw [ite_eq_left hω]
    rfl
  rw [recLim_congr_seq hseq junk _ ((trajOf run ω hω).hext hω.1 hK rfl)]
  exact (trajOf run ω hω).recLim_eq_cycRecAt junk hω.1 hK rfl

/-- The environment scheme (b), finite horizon: almost surely the limit of the records is
`Trunc_{s_∘}(ρ^𝒫(N))`. -/
theorem ae_recLim_eq_trunc (hK : 0 < P.K) (hsc : sc ≠ ⊤) :
    ∀ᵐ ω ∂Pr, recLim junk (hextΩ run hK) ω =
      CycRec.trunc sc.toNNReal (P.envFinal (run.N ω)) := by
  filter_upwards [ae_recLim_eq_cycRecAt junk run hK] with ω h
  rw [h]; unfold cycRecAt; rw [ite_eq_right hsc]

/-- The environment scheme (b) (every horizon), for an arbitrary `PPP(cycIntensity)` `N`
with `u` independent of `N` (and `N'` an independent copy): almost surely the limit of the records
of the exploration of `N` is `cycRec^𝒫(s_∘)`. -/
theorem ae_recLim_eq_cycRecAt_ppp {u : Ω → U} (hu : Measurable u)
    {N N' : Ω → Measure (CycS I d β)} (hN : IsPoissonPointProcess N (cycIntensity I d β) Pr)
    (hind : IndepFun u N Pr) (hN' : IsPoissonPointProcess N' (cycIntensity I d β) Pr)
    (hind' : IndepFun N' (fun ω => (u ω, N ω)) Pr) (hK : 0 < P.K) :
    ∀ᵐ ω ∂Pr, recLim junk (hextΩ (ExplRun.ofPPP (cycScheme P sc U) hu hN hind hN' hind') hK) ω =
      cycRecAt P (N ω) sc := by
  filter_upwards [ae_recLim_eq_cycRecAt junk
    (ExplRun.ofPPP (cycScheme P sc U) hu hN hind hN' hind') hK, hN.tau_comp_ae_eq] with ω h1 h2
  rw [h1]
  exact congrArg (cycRecAt P · sc) h2

end CycSchemeEnv
end ElboimSly.Cyclic

end
