/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycSchemeDrvKernelEq
public import ElboimSly.Foundations.PPP.Exploration.SegmentReal
public import ElboimSly.Foundations.PPP.Exploration.ThmStop
public import ElboimSly.Foundations.PPP.Exploration.ThmLawInf
public import Mathlib

/-!
# The driving scheme (d): equality in law of the two explorations

The driving scheme (d). For the driving exploration `H'` and the environment exploration
`H`, `Law(Ψ_∞(H'_∞)) = Law(H_∞)`, where `Ψ_∞(H'_∞) := (u', (ψ_{H'_j}(o'_j))_j)`.

* `drvPsiInf`: the map `Ψ_∞` on `ℋ'_∞`;
* `truncHist_drvPsiInf`: `π_k ∘ Ψ_∞ = Ψ_k ∘ π_k`;
* `drvScheme_law_Hinf`: the law identity, by sequential first-point exploration (d′) and part (b).
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

open SRW

variable {I : Type*} [MeasurableSpace I] [Countable I] [MeasurableSingletonClass I] {d : ℕ}
  {β : ℝ} [Fact (0 < β)]
  {J : Type*} [MeasurableSpace J] [Countable J] [MeasurableSingletonClass J]
  {jx : ∀ k : ℕ, CycRecN I d k → J} (j0 : J) (P : CycPlan I d β) (sc : ℝ≥0∞)
  {U : Type*} [MeasurableSpace U]

/-- The map `Ψ_∞ : ℋ'_∞ → ℋ_∞`, `(u, (o'_j)_j) ↦ (u, (ψ_{π_j}(o'_j))_j)`. -/
noncomputable def drvPsiInf (y : U × (ℕ → Outcome (DrvS d J))) :
    U × (ℕ → Outcome (CycS I d β)) :=
  (y.1, fun j => drvPsiOut (jx := jx) (β := β) j0 P sc
    (CycScheme.stateAt P sc j (drvPsi jx j0 P sc U j (truncHist j y))) (y.2 j))

theorem truncHist_drvPsiInf (k : ℕ) (y : U × (ℕ → Outcome (DrvS d J))) :
    truncHist k (drvPsiInf (jx := jx) (β := β) j0 P sc y) = drvPsi jx j0 P sc U k (truncHist k y) := by
  induction k with
  | zero => exact Prod.ext rfl (funext fun i => i.elim0)
  | succ k ih =>
    show _ = ((drvPsi jx j0 P sc U k (truncHist (k + 1) y).init).snoc
      (drvPsiOut (jx := jx) (β := β) j0 P sc
        (CycScheme.stateAt P sc k (drvPsi jx j0 P sc U k (truncHist (k + 1) y).init))
        (truncHist (k + 1) y).last))
    have e1 : (truncHist (k + 1) y).init = truncHist k y := rfl
    have e2 : (truncHist (k + 1) y).last = y.2 k := rfl
    rw [e1, e2]
    have hfst := congrArg Prod.fst ih
    refine Prod.ext hfst ?_
    funext i
    refine Fin.lastCases ?_ (fun i => ?_) i
    · simp only [Hist.snoc, truncHist, drvPsiInf, Fin.snoc_last]
      rfl
    · have h2 := congrFun (congrArg Prod.snd ih) i
      simp only [Hist.snoc, Fin.snoc_castSucc]
      rw [← h2]
      rfl

theorem measurable_drvPsiInf (hj : ∀ k, Measurable (jx k)) :
    Measurable (drvPsiInf (jx := jx) (β := β) (U := U) (d := d) (J := J) j0 P sc) := by
  refine measurable_fst.prodMk (measurable_pi_iff.2 fun j => ?_)
  exact (measurable_drvPsiOut j0 P sc hj).comp
    ((((CycScheme.measurable_stateAt P sc j).comp
      ((measurable_drvPsi j0 P sc U hj j).comp (measurable_truncHist j)))).prodMk
        ((measurable_pi_apply j).comp measurable_snd))

variable (hj : ∀ k, Measurable (jx k))

/-- The driving scheme (d): `Law(Ψ_∞(H'_∞)) = Law(H_∞)`, for the driving exploration
`run'` and the environment exploration `run` (with the same law of the auxiliary variable). -/
theorem drvScheme_law_Hinf {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {Pe : Measure Ω} {Pd : Measure Ω'}
    (run : ExplRun (cycScheme P sc U) Pe) (run' : ExplRun (drvScheme j0 P sc U hj) Pd)
    (hu : Pd.map run'.u = Pe.map run.u) :
    Pd.map (fun ω => drvPsiInf (jx := jx) (β := β) j0 P sc (run'.Hinf ω)) =
      Pe.map run.Hinf := by
  classical
  have := run'.prob
  have hH : ∀ k ω, truncHist k (run'.Hinf ω) = run'.H k ω := fun k ω =>
    (drvScheme j0 P sc U hj).truncHist_Hinf k (run'.X ω)
  have hu' : ∀ ω, (run'.Hinf ω).1 = run'.u ω := fun ω => rfl
  have hΨ : ∀ k ω, (((drvPsiInf (jx := jx) (β := β) j0 P sc (run'.Hinf ω)).1,
      fun i : Fin k => (drvPsiInf (jx := jx) (β := β) j0 P sc (run'.Hinf ω)).2 i) :
        Hist U (CycS I d β) k) = drvPsi jx j0 P sc U k (run'.H k ω) := fun k ω => by
    rw [← hH]; exact truncHist_drvPsiInf j0 P sc k _
  have hmΨ := measurable_drvPsiInf (U := U) (β := β) (jx := jx) j0 P sc hj
  have hmH := run'.measurable_Hinf
  refine run.law_Hinf_of_kernel (P₂ := Pd)
    (u₂ := fun ω => (drvPsiInf (jx := jx) (β := β) j0 P sc (run'.Hinf ω)).1)
    (O₂ := fun j ω => (drvPsiInf (jx := jx) (β := β) j0 P sc (run'.Hinf ω)).2 j) ?_ ?_ ?_ ?_
  · exact measurable_fst.comp (hmΨ.comp hmH)
  · exact fun j => (measurable_pi_apply j).comp (measurable_snd.comp (hmΨ.comp hmH))
  · exact hu
  · intro k g hg
    have e1 : ∀ ω, ((drvPsiInf (jx := jx) (β := β) j0 P sc (run'.Hinf ω)).1,
        fun i : Fin (k + 1) => (drvPsiInf (jx := jx) (β := β) j0 P sc (run'.Hinf ω)).2 i) =
        drvPsi jx j0 P sc U (k + 1) (run'.H (k + 1) ω) := hΨ (k + 1)
    have e0 : ∀ ω, ((drvPsiInf (jx := jx) (β := β) j0 P sc (run'.Hinf ω)).1,
        fun i : Fin k => (drvPsiInf (jx := jx) (β := β) j0 P sc (run'.Hinf ω)).2 i) =
        drvPsi jx j0 P sc U k (run'.H k ω) := hΨ k
    simp only [e1, e0]
    have hgΨ : Measurable fun η => g (drvPsi jx j0 P sc U (k + 1) η) :=
      hg.comp (measurable_drvPsi j0 P sc U hj (k + 1))
    rw [show (∫⁻ ω, g (drvPsi jx j0 P sc U (k + 1) (run'.H (k + 1) ω)) ∂Pd) = _ from
      run'.stepLaw hgΨ]
    refine lintegral_congr fun ω => ?_
    set η := run'.H k ω with hη
    have hψ := measurable_drvPsiOut_const (β := β) j0 P sc hj
      (CycScheme.stateAt P sc k (drvPsi jx j0 P sc U k η))
    have hgs : Measurable fun o : Outcome (CycS I d β) =>
        g ((drvPsi jx j0 P sc U k η).snoc o) :=
      hg.comp ((Hist.measurable_snoc k).comp (measurable_const.prodMk measurable_id))
    have key : ∀ o', drvPsi jx j0 P sc U (k + 1) (η.snoc o') =
        (drvPsi jx j0 P sc U k η).snoc (drvPsiOut (jx := jx) (β := β) j0 P sc
          (CycScheme.stateAt P sc k (drvPsi jx j0 P sc U k η)) o') := fun o' => by
      show ((drvPsi jx j0 P sc U k (η.snoc o').init).snoc _) = _
      simp [Hist.init_snoc, Hist.last_snoc]
    simp only [key]
    rw [← drvScheme_kernel j0 P sc U hj k η, lintegral_map hgs hψ]

end ElboimSly.Cyclic

end
