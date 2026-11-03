/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.StrongApprox.CanonLaw
public import ElboimSly.Foundations.StrongApprox.SymLaw
public import ElboimSly.Foundations.StrongApprox.ExitMean
public import Mathlib

/-!
# The law of the first exit pair

Exit times of Brownian motion from symmetric intervals (b), (e) and measurability of the embedding (e)
(Part II).

`exitLaw r` is the law of the exit time of Brownian motion from `(-r, r)`; it is the same for every
standard real Brownian motion. The pair `(X, τ)` (exit position and time) has law
`symLaw r ⊗ exitLaw r`, and `r ↦ exitLaw r A` is Borel.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace ElboimSly.StrongApprox

open ElboimSly.Brownian

/-- The law `κ_r` of the exit time from `(-r, r)`. -/
noncomputable def exitLaw (r : ℝ) : Measure ℝ≥0∞ := wienerC0.map (fun w : C0 => exitTime r w.1)

/-- The exit pair `(w(τ), τ)` of a path. -/
noncomputable def exitPair (r : ℝ) (w : ℝ≥0 → ℝ) : ℝ × ℝ≥0∞ :=
  (endVal (exitTime r w) w, exitTime r w)

lemma measurable_exitTimeC0 (r : ℝ) : Measurable fun w : C0 => exitTime r w.1 :=
  measurable_procExit (ρ := fun _ => r) isProcess_coordC0 measurable_const

lemma measurable_exitPairC0 (r : ℝ) : Measurable fun w : C0 => exitPair r w.1 :=
  (measurable_procEnd (τ := fun w : C0 => exitTime r w.1) isProcess_coordC0
    (measurable_exitTimeC0 r)).prodMk (measurable_exitTimeC0 r)

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {β : ℝ≥0 → Ω → ℝ}

lemma map_comp_pathC0 [IsProbabilityMeasure P] (hβ : IsStandardRealBM β P) {γ : Type*}
    [MeasurableSpace γ] {F : C0 → γ} (hF : Measurable F) :
    P.map (fun ω => F (pathC0 (isProcess_of_realBM hβ) ω)) = wienerC0.map F := by
  rw [← map_pathC0 hβ, Measure.map_map hF (measurable_pathC0 _)]
  rfl

lemma map_bmExit [IsProbabilityMeasure P] (hβ : IsStandardRealBM β P) (r : ℝ) :
    P.map (bmExit r β) = exitLaw r :=
  map_comp_pathC0 hβ (F := fun w : C0 => exitTime r w.1) (measurable_exitTimeC0 r)

lemma map_exitPair [IsProbabilityMeasure P] (hβ : IsStandardRealBM β P) (r : ℝ) :
    P.map (fun ω => exitPair r (fun t => β t ω)) = wienerC0.map (fun w : C0 => exitPair r w.1) :=
  map_comp_pathC0 hβ (F := fun w : C0 => exitPair r w.1) (measurable_exitPairC0 r)

lemma measurable_exitPair [IsProbabilityMeasure P] (hβ : IsStandardRealBM β P) (r : ℝ) :
    Measurable fun ω => exitPair r (fun t => β t ω) :=
  (measurable_exitPairC0 r).comp (measurable_pathC0 (isProcess_of_realBM hβ))

instance (r : ℝ) : IsProbabilityMeasure (exitLaw r) := by
  unfold exitLaw
  exact (Measure.isProbabilityMeasure_map_iff (measurable_exitTimeC0 r).aemeasurable).2
    inferInstance

/-- The exit pair of the reflected path. -/
lemma exitPair_neg (r : ℝ) (w : ℝ≥0 → ℝ) :
    exitPair r (fun s => -w s) = (-(exitPair r w).1, (exitPair r w).2) := by
  simp [exitPair, exitTime_neg, endVal_neg]

/-- Exit times of Brownian motion from symmetric intervals (b): the exit pair has law `ρ_r ⊗ κ_r`. -/
theorem map_exitPair_eq [IsProbabilityMeasure P] (hβ : IsStandardRealBM β P) {r : ℝ}
    (hr : 0 < r) :
    P.map (fun ω => exitPair r (fun t => β t ω)) = (symLaw r).prod (exitLaw r) := by
  set ν := P.map (fun ω => exitPair r (fun t => β t ω)) with hν
  have : IsProbabilityMeasure ν :=
    (Measure.isProbabilityMeasure_map_iff (measurable_exitPair hβ r).aemeasurable).2 inferInstance
  have hmeas := measurable_exitPair hβ r
  -- support
  have hsupp : ∀ᵐ p ∂ν, p.1 = r ∨ p.1 = -r := by
    rw [hν, ae_map_iff hmeas.aemeasurable (by
      exact (measurableSet_eq_fun measurable_fst measurable_const).union
        (measurableSet_eq_fun measurable_fst measurable_const))]
    filter_upwards [bmExit_lt_top_ae hβ hr] with ω hω
    exact (abs_eq hr.le).1 (abs_endVal_exitTime ((isProcess_of_realBM hβ).1 ω) hr.le hω)
  have hsymm : ν.map (fun p : ℝ × ℝ≥0∞ => (-p.1, p.2)) = ν := by
    have hneg : Measurable (fun p : ℝ × ℝ≥0∞ => (-p.1, p.2)) :=
      (measurable_fst.neg).prodMk measurable_snd
    rw [hν, Measure.map_map hneg hmeas]
    have e : ((fun p : ℝ × ℝ≥0∞ => (-p.1, p.2)) ∘ fun ω => exitPair r (fun t => β t ω)) =
        fun ω => exitPair r (fun t => (fun t ω => -β t ω) t ω) := by
      funext ω; exact (exitPair_neg r (fun t => β t ω)).symm
    rw [e, map_exitPair hβ.neg r, map_exitPair hβ r]
  have hsnd : ν.map Prod.snd = exitLaw r := by
    rw [hν, Measure.map_map measurable_snd hmeas]
    exact map_bmExit hβ r
  have key := measure_prod_eq_of_symm ν hr hsupp hsymm
  rw [hsnd] at key
  exact key

/-- The case `r = 0` of `map_exitPair_eq`. -/
theorem map_exitPair_zero [IsProbabilityMeasure P] (hβ : IsStandardRealBM β P) :
    P.map (fun ω => exitPair 0 (fun t => β t ω)) = (symLaw 0).prod (exitLaw 0) := by
  have hproc := isProcess_of_realBM hβ
  have h1 : (fun ω => exitPair 0 (fun t => β t ω)) = fun _ => ((0 : ℝ), (0 : ℝ≥0∞)) := by
    funext ω
    have hτ := exitTime_of_nonpos (le_refl (0 : ℝ)) (fun t => β t ω)
    simp [exitPair, hτ, endVal, (hproc.1 ω).2]
  have h2 : exitLaw 0 = Measure.dirac 0 := by
    unfold exitLaw
    have : (fun w : C0 => exitTime 0 w.1) = fun _ => (0 : ℝ≥0∞) := by
      funext w; exact exitTime_of_nonpos (le_refl (0 : ℝ)) w.1
    rw [this, Measure.map_const, measure_univ, one_smul]
  have h3 : symLaw 0 = Measure.dirac 0 := by
    simp only [symLaw, neg_zero]
    rw [← two_smul ℝ≥0∞, smul_smul, ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_smul]
  rw [h1, Measure.map_const, measure_univ, one_smul, h2, h3, Measure.dirac_prod_dirac]

/-- Exit times of Brownian motion from symmetric intervals (b), all `r ≥ 0`. -/
theorem map_exitPair_eq_of_nonneg [IsProbabilityMeasure P] (hβ : IsStandardRealBM β P) {r : ℝ}
    (hr : 0 ≤ r) :
    P.map (fun ω => exitPair r (fun t => β t ω)) = (symLaw r).prod (exitLaw r) := by
  rcases hr.eq_or_lt with h | h
  · subst h; exact map_exitPair_zero hβ
  · exact map_exitPair_eq hβ h

/-- Exit times of Brownian motion from symmetric intervals (e): `r ↦ κ_r(A)` is Borel. -/
theorem measurable_exitLaw {A : Set ℝ≥0∞} (hA : MeasurableSet A) :
    Measurable fun r : ℝ => exitLaw r A := by
  have hp := isProcess_of_realBM isStandardRealBM_β₀
  have hZ : IsProcess (fun (t : ℝ≥0) (p : ℝ × Ω₀) => β₀ t p.2) :=
    ⟨fun p => hp.1 p.2, fun t => (hp.2 t).comp measurable_snd⟩
  have hT : Measurable (procExit (fun p : ℝ × Ω₀ => p.1) (fun t p => β₀ t p.2)) :=
    measurable_procExit hZ measurable_fst
  have := measurable_measure_prodMk_left (ν := P₀) (hT hA)
  convert this using 1
  funext r
  rw [← map_bmExit isStandardRealBM_β₀ r, Measure.map_apply (measurable_bmExit isStandardRealBM_β₀ r) hA]
  rfl

end ElboimSly.StrongApprox
