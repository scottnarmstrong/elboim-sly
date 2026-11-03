/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Brownian.Markov
public import ElboimSly.Foundations.Brownian.Invariance
public import ElboimSly.Foundations.Brownian.Measurability
public import Mathlib

/-!
# Unit increments of Brownian motion

Laws in the coupling (b) (Part II).

The unit increments `B(i+1) - B(i)`, `i < ℓ`, of a standard `d`-dimensional Brownian motion are
i.i.d. with law `N_d(0, I)`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace ElboimSly.StrongApprox

open ElboimSly.Brownian

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {d : ℕ}

/-- The unit increments of a process. -/
def unitIncr (B : ℝ≥0 → Ω → (Fin d → ℝ)) (ℓ : ℕ) (ω : Ω) : Fin ℓ → Fin d → ℝ :=
  fun i => B ((i : ℕ) + 1) ω - B (i : ℕ) ω

omit mΩ in
lemma unitIncr_succ (B : ℝ≥0 → Ω → (Fin d → ℝ)) (ℓ : ℕ) (ω : Ω) :
    unitIncr B (ℓ + 1) ω =
      Fin.cons (B 1 ω - B 0 ω) (unitIncr (fun t ω => B (1 + t) ω - B 1 ω) ℓ ω) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [unitIncr]
  · simp only [unitIncr, Fin.cons_succ, Fin.val_succ]
    have e1 : (((j : ℕ) + 1 : ℕ) : ℝ≥0) = 1 + (j : ℕ) := by push_cast; ring
    have e2 : (((j : ℕ) + 1 : ℕ) : ℝ≥0) + 1 = 1 + ((j : ℕ) + 1) := by push_cast; ring
    rw [e2, e1]
    ext k
    simp

/-- Laws in the coupling (b). -/
theorem map_unitIncr [IsProbabilityMeasure P] (ℓ : ℕ) :
    ∀ {B : ℝ≥0 → Ω → (Fin d → ℝ)}, IsStandardBrownianMotion d B P →
      P.map (unitIncr B ℓ) = Measure.pi fun _ : Fin ℓ => Measure.pi fun _ : Fin d => gaussianReal 0 1 := by
  induction ℓ with
  | zero =>
    intro B hB
    refine Measure.ext fun s hs => ?_
    rcases s.eq_empty_or_nonempty with rfl | hne
    · simp
    · rw [Subsingleton.eq_univ_of_nonempty hne]
      rw [Measure.map_apply (measurable_of_subsingleton_codomain _) MeasurableSet.univ]
      simp
  | succ ℓ ih =>
    intro B hB
    set B1 : ℝ≥0 → Ω → (Fin d → ℝ) := fun t ω => B (1 + t) ω - B 1 ω with hB1
    have hBsh : IsStandardBrownianMotion d B1 P := hB.shift 1
    set A : Ω → Fin d → ℝ := fun ω => B 1 ω - B 0 ω with hA
    set C : Ω → Fin ℓ → Fin d → ℝ := unitIncr B1 ℓ with hC
    have hAm' : Measurable[bmFiltration B 1] A :=
      (measurable_bmFiltration le_rfl).sub (measurable_bmFiltration (show (0 : ℝ≥0) ≤ 1 from zero_le_one))
    have hAm : Measurable A := (hB.measurable 1).sub (hB.measurable 0)
    have hCm : Measurable C := measurable_pi_iff.2 fun i =>
      (hBsh.measurable _).sub (hBsh.measurable _)
    have hCF : C = (fun (w : ElboimSly.Brownian.PathSpace d) (i : Fin ℓ) => w ((i : ℕ) + 1) - w (i : ℕ)) ∘
        shiftPath B 1 := rfl
    have hFm : Measurable (fun (w : ElboimSly.Brownian.PathSpace d) (i : Fin ℓ) => w ((i : ℕ) + 1) - w (i : ℕ)) :=
      measurable_pi_iff.2 fun i => (measurable_pi_apply _).sub (measurable_pi_apply _)
    have hindep : IndepFun A C P := by
      show Indep (MeasurableSpace.comap A inferInstance) (MeasurableSpace.comap C inferInstance) P
      have hind := (hB.indep_shift 1).symm
      refine indep_of_indep_of_le_right (indep_of_indep_of_le_left hind hAm'.comap_le) ?_
      rw [hCF, ← MeasurableSpace.comap_comp]
      exact MeasurableSpace.comap_mono hFm.comap_le
    have hlawA : P.map A = Measure.pi fun _ : Fin d => gaussianReal 0 1 := by
      have := (hB.hasLaw_increment (show (0 : ℝ≥0) ≤ 1 from zero_le_one)).map_eq
      simpa using this
    have hlawC : P.map C = Measure.pi fun _ : Fin ℓ => Measure.pi fun _ : Fin d =>
        gaussianReal 0 1 := ih hBsh
    have hpair := (indepFun_iff_map_prod_eq_prod_map_map hAm.aemeasurable hCm.aemeasurable).1
      hindep
    set μ : Fin (ℓ + 1) → Measure (Fin d → ℝ) := fun _ => Measure.pi fun _ : Fin d =>
      gaussianReal 0 1 with hμ
    have : ∀ i, SigmaFinite (μ i) := fun i => by infer_instance
    have hmp := (measurePreserving_piFinSuccAbove (α := fun _ : Fin (ℓ + 1) => Fin d → ℝ) μ 0).symm
    have e : unitIncr B (ℓ + 1) =
        (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (ℓ + 1) => Fin d → ℝ) 0).symm ∘
          fun ω => (A ω, C ω) := by
      funext ω
      rw [unitIncr_succ]
      simp [hA, hC, hB1]
      rfl
    rw [e, ← Measure.map_map (MeasurableEquiv.measurable _) (hAm.prodMk hCm), hpair, hlawA, hlawC]
    exact hmp.map_eq

end ElboimSly.StrongApprox
