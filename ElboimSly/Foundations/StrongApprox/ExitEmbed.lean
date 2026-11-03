/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.StrongApprox.ExitLaw
public import Mathlib

/-!
# Skorokhod embedding of a weighted Rademacher walk

Skorokhod embedding of a weighted Rademacher walk (Part II).

For a standard real Brownian motion `β` and moduli `r 0, …, r (ℓ-1) ≥ 0`, the iterated embedding
`((X_i, τ_i))_{i < ℓ}` of `r` in `β` has the product law `⨂ᵢ (ρ_{rᵢ} ⊗ κ_{rᵢ})`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace ElboimSly.StrongApprox

open ElboimSly.Brownian

/-- The `i`-th pair `(X_i, τ_i)` of the iterated embedding (0-indexed). -/
noncomputable def embPair (r : ℕ → ℝ) (w : ℝ≥0 → ℝ) (i : ℕ) : ℝ × ℝ≥0∞ :=
  (embX r w i, embTau r w i)

/-- The first `ℓ` pairs of the iterated embedding. -/
noncomputable def embVec (ℓ : ℕ) (r : ℕ → ℝ) (w : ℝ≥0 → ℝ) : Fin ℓ → ℝ × ℝ≥0∞ :=
  fun i => embPair r w i

lemma embPath_succ_shift (r : ℕ → ℝ) (w : ℝ≥0 → ℝ) (i : ℕ) :
    embPath r w (i + 1) =
      embPath (fun k => r (k + 1)) (shiftAt (exitTime (r 0) w) w) i := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [embPath_succ, embTau, ih]
    rfl

lemma embPair_succ (r : ℕ → ℝ) (w : ℝ≥0 → ℝ) (i : ℕ) :
    embPair r w (i + 1) =
      embPair (fun k => r (k + 1)) (shiftAt (exitTime (r 0) w) w) i := by
  simp only [embPair, embX, embTau, embPath_succ_shift]

lemma embVec_succ (ℓ : ℕ) (r : ℕ → ℝ) (w : ℝ≥0 → ℝ) :
    embVec (ℓ + 1) r w =
      Fin.cons (exitPair (r 0) w)
        (embVec ℓ (fun k => r (k + 1)) (shiftAt (exitTime (r 0) w) w)) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · simp only [embVec, Fin.cons_succ, Fin.val_succ]
    exact embPair_succ r w j

lemma measurable_embVecC0 (ℓ : ℕ) (r : ℕ → ℝ) : Measurable fun w : C0 => embVec ℓ r w.1 := by
  refine measurable_pi_iff.2 fun i => ?_
  exact (measurable_embX (ρs := fun k _ => r k) isProcess_coordC0 (fun _ => measurable_const)
    i).prodMk (measurable_embTau (ρs := fun k _ => r k) isProcess_coordC0
    (fun _ => measurable_const) i)

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

lemma bmExit_lt_top_ae_of_nonneg [IsProbabilityMeasure P] {β : ℝ≥0 → Ω → ℝ}
    (hβ : IsStandardRealBM β P) {r : ℝ} (hr : 0 ≤ r) : ∀ᵐ ω ∂P, bmExit r β ω < ⊤ := by
  rcases hr.eq_or_lt with h | h
  · subst h
    refine Filter.Eventually.of_forall fun ω => ?_
    show exitTime 0 (fun t => β t ω) < ⊤
    rw [exitTime_of_nonpos (le_refl (0 : ℝ))]; exact ENNReal.zero_lt_top
  · exact bmExit_lt_top_ae hβ h

omit mΩ in
lemma measurable_endVal_aux {m : MeasurableSpace Ω} {τ : Ω → ℝ≥0∞} {Z : ℝ≥0 → Ω → ℝ}
    (hτ : Measurable[m] τ) (hZ : Measurable[m] fun ω => Z (τ ω).toNNReal ω) :
    Measurable[m] fun ω => endVal (τ ω) (fun t => Z t ω) := by
  have : (fun ω => endVal (τ ω) (fun t => Z t ω)) =
      fun ω => if τ ω = ⊤ then 0 else Z (τ ω).toNNReal ω := rfl
  rw [this]
  exact Measurable.ite (hτ (measurableSet_singleton ⊤)) measurable_const hZ

/-- Skorokhod embedding of a weighted Rademacher walk. -/
theorem map_embVec [IsProbabilityMeasure P] (ℓ : ℕ) (r : ℕ → ℝ) (hr : ∀ i, 0 ≤ r i)
    {β : ℝ≥0 → Ω → ℝ} (hβ : IsStandardRealBM β P) :
    P.map (fun ω => embVec ℓ r (fun t => β t ω)) =
      Measure.pi fun i : Fin ℓ => (symLaw (r i)).prod (exitLaw (r i)) := by
  induction ℓ generalizing r β with
  | zero =>
    refine Measure.ext fun s hs => ?_
    rcases s.eq_empty_or_nonempty with rfl | hne
    · simp
    · rw [Subsingleton.eq_univ_of_nonempty hne]
      rw [Measure.map_apply (measurable_of_subsingleton_codomain _) MeasurableSet.univ]
      simp
  | succ ℓ ih =>
    have hproc := isProcess_of_realBM hβ
    have hF : ∀ t, realFiltration β t ≤ mΩ := realFiltration_le hproc.2
    have hstop := bmExit_stopping hβ (r 0)
    have hfin := bmExit_lt_top_ae_of_nonneg hβ (hr 0)
    set β1 : ℝ≥0 → Ω → ℝ := procShift (bmExit (r 0) β) β with hβ1def
    have hβ1 : IsStandardRealBM β1 P := isStandardRealBM_procShift hβ hstop hfin
    have hproc1 := isProcess_of_realBM hβ1
    have hind := indep_stopped_procShift hβ hstop hfin
    set A : Ω → ℝ × ℝ≥0∞ := fun ω => exitPair (r 0) (fun t => β t ω) with hA
    set B : Ω → (Fin ℓ → ℝ × ℝ≥0∞) :=
      fun ω => embVec ℓ (fun k => r (k + 1)) (fun t => β1 t ω) with hB
    have hAm : Measurable[stoppedSigma (realFiltration β) (bmExit (r 0) β) hstop] A := by
      have h1 := measurable_self_stopped hF hstop
      have h2 := measurable_endVal_aux (Z := β) h1 (measurable_value_stopped hproc hstop)
      exact h2.prodMk h1
    have hcomap : MeasurableSpace.comap (pathC0 hproc1) inferInstance =
        MeasurableSpace.comap (fun ω s => β1 s ω) inferInstance :=
      MeasurableSpace.comap_comp (f := Subtype.val) (g := pathC0 hproc1)
    have hBm : Measurable[MeasurableSpace.comap (fun ω s => β1 s ω) inferInstance] B := by
      rw [← hcomap]
      exact (measurable_embVecC0 ℓ (fun k => r (k + 1))).comp (comap_measurable _)
    have hindep : IndepFun A B P := by
      show Indep (MeasurableSpace.comap A inferInstance) (MeasurableSpace.comap B inferInstance) P
      exact indep_of_indep_of_le_left (indep_of_indep_of_le_right hind hBm.comap_le) hAm.comap_le
    have hAmeas : Measurable A := hAm.mono stoppedSigma_le le_rfl
    have hBmeas : Measurable B := hBm.mono (by
      intro S hS
      obtain ⟨T, hT, rfl⟩ := hS
      exact (measurable_pi_iff.2 hproc1.2) hT) le_rfl
    have hlawA : P.map A = (symLaw (r 0)).prod (exitLaw (r 0)) :=
      map_exitPair_eq_of_nonneg hβ (hr 0)
    have hlawB : P.map B = Measure.pi fun i : Fin ℓ =>
        (symLaw (r (i + 1))).prod (exitLaw (r (i + 1))) :=
      ih (fun k => r (k + 1)) (fun k => hr _) hβ1
    have hpair := (indepFun_iff_map_prod_eq_prod_map_map hAmeas.aemeasurable
      hBmeas.aemeasurable).1 hindep
    set μ : Fin (ℓ + 1) → Measure (ℝ × ℝ≥0∞) :=
      fun i => (symLaw (r i)).prod (exitLaw (r i)) with hμ
    have : ∀ i, SigmaFinite (μ i) := fun i => by infer_instance
    have hmp := (measurePreserving_piFinSuccAbove (α := fun _ : Fin (ℓ + 1) => ℝ × ℝ≥0∞) μ 0).symm
    have e : (fun ω => embVec (ℓ + 1) r (fun t => β t ω)) =
        (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (ℓ + 1) => ℝ × ℝ≥0∞) 0).symm ∘
          fun ω => (A ω, B ω) := by
      funext ω
      rw [embVec_succ]
      simp [hA, hB, hβ1def, procShift]
      rfl
    rw [e, ← Measure.map_map (MeasurableEquiv.measurable _) (hAmeas.prodMk hBmeas), hpair, hlawA,
      hlawB]
    convert hmp.map_eq using 2
    simp [hμ]

end ElboimSly.StrongApprox
