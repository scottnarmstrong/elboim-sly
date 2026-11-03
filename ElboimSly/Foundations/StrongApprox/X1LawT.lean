/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.StrongApprox.X1LawX
public import Mathlib

/-!
# The law of the clocks

Laws in the coupling (c) (Part II).

For each coordinate `k`, the clocks `τ^k_1, …, τ^k_ℓ` are i.i.d. with the mixture law
`κ̄_k = ∫ κ_{s_k} λ(ds)`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace ElboimSly.StrongApprox

open ElboimSly.Brownian

lemma lintegral_exitLaw {r : ℝ} {f : ℝ≥0∞ → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ t, f t ∂(exitLaw r) = ∫⁻ ω, f (bmExit r β₀ ω) ∂P₀ := by
  rw [← map_bmExit isStandardRealBM_β₀ r, lintegral_map hf (measurable_bmExit isStandardRealBM_β₀ r)]

lemma exitLaw_zero : exitLaw 0 = Measure.dirac 0 := by
  unfold exitLaw
  have : (fun w : C0 => exitTime 0 w.1) = fun _ => (0 : ℝ≥0∞) := by
    funext w; exact exitTime_of_nonpos (le_refl (0 : ℝ)) w.1
  rw [this, Measure.map_const, measure_univ, one_smul]

lemma exitLaw_top {r : ℝ} (hr : 0 ≤ r) : exitLaw r {⊤} = 0 := by
  rw [← map_bmExit isStandardRealBM_β₀ r, Measure.map_apply (measurable_bmExit isStandardRealBM_β₀ r)
    (measurableSet_singleton _)]
  have := bmExit_lt_top_ae_of_nonneg isStandardRealBM_β₀ hr
  rw [ae_iff] at this
  refine measure_mono_null ?_ this
  intro ω hω
  simp only [Set.mem_preimage, Set.mem_singleton_iff] at hω
  simp [hω]

lemma lintegral_exitLaw_id {r : ℝ} (hr : 0 ≤ r) :
    ∫⁻ t, t ∂(exitLaw r) = ENNReal.ofReal (r ^ 2) := by
  rcases hr.eq_or_lt with h | h
  · subst h
    rw [exitLaw_zero, lintegral_dirac]
    simp
  · have := lintegral_exitLaw (r := r) (f := fun t => t) measurable_id
    rw [this]
    exact lintegral_bmExit isStandardRealBM_β₀ h

lemma lintegral_exitLaw_exp {s M : ℝ} (hs : 0 ≤ s) (hsM : s ≤ M) (_hM : 1 ≤ M) :
    ∫⁻ t, ENNReal.ofReal (Real.exp (t.toReal / (36 * M ^ 2))) ∂(exitLaw s) ≤ 6 := by
  rcases hs.eq_or_lt with h | h
  · subst h
    rw [exitLaw_zero, lintegral_dirac' _ (by fun_prop)]
    simp
  · have hf : Measurable fun t : ℝ≥0∞ => ENNReal.ofReal (Real.exp (t.toReal / (36 * M ^ 2))) :=
      ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
        (ENNReal.measurable_toReal.div_const _))
    rw [lintegral_exitLaw hf]
    refine le_trans (lintegral_mono fun ω => ?_) (lintegral_exp_bmExit_le isStandardRealBM_β₀ h)
    refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
    have hM2 : s ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ hs hsM 2
    exact div_le_div_of_nonneg_left ENNReal.toReal_nonneg (by positivity) (by nlinarith)

section Mixture

variable {d : ℕ}

lemma measurable_exitLaw_coord (k : Fin d) : Measurable fun x : Fin d → ℝ => exitLaw (x k) :=
  Measure.measurable_of_measurable_coe _ fun _ hA =>
    (measurable_exitLaw hA).comp (measurable_pi_apply k)

/-- The mixture law `κ̄_k = ∫ κ_{s_k} λ(ds)` of a clock. -/
noncomputable def kbar (lam : Measure (Fin d → ℝ)) (k : Fin d) : Measure ℝ≥0∞ :=
  Measure.bind lam fun x => exitLaw (x k)

lemma kbar_apply (lam : Measure (Fin d → ℝ)) (k : Fin d) {A : Set ℝ≥0∞} (hA : MeasurableSet A) :
    kbar lam k A = ∫⁻ x, exitLaw (x k) A ∂lam :=
  Measure.bind_apply hA (measurable_exitLaw_coord k).aemeasurable

instance (lam : Measure (Fin d → ℝ)) [IsProbabilityMeasure lam] (k : Fin d) :
    IsProbabilityMeasure (kbar lam k) :=
  ⟨by rw [kbar_apply lam k MeasurableSet.univ]; simp⟩

variable (lam : Measure (Fin d → ℝ)) [IsProbabilityMeasure lam] (k : Fin d)

omit [IsProbabilityMeasure lam] in
lemma lintegral_kbar {f : ℝ≥0∞ → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ t, f t ∂(kbar lam k) = ∫⁻ x, ∫⁻ t, f t ∂(exitLaw (x k)) ∂lam :=
  Measure.lintegral_bind (measurable_exitLaw_coord k).aemeasurable hf.aemeasurable

omit [IsProbabilityMeasure lam] in
lemma kbar_top (hlam : ∀ᵐ x ∂lam, 0 ≤ x k) : kbar lam k {⊤} = 0 := by
  rw [kbar_apply lam k (measurableSet_singleton _)]
  have hm : Measurable fun x : Fin d → ℝ => exitLaw (x k) {⊤} :=
    (measurable_exitLaw (measurableSet_singleton _)).comp (measurable_pi_apply k)
  rw [lintegral_eq_zero_iff hm]
  filter_upwards [hlam] with x hx
  exact exitLaw_top hx

omit [IsProbabilityMeasure lam] in
lemma lintegral_kbar_id (hlam : ∀ᵐ x ∂lam, 0 ≤ x k) :
    ∫⁻ t, t ∂(kbar lam k) = ∫⁻ x, ENNReal.ofReal (x k ^ 2) ∂lam := by
  rw [lintegral_kbar lam k (f := fun t => t) measurable_id]
  exact lintegral_congr_ae (by filter_upwards [hlam] with x hx; exact lintegral_exitLaw_id hx)

lemma lintegral_kbar_exp {M : ℝ} (hM : 1 ≤ M) (hlam : ∀ᵐ x ∂lam, 0 ≤ x k ∧ x k ≤ M) :
    ∫⁻ t, ENNReal.ofReal (Real.exp (t.toReal / (36 * M ^ 2))) ∂(kbar lam k) ≤ 6 := by
  have hf : Measurable fun t : ℝ≥0∞ => ENNReal.ofReal (Real.exp (t.toReal / (36 * M ^ 2))) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      (ENNReal.measurable_toReal.div_const _))
  rw [lintegral_kbar lam k hf]
  calc _ ≤ ∫⁻ _x, (6 : ℝ≥0∞) ∂lam := by
        refine lintegral_mono_ae ?_
        filter_upwards [hlam] with x hx
        exact lintegral_exitLaw_exp hx.1 hx.2 hM
    _ = 6 := by simp

end Mixture

section Tvec

variable {d ℓ : ℕ}

/-- The clocks `(τ^k_i)_i` of coordinate `k`. -/
def Tp (k : Fin d) (v : Fin d → Fin ℓ → ℝ × ℝ≥0∞) : Fin ℓ → ℝ≥0∞ := fun i => (v k i).2

lemma measurable_Tp (k : Fin d) : Measurable (Tp (d := d) (ℓ := ℓ) k) :=
  measurable_pi_iff.2 fun i => measurable_snd.comp ((measurable_pi_apply i).comp
    (measurable_pi_apply k))

lemma Lr_map_Tp (r : Fin ℓ → Fin d → ℝ) (k : Fin d) :
    (Lr ℓ r).map (Tp k) = Measure.pi fun i : Fin ℓ => exitLaw (r i k) := by
  have hprob : ∀ (k : Fin d) (i : Fin ℓ),
      IsProbabilityMeasure ((symLaw (r i k)).prod (exitLaw (r i k))) := fun _ _ => inferInstance
  have hT : Tp k = (fun (w : Fin ℓ → ℝ × ℝ≥0∞) (i : Fin ℓ) => (w i).2) ∘
      (fun v : Fin d → Fin ℓ → ℝ × ℝ≥0∞ => v k) := rfl
  have hw : Measurable (fun (w : Fin ℓ → ℝ × ℝ≥0∞) (i : Fin ℓ) => (w i).2) :=
    measurable_pi_iff.2 fun i => measurable_snd.comp (measurable_pi_apply i)
  rw [hT, ← Measure.map_map hw (measurable_pi_apply k), Lr,
    (measurePreserving_eval (fun k : Fin d => Measure.pi fun i : Fin ℓ =>
      (symLaw (r i k)).prod (exitLaw (r i k))) k).map_eq]
  have := Measure.pi_map_pi (μ := fun i : Fin ℓ => (symLaw (r i k)).prod (exitLaw (r i k)))
    (f := fun _ (u : ℝ × ℝ≥0∞) => u.2) (fun i => measurable_snd.aemeasurable)
  refine this.trans ?_
  congr 1
  funext i
  simp [Measure.map_snd_prod]

variable (lam : Measure (Fin d → ℝ)) [IsProbabilityMeasure lam]

/-- Laws in the coupling (c): the clocks of coordinate `k` are i.i.d. with law `κ̄_k`. -/
theorem map_Tvec (hlam : ∀ᵐ x ∂lam, ∀ k, 0 ≤ x k) (k : Fin d) :
    (P1 d ℓ lam).map (fun ω => Tp k (Vfull ℓ ω)) = Measure.pi fun _ : Fin ℓ => kbar lam k := by
  have hTm : Measurable fun ω : Ω1 d ℓ => Tp k (Vfull ℓ ω) :=
    (measurable_Tp k).comp (measurable_Vfull d ℓ)
  refine (Measure.pi_eq fun s hs => ?_).symm
  have hB : MeasurableSet (Set.univ.pi s) := MeasurableSet.univ_pi hs
  rw [Measure.map_apply hTm hB, ← lintegral_indicator_one (hTm hB)]
  have hG : Measurable (Function.uncurry fun (_ : Fin ℓ → Fin d → ℝ)
      (v : Fin d → Fin ℓ → ℝ × ℝ≥0∞) => (Set.univ.pi s).indicator (1 : (Fin ℓ → ℝ≥0∞) → ℝ≥0∞)
        (Tp k v)) :=
    (measurable_one.indicator hB).comp ((measurable_Tp k).comp measurable_snd)
  have hcond := lintegral_cond hlam hG
  have e1 : ∀ ω : Ω1 d ℓ, ((fun ω => Tp k (Vfull ℓ ω)) ⁻¹' Set.univ.pi s).indicator
      (1 : Ω1 d ℓ → ℝ≥0∞) ω =
      (Set.univ.pi s).indicator (1 : (Fin ℓ → ℝ≥0∞) → ℝ≥0∞) (Tp k (Vfull ℓ ω)) := by
    intro ω
    by_cases h : Tp k (Vfull ℓ ω) ∈ Set.univ.pi s
    · rw [Set.indicator_of_mem (show ω ∈ (fun ω => Tp k (Vfull ℓ ω)) ⁻¹' Set.univ.pi s from h),
        Set.indicator_of_mem h]
      rfl
    · rw [Set.indicator_of_notMem
        (show ω ∉ (fun ω => Tp k (Vfull ℓ ω)) ⁻¹' Set.univ.pi s from h),
        Set.indicator_of_notMem h]
  simp_rw [e1]
  rw [hcond]
  have e2 : ∀ r : Fin ℓ → Fin d → ℝ, ∫⁻ v, (Set.univ.pi s).indicator 1 (Tp k v) ∂(Lr ℓ r) =
      ∏ i, exitLaw (r i k) (s i) := by
    intro r
    rw [← lintegral_map (measurable_one.indicator hB) (measurable_Tp k), Lr_map_Tp,
      lintegral_indicator_one hB, Measure.pi_pi]
  simp_rw [e2]
  rw [PR, lintegral_pi_prod lam (fun i x => exitLaw (x k) (s i))
    (fun i => (measurable_exitLaw (hs i)).comp (measurable_pi_apply k))]
  exact Finset.prod_congr rfl fun i _ => (kbar_apply lam k (hs i)).symm

end Tvec

end ElboimSly.StrongApprox
