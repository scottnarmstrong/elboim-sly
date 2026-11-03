/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.StrongApprox.X1Cond
public import Mathlib

/-!
# The law of the embedded vectors

Laws in the coupling (a) (Part II).

In the coupling space, the vectors `X_i = (X^k_i)_k` are i.i.d. with law `μ`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace ElboimSly.StrongApprox

open ElboimSly.Brownian

/-- The integral of a product of functions of independent coordinates. -/
lemma lintegral_pi_prod {ι S : Type*} [Fintype ι] [MeasurableSpace S] (lam : Measure S)
    [IsProbabilityMeasure lam] (f : ι → S → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    ∫⁻ r, ∏ i, f i (r i) ∂(Measure.pi fun _ : ι => lam) = ∏ i, ∫⁻ x, f i x ∂lam := by
  have hind := iIndepFun_pi (μ := fun _ : ι => lam) (X := f) (fun i => (hf i).aemeasurable)
  have h := lintegral_prod_eq_prod_lintegral_of_indepFun (μ := Measure.pi fun _ : ι => lam) Finset.univ
    (fun (i : ι) (r : ι → S) => f i (r i)) hind
    (fun i => (hf i).comp (measurable_pi_apply i))
  refine h.trans ?_
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← (measurePreserving_eval (fun _ : ι => lam) i).map_eq]
  rw [lintegral_map (hf i) (measurable_pi_apply i)]
  rw [(measurePreserving_eval (fun _ : ι => lam) i).map_eq]

lemma symLaw_eq_map (r : ℝ) : symLaw r = signLaw.map (fun t => r * t) := by
  have hm : Measurable (fun t : ℝ => r * t) := measurable_const.mul measurable_id
  unfold symLaw signLaw
  rw [Measure.map_smul, Measure.map_add _ _ hm]
  simp only [Measure.map_dirac' hm]
  · simp
  · exact hm.aemeasurable

lemma pi_symLaw {d : ℕ} (x : Fin d → ℝ) :
    Measure.pi (fun k => symLaw (x k)) = (signsLaw d).map (fun ε => x * ε) := by
  unfold signsLaw
  have := Measure.pi_map_pi (μ := fun _ : Fin d => signLaw) (f := fun k (t : ℝ) => x k * t)
    (fun k => (measurable_const.mul measurable_id).aemeasurable)
  simp only [← symLaw_eq_map] at this
  exact this.symm

variable {d : ℕ}

/-- The sign decomposition as a mixture of product two-point laws. -/
lemma mixture_symLaw (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ]
    (hsym : ∀ ε : Fin d → ℝ, (∀ k, ε k = 1 ∨ ε k = -1) → μ.map (fun x => ε * x) = μ)
    {A : Set (Fin d → ℝ)} (hA : MeasurableSet A) :
    ∫⁻ x, (Measure.pi fun k => symLaw (x k)) A ∂(μ.map absVec) = μ A := by
  have hdec := sign_decomposition μ hsym
  have hG : Measurable (fun p : (Fin d → ℝ) × (Fin d → ℝ) => p.2 * p.1) :=
    measurable_snd.mul measurable_fst
  conv_rhs => rw [← hdec]
  rw [Measure.map_apply hG hA, Measure.prod_apply (hG hA)]
  refine lintegral_congr fun x => ?_
  have hm : Measurable (fun ε : Fin d → ℝ => x * ε) := measurable_const.mul measurable_id
  rw [pi_symLaw, Measure.map_apply hm hA]
  congr 1
  ext ε
  simp [mul_comm]

lemma measurable_symLaw_pi (A : Set (Fin d → ℝ)) (hA : MeasurableSet A) :
    Measurable fun x : Fin d → ℝ => (Measure.pi fun k => symLaw (x k)) A := by
  have : (fun x : Fin d → ℝ => (Measure.pi fun k => symLaw (x k)) A) =
      fun x => signsLaw d {ε | x * ε ∈ A} := by
    funext x
    have hm : Measurable (fun ε : Fin d → ℝ => x * ε) := measurable_const.mul measurable_id
    rw [pi_symLaw, Measure.map_apply hm hA]
    rfl
  rw [this]
  have hG : MeasurableSet {p : (Fin d → ℝ) × (Fin d → ℝ) | p.1 * p.2 ∈ A} :=
    (measurable_fst.mul measurable_snd) hA
  exact measurable_measure_prodMk_left hG

/-- The `X`-part of the embedding vector: `X_i = (X^k_i)_k`. -/
def Xp {ℓ : ℕ} (v : Fin d → Fin ℓ → ℝ × ℝ≥0∞) : Fin ℓ → Fin d → ℝ := fun i k => (v k i).1

lemma measurable_Xp (ℓ : ℕ) : Measurable (Xp (d := d) (ℓ := ℓ)) :=
  measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun k =>
    measurable_fst.comp ((measurable_pi_apply i).comp (measurable_pi_apply k))

lemma map_Xp {ℓ : ℕ} (ν : Fin d → Fin ℓ → Measure (ℝ × ℝ≥0∞))
    [∀ k i, IsProbabilityMeasure (ν k i)] :
    ((Measure.pi fun k : Fin d => Measure.pi fun i : Fin ℓ => ν k i).map Xp) =
      Measure.pi fun i : Fin ℓ => Measure.pi fun k : Fin d => (ν k i).map Prod.fst := by
  have hT : Measurable (fun (v : Fin d → Fin ℓ → ℝ × ℝ≥0∞) (i : Fin ℓ) (k : Fin d) => v k i) :=
    measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun k =>
      (measurable_pi_apply i).comp (measurable_pi_apply k)
  have h1 := pi_pi_transpose ν
  have hΦ : Xp = (fun (w : Fin ℓ → Fin d → ℝ × ℝ≥0∞) (i : Fin ℓ) =>
      (fun (u : Fin d → ℝ × ℝ≥0∞) (k : Fin d) => (u k).1) (w i)) ∘
      (fun (v : Fin d → Fin ℓ → ℝ × ℝ≥0∞) (i : Fin ℓ) (k : Fin d) => v k i) := rfl
  have hf : ∀ i : Fin ℓ, Measurable (fun (u : Fin d → ℝ × ℝ≥0∞) (k : Fin d) => (u k).1) :=
    fun i => measurable_pi_iff.2 fun k => measurable_fst.comp (measurable_pi_apply k)
  have hΦm : Measurable (fun (w : Fin ℓ → Fin d → ℝ × ℝ≥0∞) (i : Fin ℓ) =>
      (fun (u : Fin d → ℝ × ℝ≥0∞) (k : Fin d) => (u k).1) (w i)) :=
    measurable_pi_iff.2 fun i => (hf i).comp (measurable_pi_apply i)
  rw [hΦ, ← Measure.map_map hΦm hT, h1]
  have := Measure.pi_map_pi (μ := fun i : Fin ℓ => Measure.pi fun k : Fin d => ν k i)
    (f := fun _ (u : Fin d → ℝ × ℝ≥0∞) (k : Fin d) => (u k).1) (fun i => (hf i).aemeasurable)
  refine this.trans ?_
  congr 1
  funext i
  have := Measure.pi_map_pi (μ := fun k : Fin d => ν k i)
    (f := fun _ (u : ℝ × ℝ≥0∞) => u.1) (fun k => measurable_fst.aemeasurable)
  exact this

lemma ae_map_abs_nonneg (μ : Measure (Fin d → ℝ)) :
    ∀ᵐ x ∂(μ.map absVec), ∀ k, 0 ≤ x k := by
  have hS : MeasurableSet {x : Fin d → ℝ | ∀ k, 0 ≤ x k} := by
    have : {x : Fin d → ℝ | ∀ k, 0 ≤ x k} = ⋂ k, {x : Fin d → ℝ | 0 ≤ x k} := by
      ext x; simp
    rw [this]
    exact MeasurableSet.iInter fun k => measurableSet_le measurable_const (measurable_pi_apply k)
  rw [ae_map_iff (measurable_absVec d).aemeasurable hS]
  exact Filter.Eventually.of_forall fun x k => abs_nonneg _

/-- The first `X`-part of the embedding on the coupling space. -/
noncomputable def Xvec {ℓ : ℕ} (ω : Ω1 d ℓ) : Fin ℓ → Fin d → ℝ := Xp (Vfull ℓ ω)

lemma measurable_Xvec (ℓ : ℕ) : Measurable (Xvec (d := d) (ℓ := ℓ)) :=
  (measurable_Xp ℓ).comp (measurable_Vfull d ℓ)

/-- Laws in the coupling (a): `(X_i)_i ∼ μ^{⊗ℓ}`. -/
theorem map_Xvec (ℓ : ℕ) (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ]
    (hsym : ∀ ε : Fin d → ℝ, (∀ k, ε k = 1 ∨ ε k = -1) → μ.map (fun x => ε * x) = μ) :
    (P1 d ℓ (μ.map absVec)).map Xvec = Measure.pi fun _ : Fin ℓ => μ := by
  have : IsProbabilityMeasure (μ.map absVec) :=
    (Measure.isProbabilityMeasure_map_iff (measurable_absVec d).aemeasurable).2 inferInstance
  refine (Measure.pi_eq fun s hs => ?_).symm
  have hB : MeasurableSet (Set.univ.pi s) := MeasurableSet.univ_pi hs
  rw [Measure.map_apply (measurable_Xvec ℓ) hB, ← lintegral_indicator_one
    ((measurable_Xvec ℓ) hB)]
  have hG : Measurable (Function.uncurry fun (_ : Fin ℓ → Fin d → ℝ)
      (v : Fin d → Fin ℓ → ℝ × ℝ≥0∞) => (Set.univ.pi s).indicator (1 : (Fin ℓ → Fin d → ℝ) → ℝ≥0∞)
        (Xp v)) :=
    (measurable_one.indicator hB).comp ((measurable_Xp ℓ).comp measurable_snd)
  have hcond := lintegral_cond (lam := μ.map absVec) (ae_map_abs_nonneg μ) hG
  have e1 : ∀ ω : Ω1 d ℓ, (Xvec ⁻¹' Set.univ.pi s).indicator (1 : Ω1 d ℓ → ℝ≥0∞) ω =
      (Set.univ.pi s).indicator (1 : (Fin ℓ → Fin d → ℝ) → ℝ≥0∞) (Xp (Vfull ℓ ω)) := by
    intro ω
    by_cases h : Xvec ω ∈ Set.univ.pi s
    · rw [Set.indicator_of_mem (show ω ∈ Xvec ⁻¹' Set.univ.pi s from h),
        Set.indicator_of_mem (show Xp (Vfull ℓ ω) ∈ Set.univ.pi s from h)]
      rfl
    · rw [Set.indicator_of_notMem (show ω ∉ Xvec ⁻¹' Set.univ.pi s from h),
        Set.indicator_of_notMem (show Xp (Vfull ℓ ω) ∉ Set.univ.pi s from h)]
  simp_rw [e1]
  rw [hcond]
  have e2 : ∀ r : Fin ℓ → Fin d → ℝ, ∫⁻ v, (Set.univ.pi s).indicator 1 (Xp v) ∂(Lr ℓ r) =
      ∏ i, (Measure.pi fun k => symLaw (r i k)) (s i) := by
    intro r
    have hprob : ∀ (k : Fin d) (i : Fin ℓ),
        IsProbabilityMeasure ((symLaw (r i k)).prod (exitLaw (r i k))) := fun _ _ => inferInstance
    rw [← lintegral_map (measurable_one.indicator hB) (measurable_Xp ℓ), Lr, map_Xp]
    simp only [Measure.map_fst_prod, measure_univ, one_smul]
    rw [lintegral_indicator_one hB, Measure.pi_pi]
  simp_rw [e2]
  rw [PR, lintegral_pi_prod (μ.map absVec) (fun i x => (Measure.pi fun k => symLaw (x k)) (s i))
    (fun i => measurable_symLaw_pi (s i) (hs i))]
  refine Finset.prod_congr rfl fun i _ => ?_
  exact mixture_symLaw μ hsym (hs i)

end ElboimSly.StrongApprox
