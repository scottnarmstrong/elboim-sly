/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Probability.ProbabilityMassFunction.Basic

/-!
# Sign decomposition

Signs, moduli, symmetric two-point laws; Sign decomposition (Part II).

A sign-symmetric law `μ` on `Fin d → ℝ` is the image of `|μ| ⊗ υ` under `(s, ε) ↦ ε * s`, where
`υ` is the uniform law on `{-1,1}^d`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace ElboimSly
namespace StrongApprox

/-- The uniform law on `{-1, 1}`. -/
noncomputable def signLaw : Measure ℝ := (2 : ℝ≥0∞)⁻¹ • (Measure.dirac 1 + Measure.dirac (-1))

/-- The uniform law `υ` on `{-1,1}^d`. Signs, moduli, symmetric two-point laws. -/
noncomputable def signsLaw (d : ℕ) : Measure (Fin d → ℝ) := Measure.pi fun _ => signLaw

/-- The coordinatewise absolute value. -/
def absVec {d : ℕ} (x : Fin d → ℝ) : Fin d → ℝ := fun k => |x k|

/-- The coordinatewise sign (`1` on `0 ≤ x k`, `-1` otherwise). -/
noncomputable def sgnVec {d : ℕ} (x : Fin d → ℝ) : Fin d → ℝ :=
  fun k => if 0 ≤ x k then 1 else -1

instance : IsProbabilityMeasure signLaw := ⟨by
  simp only [signLaw, Measure.smul_apply, Measure.add_apply, measure_univ, smul_eq_mul]
  rw [one_add_one_eq_two, mul_comm]
  exact ENNReal.mul_inv_cancel (by norm_num : (2:ℝ≥0∞) ≠ 0) (by norm_num : (2:ℝ≥0∞) ≠ ∞)⟩

instance (d : ℕ) : IsProbabilityMeasure (signsLaw d) := by
  unfold signsLaw; infer_instance

lemma measurable_absVec (d : ℕ) : Measurable (absVec (d := d)) :=
  Measurable.of_eval fun k => continuous_abs.measurable.comp (measurable_pi_apply k)

lemma sgnVec_mul_absVec {d : ℕ} (x : Fin d → ℝ) : sgnVec x * absVec x = x := by
  funext k
  by_cases h : 0 ≤ x k
  · simp [sgnVec, absVec, h, abs_of_nonneg h]
  · simp [sgnVec, absVec, h, abs_of_neg (not_le.mp h)]

lemma sgnVec_pm {d : ℕ} (x : Fin d → ℝ) (k : Fin d) : sgnVec x k = 1 ∨ sgnVec x k = -1 := by
  unfold sgnVec; split_ifs <;> simp

lemma signLaw_map_mul {c : ℝ} (hc : c = 1 ∨ c = -1) : signLaw.map (c * ·) = signLaw := by
  have hm : Measurable (c * · : ℝ → ℝ) := measurable_const.mul measurable_id
  unfold signLaw
  rw [Measure.map_smul, Measure.map_add _ _ hm]
  simp only [Measure.map_dirac' hm]
  rcases hc with rfl | rfl
  · simp
  · simp [add_comm]
  · exact hm.aemeasurable

lemma signsLaw_map_mul {d : ℕ} {σ : Fin d → ℝ} (hσ : ∀ k, σ k = 1 ∨ σ k = -1) :
    (signsLaw d).map (σ * ·) = signsLaw d := by
  unfold signsLaw
  have := Measure.pi_map_pi (μ := fun _ : Fin d => signLaw) (f := fun k (t : ℝ) => σ k * t)
    (fun k => (measurable_const.mul measurable_id).aemeasurable)
  simp only [signLaw_map_mul (hσ _)] at this
  exact this

lemma signsLaw_ae_pm (d : ℕ) : ∀ᵐ ε ∂(signsLaw d), ∀ k, ε k = 1 ∨ ε k = -1 := by
  rw [ae_all_iff]
  intro k
  have hmp : MeasurePreserving (fun ε : Fin d → ℝ => ε k) (signsLaw d) signLaw :=
    measurePreserving_eval (fun _ : Fin d => signLaw) k
  have : ∀ᵐ t ∂signLaw, t = 1 ∨ t = -1 := by
    rw [ae_iff]
    have h : {t : ℝ | ¬(t = 1 ∨ t = -1)} = ({1, -1} : Set ℝ)ᶜ := by
      ext t; simp
    rw [h]
    simp [signLaw]
  exact hmp.quasiMeasurePreserving.ae this

/-- Sign decomposition. Sign decomposition. -/
theorem sign_decomposition {d : ℕ} (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ]
    (hsym : ∀ ε : Fin d → ℝ, (∀ k, ε k = 1 ∨ ε k = -1) → μ.map (fun x => ε * x) = μ) :
    ((μ.map absVec).prod (signsLaw d)).map (fun p => p.2 * p.1) = μ := by
  have hG : Measurable (fun p : (Fin d → ℝ) × (Fin d → ℝ) => p.2 * p.1) :=
    measurable_snd.mul measurable_fst
  ext A hA
  have hGA : MeasurableSet ((fun p : (Fin d → ℝ) × (Fin d → ℝ) => p.2 * p.1) ⁻¹' A) := hG hA
  rw [Measure.map_apply hG hA, Measure.prod_apply hGA]
  have hmeas : Measurable fun s : Fin d → ℝ =>
      signsLaw d (Prod.mk s ⁻¹' ((fun p : (Fin d → ℝ) × (Fin d → ℝ) => p.2 * p.1) ⁻¹' A)) :=
    measurable_measure_prodMk_left hGA
  rw [lintegral_map hmeas (measurable_absVec d)]
  have step1 : ∀ x : Fin d → ℝ,
      signsLaw d (Prod.mk (absVec x) ⁻¹' ((fun p : (Fin d → ℝ) × (Fin d → ℝ) => p.2 * p.1) ⁻¹' A))
        = signsLaw d {ε | ε * x ∈ A} := by
    intro x
    have hmapx : (signsLaw d).map (sgnVec x * ·) = signsLaw d :=
      signsLaw_map_mul (sgnVec_pm x)
    have hm : Measurable (fun ε : Fin d → ℝ => sgnVec x * ε) := measurable_const.mul measurable_id
    have hS : MeasurableSet (Prod.mk (absVec x) ⁻¹'
        ((fun p : (Fin d → ℝ) × (Fin d → ℝ) => p.2 * p.1) ⁻¹' A)) :=
      measurable_prodMk_left hGA
    conv_lhs => rw [← hmapx, Measure.map_apply hm hS]
    congr 1
    ext ε
    simp only [Set.mem_preimage, Set.mem_ofPred_eq]
    rw [show sgnVec x * ε * absVec x = ε * x by
      conv_rhs => rw [← sgnVec_mul_absVec x]
      ring]
  simp_rw [step1]
  have e1 : ∫⁻ x, signsLaw d {ε | ε * x ∈ A} ∂μ = (μ.prod (signsLaw d)) ((fun p : (Fin d → ℝ) × (Fin d → ℝ) => p.2 * p.1) ⁻¹' A) := by
    rw [Measure.prod_apply hGA]; rfl
  rw [e1, Measure.prod_apply_symm hGA]
  have : ∀ᵐ ε ∂(signsLaw d),
      μ ((fun x => (x, ε)) ⁻¹' ((fun p : (Fin d → ℝ) × (Fin d → ℝ) => p.2 * p.1) ⁻¹' A)) = μ A := by
    filter_upwards [signsLaw_ae_pm d] with ε hε
    have hm : Measurable (fun x : Fin d → ℝ => ε * x) := measurable_const.mul measurable_id
    have h2 := hsym ε hε
    change μ ((fun x : Fin d → ℝ => ε * x) ⁻¹' A) = μ A
    rw [← Measure.map_apply hm hA, h2]
  rw [lintegral_congr_ae this]
  simp
