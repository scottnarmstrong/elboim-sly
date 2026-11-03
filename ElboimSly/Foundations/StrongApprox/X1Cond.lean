/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.StrongApprox.X1Space
public import Mathlib

/-!
# Conditioning on the moduli

The coupling space; Laws in the coupling Step 2.

The coupling space is `Ω1 = (Fin ℓ → Fin d → ℝ) × ΩB d` with the product of `λ^{⊗ℓ}` and the
Wiener sample measure. Measurability of the embedding vector on `Ω1`, and the Tonelli identity
that replaces the embedding vector by its law for fixed moduli.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace ElboimSly.StrongApprox

open ElboimSly.Brownian

/-- The coupling space `Ω_R × Ω_B`. -/
abbrev Ω1 (d ℓ : ℕ) : Type := (Fin ℓ → Fin d → ℝ) × ΩB d

/-- The measure on the moduli: `λ^{⊗ℓ}`. -/
noncomputable def PR (d ℓ : ℕ) (lam : Measure (Fin d → ℝ)) : Measure (Fin ℓ → Fin d → ℝ) :=
  Measure.pi fun _ : Fin ℓ => lam

/-- The coupling measure `P_R ⊗ P_B`. -/
noncomputable def P1 (d ℓ : ℕ) (lam : Measure (Fin d → ℝ)) : Measure (Ω1 d ℓ) :=
  (PR d ℓ lam).prod (PB d)

/-- The embedding vector on the coupling space. -/
noncomputable def Vfull {d : ℕ} (ℓ : ℕ) (ω : Ω1 d ℓ) : Fin d → Fin ℓ → ℝ × ℝ≥0∞ :=
  vecV ℓ ω.1 ω.2

lemma measurable_rr {d ℓ : ℕ} (k : Fin d) (i : ℕ) :
    Measurable fun r : Fin ℓ → Fin d → ℝ => rr ℓ r k i := by
  unfold rr
  by_cases h : i < ℓ
  · simp only [h, dite_true]
    exact (measurable_pi_apply k).comp (measurable_pi_apply (⟨i, h⟩ : Fin ℓ))
  · simp [h]

lemma isProcess_coord1 {d ℓ : ℕ} (k : Fin d) :
    IsProcess (fun (t : ℝ≥0) (ω : Ω1 d ℓ) => Bd d t ω.2 k) := by
  have hp := isProcess_of_realBM (isStandardRealBM_Bd_coord d k)
  exact ⟨fun ω => hp.1 ω.2, fun t => (hp.2 t).comp measurable_snd⟩

lemma measurable_Vfull (d ℓ : ℕ) : Measurable (Vfull (d := d) ℓ) := by
  refine measurable_pi_iff.2 fun k => measurable_pi_iff.2 fun i => ?_
  have hρ : ∀ j, Measurable fun ω : Ω1 d ℓ => rr ℓ ω.1 k j := fun j =>
    (measurable_rr k j).comp measurable_fst
  exact (measurable_embX (isProcess_coord1 k) hρ i).prodMk
    (measurable_embTau (isProcess_coord1 k) hρ i)

variable {d ℓ : ℕ} {lam : Measure (Fin d → ℝ)} [IsProbabilityMeasure lam]

instance : IsProbabilityMeasure (PR d ℓ lam) := by unfold PR; infer_instance

instance : IsProbabilityMeasure (P1 d ℓ lam) := by unfold P1; infer_instance

lemma ae_PR_nonneg (hlam : ∀ᵐ x ∂lam, ∀ k, 0 ≤ x k) :
    ∀ᵐ r ∂(PR d ℓ lam), ∀ i k, 0 ≤ r i k := by
  rw [ae_all_iff]
  intro i
  have : ∀ᵐ r ∂(PR d ℓ lam), ∀ k, 0 ≤ r i k := by
    have hmp : MeasurePreserving (fun r : Fin ℓ → Fin d → ℝ => r i) (PR d ℓ lam) lam :=
      measurePreserving_eval (fun _ : Fin ℓ => lam) i
    exact hmp.quasiMeasurePreserving.ae hlam
  filter_upwards [this] with r hr k using hr k

/-- Laws in the coupling, Step 2 (Tonelli). -/
theorem lintegral_cond (hlam : ∀ᵐ x ∂lam, ∀ k, 0 ≤ x k)
    {G : (Fin ℓ → Fin d → ℝ) → (Fin d → Fin ℓ → ℝ × ℝ≥0∞) → ℝ≥0∞}
    (hG : Measurable (Function.uncurry G)) :
    ∫⁻ ω, G ω.1 (Vfull ℓ ω) ∂(P1 d ℓ lam) = ∫⁻ r, ∫⁻ v, G r v ∂(Lr ℓ r) ∂(PR d ℓ lam) := by
  have hmeas : Measurable fun ω : Ω1 d ℓ => G ω.1 (Vfull ℓ ω) :=
    hG.comp (measurable_fst.prodMk (measurable_Vfull d ℓ))
  rw [P1, lintegral_prod _ hmeas.aemeasurable]
  refine lintegral_congr_ae ?_
  filter_upwards [ae_PR_nonneg hlam] with r hr
  have hv : Measurable (vecV ℓ r : ΩB d → Fin d → Fin ℓ → ℝ × ℝ≥0∞) :=
    (measurable_Vfull d ℓ).comp (measurable_const.prodMk measurable_id)
  have hGr : Measurable (G r) := hG.comp (measurable_const.prodMk measurable_id)
  rw [← map_vecV hr, lintegral_map hGr hv]
  rfl

end ElboimSly.StrongApprox
