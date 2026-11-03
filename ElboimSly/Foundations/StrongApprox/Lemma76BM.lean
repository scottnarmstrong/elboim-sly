/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.StrongApprox.BaseBM
public import Mathlib

/-!
# A Brownian motion through an initial Gaussian vector

The coupling step of Lemma 7.6, re-tuned ("The Brownian motion").

On `(Ωz × SX d) × SH d`, given `z : Ωz → (Fin ℓ → ℝ^d)` with law `N_d(0,I)^{⊗ℓ}`, put
`X_m = z_{m+1}` for `m < ℓ` and `X_m = x_{m}` otherwise; Brownian interpolation of a Gaussian walk gives a standard
Brownian motion `B` with `B(j+1) = ∑_{i ≤ j} z_i` for `j < ℓ`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ElboimSly
namespace StrongApprox

variable {d : ℕ} {Ωz : Type*} [MeasurableSpace Ωz]

/-- The increments `X_m`. -/
noncomputable def XfamZ {ℓ : ℕ} (z : Ωz → Fin ℓ → Fin d → ℝ) (ω : Ωz × SX d) : ℕ → Fin d → ℝ :=
  overrideAt (fun m : Fin ℓ => (m : ℕ)) (z ω.1) ω.2

theorem bm_of_override (Pz : Measure Ωz) [IsProbabilityMeasure Pz] {ℓ : ℕ}
    (z : Ωz → Fin ℓ → Fin d → ℝ) (hz : Measurable z)
    (hzlaw : Pz.map z = Measure.pi fun _ : Fin ℓ => Measure.pi fun _ : Fin d => gaussianReal 0 1) :
    ∃ B : ℝ≥0 → (Ωz × SX d) × SH d → Fin d → ℝ,
      IsStandardBrownianMotion d B ((Pz.prod (PX d)).prod (PH d)) ∧
      ∀ (j : Fin ℓ) (ω : (Ωz × SX d) × SH d),
        B (((j : ℕ) + 1 : ℕ) : ℝ≥0) ω = ∑ i ∈ Finset.univ.filter (· ≤ j), z ω.1.1 i := by
  set P' : Measure ((Ωz × SX d) × SH d) := (Pz.prod (PX d)).prod (PH d) with hP'
  have hXm : Measurable (XfamZ z : Ωz × SX d → ℕ → Fin d → ℝ) := by
    have := (measurable_overrideAt (X := Fin d → ℝ) (J := Fin ℓ)
      (j := fun m : Fin ℓ => (m : ℕ)) Fin.val_injective)
    exact this.comp ((hz.comp measurable_fst).prodMk measurable_snd)
  set X : ℕ → (Ωz × SX d) × SH d → Fin d → ℝ := fun m ω => XfamZ z ω.1 m with hX
  set η : Brownian.BridgeIdx d → (Ωz × SX d) × SH d → ℝ := fun β ω => ω.2 β with hη
  have hXm' : ∀ m, Measurable (X m) := fun m =>
    (measurable_pi_apply m).comp (hXm.comp measurable_fst)
  have hηm : ∀ β, Measurable (η β) := fun β => (measurable_pi_apply β).comp measurable_snd
  have hlawX : (Pz.prod (PX d)).map (XfamZ z) = PX d := by
    have hZ : Measurable fun ω : Ωz × SX d => z ω.1 := hz.comp measurable_fst
    have hW : Measurable fun ω : Ωz × SX d => ω.2 := measurable_snd
    have hind : IndepFun (fun ω : Ωz × SX d => z ω.1) (fun ω : Ωz × SX d => ω.2)
        (Pz.prod (PX d)) := indepFun_prod (X := z) (Y := id) hz measurable_id
    have hZlaw : (Pz.prod (PX d)).map (fun ω : Ωz × SX d => z ω.1) =
        Measure.pi fun _ : Fin ℓ => Measure.pi fun _ : Fin d => gaussianReal 0 1 := by
      have : (fun ω : Ωz × SX d => z ω.1) = z ∘ Prod.fst := rfl
      rw [this, ← Measure.map_map hz measurable_fst]
      simpa [Measure.map_fst_prod] using hzlaw
    have hWlaw : (Pz.prod (PX d)).map (fun ω : Ωz × SX d => ω.2) = PX d := by
      simp [Measure.map_snd_prod]
    exact map_overrideAt_eq_infinitePi
      (fun _ : ℕ => Measure.pi fun _ : Fin d => gaussianReal 0 1) Fin.val_injective hZ hW hind
      hZlaw hWlaw
  have hXfam : P'.map (fun ω i => X i ω) =
      Measure.infinitePi fun _ : ℕ => Measure.pi fun _ : Fin d => gaussianReal 0 1 := by
    have : (fun ω i => X i ω) = XfamZ z ∘ Prod.fst := rfl
    rw [this, ← Measure.map_map hXm measurable_fst, hP']
    simp only [Measure.map_fst_prod, measure_univ, one_smul]
    exact hlawX
  have hηfam : P'.map (fun ω β => η β ω) =
      Measure.infinitePi fun _ : Brownian.BridgeIdx d => gaussianReal 0 1 := by
    have : (fun ω β => η β ω) = (id : SH d → SH d) ∘ Prod.snd := rfl
    rw [this, ← Measure.map_map measurable_id measurable_snd, hP']
    simp [Measure.map_snd_prod]
    rfl
  obtain ⟨hXind, hXlaw⟩ := iIndep_hasLaw X hXm' _ _ hXfam
  obtain ⟨hηind, hηlaw⟩ := iIndep_hasLaw η hηm _ _ hηfam
  have hXη : IndepFun (fun ω m => X m ω) (fun ω β => η β ω) P' :=
    indepFun_prod (μ := Pz.prod (PX d)) (ν := PH d) (X := XfamZ z) (Y := id) hXm measurable_id
  refine ⟨Brownian.levyCiesielski (Brownian.interpXi X η),
    Brownian.isStandardBrownianMotion_interp hXm' hηm hXind hXlaw hηind hηlaw hXη, ?_⟩
  intro j ω
  rw [Brownian.levyCiesielski_interpXi_nat X η]
  -- ∑_{m < j+1} X_m = ∑_{i ≤ j} z_i
  have hXe : ∀ (m : ℕ) (hm : m < ℓ), X m ω = z ω.1.1 ⟨m, hm⟩ := fun m hm =>
    overrideAt_apply (j := fun m : Fin ℓ => (m : ℕ)) Fin.val_injective _ _ ⟨m, hm⟩
  refine Finset.sum_bij (fun m hm => (⟨m, by
      have := Finset.mem_range.1 hm; have := j.2; omega⟩ : Fin ℓ)) ?_ ?_ ?_ ?_
  · intro m hm
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.le_def]
    have := Finset.mem_range.1 hm; omega
  · intro m _ m' _ h
    simpa using h
  · intro p hp
    refine ⟨p, ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.le_def] at hp
    exact Finset.mem_range.2 (by omega)
  · intro m hm
    exact hXe m (by have := Finset.mem_range.1 hm; have := j.2; omega)

end StrongApprox
end ElboimSly
