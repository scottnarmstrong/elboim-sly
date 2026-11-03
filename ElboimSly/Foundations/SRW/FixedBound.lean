/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.SRW.FixedLaw
public import Mathlib

/-!
# The local upper bound for the canonical walk

Local upper bound without constant (canonical walk, fixed time).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Real

namespace ElboimSly
namespace SRW

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {N : Ω → Measure (Dir d × ℝ)} {P : Measure Ω}

theorem poisson_singleton_le {t : ℝ} (ht : 1 ≤ t) (n : ℕ) :
    poissonMeasure t.toNNReal {n} ≤ ENNReal.ofReal (1 / √(π * t)) := by
  rw [poissonMeasure_singleton]
  refine ENNReal.ofReal_le_ofReal ?_
  have := po_le_inv_sqrt_pi_mul ht n
  unfold po at this
  rwa [Real.coe_toNNReal _ (by linarith)]

/-- One coordinate at a fixed time `t ≥ 1` has no atom heavier than `(π t)^{-1/2}`. -/
theorem prob_coordY_le (hN : IsPoissonPointProcess N (clockIntensity (Dir d)) P) {t : ℝ}
    (ht : 1 ≤ t) (i : Fin d) (k : ℤ) :
    P {ω | coordY N t i ω = k} ≤ ENNReal.ofReal (1 / √(π * t)) := by
  have := hN.isProbabilityMeasure
  have ht0 : 0 ≤ t := by linarith
  have hind : IndepFun (cntN N t (i, true)) (cntN N t (i, false)) P :=
    (iIndepFun_cntN hN t).indepFun (by simp)
  set S : Set (ℕ × ℕ) := {p | (p.1 : ℤ) - p.2 = k} with hS
  have hSm : MeasurableSet S := (Set.to_countable S).measurableSet
  have hpre : {ω | coordY N t i ω = k} =
      (fun ω => (cntN N t (i, true) ω, cntN N t (i, false) ω)) ⁻¹' S := rfl
  have hmeas : Measurable fun ω => (cntN N t (i, true) ω, cntN N t (i, false) ω) :=
    (measurable_cntN hN t _).prodMk (measurable_cntN hN t _)
  rw [hpre, ← Measure.map_apply hmeas hSm,
    (indepFun_iff_map_prod_eq_prod_map_map (measurable_cntN hN t _).aemeasurable
      (measurable_cntN hN t _).aemeasurable).1 hind,
    map_cntN hN ht0, map_cntN hN ht0, Measure.prod_apply hSm]
  have hsec : ∀ x : ℕ, poissonMeasure t.toNNReal (Prod.mk x ⁻¹' S) ≤
      ENNReal.ofReal (1 / √(π * t)) := by
    intro x
    have hsub : (Prod.mk x ⁻¹' S).Subsingleton := by
      intro a ha b hb
      simp only [hS, mem_preimage, mem_ofPred_eq] at ha hb
      exact_mod_cast (by omega : (a : ℤ) = b)
    rcases hsub.eq_empty_or_singleton with h | ⟨b, h⟩
    · rw [h]; simp
    · rw [h]; exact poisson_singleton_le ht b
  calc ∫⁻ x, poissonMeasure t.toNNReal (Prod.mk x ⁻¹' S) ∂poissonMeasure t.toNNReal
      ≤ ∫⁻ _x, ENNReal.ofReal (1 / √(π * t)) ∂poissonMeasure t.toNNReal := lintegral_mono hsec
    _ = ENNReal.ofReal (1 / √(π * t)) := by simp

/-- Local upper bound without constant for the canonical walk: `P(X(t) = u) ≤ (π t)^{-d/2}`. -/
theorem prob_walk_eq_le (hN : IsPoissonPointProcess N (clockIntensity (Dir d)) P) {t : ℝ}
    (ht : 1 ≤ t) (u : Fin d → ℤ) :
    P {ω | walk d (N ω) t = u} ≤ ENNReal.ofReal ((1 / √(π * t)) ^ d) := by
  have := hN.isProbabilityMeasure
  have hae : {ω | walk d (N ω) t = u} =ᵐ[P] {ω | ∀ i, coordY N t i ω = u i} := by
    filter_upwards [walk_ae_eq hN t] with ω hω
    apply propext
    constructor
    · intro h i; rw [← hω i, h]
    · intro h; funext i; rw [hω i, h i]
  rw [measure_congr hae]
  have hind := (iIndepFun_iff_measure_inter_preimage_eq_mul.1 (iIndepFun_coordY hN t))
    Finset.univ (sets := fun i => {u i}) (fun i _ => measurableSet_singleton _)
  have : {ω | ∀ i, coordY N t i ω = u i} = ⋂ i ∈ (Finset.univ : Finset (Fin d)),
      coordY N t i ⁻¹' {u i} := by
    ext ω; simp
  rw [this, hind]
  calc ∏ i : Fin d, P (coordY N t i ⁻¹' {u i}) ≤ ∏ _i : Fin d, ENNReal.ofReal (1 / √(π * t)) :=
        Finset.prod_le_prod fun i _ => prob_coordY_le hN ht i (u i)
    _ = ENNReal.ofReal ((1 / √(π * t)) ^ d) := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
          ENNReal.ofReal_pow (by positivity)]

end SRW
end ElboimSly
