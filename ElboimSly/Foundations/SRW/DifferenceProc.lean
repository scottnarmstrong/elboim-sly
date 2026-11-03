/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.SRW.ReversalMain
public import Mathlib

/-!
# Difference of independent walks: point processes

Difference of independent walks.

`psi ν` is the walk built from the counts of `ν`, without the good-event gate.  For a point process
`N`, `Ñ = N + (σ_* N')` with `σ` flipping all signs is a Poisson point process with intensity
`2 · clockIntensity` (`isPPP_sum`), as is the time-halved process `(id × (·/2))_* N`
(`isPPP_scale`).  On the good events, `canonical N - canonical N' = psi Ñ` and
`canonical N (2 ·) = psi (scaled N)`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ElboimSly
namespace SRW

variable {d : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω] {N N' : Ω → Measure (Dir d × ℝ)}
  {P : Measure Ω}

/-- The walk built from the counts of `ν`, without the good-event gate. -/
noncomputable def psi (d : ℕ) (ν : Measure (Dir d × ℝ)) : PathSpace d := fun s =>
  ∑ v : Dir d, ((natOf (ν (({v} : Set (Dir d)) ×ˢ Ioc 0 (s : ℝ))) : ℕ) : ℤ) • v.vec

theorem measurable_psi (d : ℕ) : Measurable (psi d) := by
  refine measurable_pi_iff.2 fun s => ?_
  refine Finset.measurable_fun_sum _ fun v _ => ?_
  have h : Measurable fun ρ : Measure (Dir d × ℝ) =>
      natOf (ρ (({v} : Set (Dir d)) ×ˢ Ioc 0 (s : ℝ))) :=
    measurable_natOf.comp (Measure.measurable_coe (measurableSet_rect v _ measurableSet_Ioc))
  exact (Measurable.of_discrete (f := fun n : ℕ => ((n : ℤ) • v.vec))).comp h

theorem psi_of_good {ν : Measure (Dir d × ℝ)} (hν : ν ∈ goodSet d) (s : ℝ≥0) :
    psi d ν s = can d ν s := by
  simp only [psi, can]
  rw [walk_of_good hν]
  rfl

theorem natOf_add {x y : ℝ≥0∞} (hx : IsNat x) (hy : IsNat y) : natOf (x + y) = natOf x + natOf y := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  have : (a : ℝ≥0∞) + b = ((a + b : ℕ) : ℝ≥0∞) := by push_cast; rfl
  rw [this]
  simp only [natOf, ENNReal.toReal_natCast, Nat.floor_natCast]

theorem psi_add {ν₁ ν₂ : Measure (Dir d × ℝ)} (h₁ : ν₁ ∈ goodSet d) (h₂ : ν₂ ∈ goodSet d)
    (s : ℝ≥0) : psi d (ν₁ + ν₂) s = psi d ν₁ s + psi d ν₂ s := by
  simp only [psi, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun v _ => ?_
  have hc1 : IsNat (ν₁ (({v} : Set (Dir d)) ×ˢ Ioc 0 (s : ℝ))) := good_cnt h₁ v s
  have hc2 : IsNat (ν₂ (({v} : Set (Dir d)) ×ˢ Ioc 0 (s : ℝ))) := good_cnt h₂ v s
  rw [Measure.add_apply, natOf_add hc1 hc2]
  push_cast
  rw [add_smul]

theorem psi_map_negPerm (ν : Measure (Dir d × ℝ)) (s : ℝ≥0) :
    psi d (ν.map (Prod.map (negPerm d) id)) s = -psi d ν s := by
  simp only [psi, ← Finset.sum_neg_distrib]
  have h : ∀ w : Dir d, (ν.map (Prod.map (negPerm d) id)) (({w} : Set (Dir d)) ×ˢ Ioc 0 (s : ℝ)) =
      ν (({(negPerm d).symm w} : Set (Dir d)) ×ˢ Ioc 0 (s : ℝ)) := fun w =>
    cnt_perm (negPerm d) ν w s
  simp only [h]
  refine Fintype.sum_equiv (negPerm d).symm _ _ (fun w => ?_)
  have := vec_negPerm ((negPerm d).symm w)
  rw [Equiv.apply_symm_apply] at this
  rw [this, smul_neg]

theorem clock_scale :
    (clockIntensity (Dir d)).map (Prod.map id (fun s : ℝ => s * 2⁻¹)) =
      clockIntensity (Dir d) + clockIntensity (Dir d) := by
  unfold clockIntensity
  have hg : Measurable fun s : ℝ => s * 2⁻¹ := measurable_id.mul_const _
  rw [← Measure.map_prod_map _ _ measurable_id hg, Measure.map_id]
  have hpre : (fun s : ℝ => s * 2⁻¹) ⁻¹' Ioi 0 = Ioi 0 := by
    ext x; simp only [mem_preimage, mem_Ioi]
    constructor <;> intro h <;> linarith
  have h1 := Measure.restrict_map (μ := (volume : Measure ℝ)) (f := fun s : ℝ => s * 2⁻¹) hg
    (measurableSet_Ioi (a := (0 : ℝ)))
  rw [hpre, Real.map_volume_mul_right (by norm_num)] at h1
  rw [← h1]
  have h2 : ENNReal.ofReal |(2 : ℝ)⁻¹⁻¹| = 2 := by
    rw [inv_inv, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    simp
  rw [Measure.restrict_smul, h2, Measure.prod_smul_right, two_smul]

theorem isPPP_scale (hN : IsPoissonPointProcess N (clockIntensity (Dir d)) P) :
    IsPoissonPointProcess (fun ω => (N ω).map (Prod.map id (fun s : ℝ => s * 2⁻¹)))
      (clockIntensity (Dir d) + clockIntensity (Dir d)) P := by
  have hφ : Measurable (Prod.map (id : Dir d → Dir d) (fun s : ℝ => s * 2⁻¹)) :=
    measurable_id.prodMap (measurable_id.mul_const _)
  have h := hN.map_measure hφ
  rwa [clock_scale] at h

theorem isPPP_sum (hN : IsPoissonPointProcess N (clockIntensity (Dir d)) P)
    (hN' : IsPoissonPointProcess N' (clockIntensity (Dir d)) P) (hind : IndepFun N N' P) :
    IsPoissonPointProcess (fun ω => N ω + (N' ω).map (Prod.map (negPerm d) id))
      (clockIntensity (Dir d) + clockIntensity (Dir d)) P := by
  have hneg := perm_ppp hN' (negPerm d)
  have hm : Measurable fun ν : Measure (Dir d × ℝ) => ν.map (Prod.map (negPerm d) id) :=
    measurable_map_measure ((measurable_of_countable _).prodMap measurable_id)
  exact hN.add hneg (hind.comp measurable_id hm)

end SRW
end ElboimSly
