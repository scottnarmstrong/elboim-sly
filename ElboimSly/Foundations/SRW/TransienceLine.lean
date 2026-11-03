/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.SRW.TransienceFar
public import ElboimSly.Foundations.SRW.UpPath
public import Mathlib

/-!
# Running straight for time one

Transience: escape from the unit box, "getting far".
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Real

namespace ElboimSly
namespace SRW

variable {d : ℕ}

/-- Paths that, up to time `1`, move only in the direction `v₀`, ending at `R v₀`. -/
def gamLine (v₀ : Dir d) (R : ℕ) : Set (PathSpace d) :=
  evalForall {w : Fin d → ℤ | w = (R : ℤ) • v₀.vec}
    {w : Fin d → ℤ | ∃ k : ℕ, k ≤ R ∧ w = (k : ℤ) • v₀.vec} 1

theorem real_cntN_eq_po {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {N : Ω → Measure (Dir d × ℝ)} (hN : IsPoissonPointProcess N (clockIntensity (Dir d)) P)
    (v : Dir d) (n : ℕ) : P.real {ω | cntN N 1 v ω = n} = po 1 n := by
  have := hN.isProbabilityMeasure
  have h := map_cntN hN (t := 1) zero_le_one v
  have : P {ω | cntN N 1 v ω = n} = poissonMeasure ((1 : ℝ).toNNReal) {n} := by
    rw [← h, Measure.map_apply (measurable_cntN hN 1 v) (measurableSet_singleton n)]
    rfl
  rw [measureReal_def, this, poissonMeasure_singleton]
  unfold po
  simp
  try positivity

theorem prob_gamLine_canonical {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {N : Ω → Measure (Dir d × ℝ)} (hN : IsPoissonPointProcess N (clockIntensity (Dir d)) P)
    (v₀ : Dir d) (R : ℕ) :
    Real.exp (-(2 * d)) / R.factorial ≤ P.real {ω | canonical d N ω ∈ gamLine v₀ R} := by
  classical
  have := hN.isProbabilityMeasure
  set n : Dir d → ℕ := fun v => if v = v₀ then R else 0 with hn
  set E : Set Ω := ⋂ v : Dir d, {ω | cntN N 1 v ω = n v} with hE
  have hsub : E ≤ᵐ[P] {ω | canonical d N ω ∈ gamLine v₀ R} := by
    filter_upwards [ae_good hN] with ω hg hω
    have hω' : ∀ v : Dir d, natOf (cnt (N ω) v 1) = n v := fun v => by
      have := mem_iInter.1 hω v
      exact this
    have hcn : ∀ (v : Dir d) (k : ℕ), natOf (cnt (N ω) v 1) = k → cnt (N ω) v 1 = k := by
      intro v k hk
      obtain ⟨m, hm⟩ := good_cnt hg v 1
      rw [hm] at hk ⊢
      simp only [natOf, ENNReal.toReal_natCast, Nat.floor_natCast] at hk
      rw [hk]
    have hmono : ∀ (v : Dir d) (s : ℝ≥0), s ≤ 1 → cnt (N ω) v s ≤ cnt (N ω) v 1 := by
      intro v s hs
      unfold cnt
      refine measure_mono (prod_mono subset_rfl (Ioc_subset_Ioc_right ?_))
      exact_mod_cast hs
    have hcnt1 : ∀ v : Dir d, cnt (N ω) v 1 = (n v : ℝ≥0∞) := fun v => hcn v (n v) (hω' v)
    show canonical d N ω ∈ evalForall _ _ 1
    have hwalk : ∀ s : ℝ≥0, s ≤ 1 → walk d (N ω) (s : ℝ) =
        ((natOf (cnt (N ω) v₀ s) : ℕ) : ℤ) • v₀.vec := by
      intro s hs
      rw [walk_of_good hg]
      rw [Finset.sum_eq_single v₀]
      · intro v _ hv
        have h0 : cnt (N ω) v s = 0 := by
          have := hmono v s hs
          rw [hcnt1 v] at this
          have hnv : n v = 0 := by simp [hn, hv]
          rw [hnv] at this
          simpa using this
        rw [h0]; simp [natOf]
      · intro h; exact absurd (Finset.mem_univ _) h
    refine ⟨?_, fun s hs => ?_⟩
    · show walk d (N ω) ((1 : ℝ≥0) : ℝ) = (R : ℤ) • v₀.vec
      have := hwalk 1 le_rfl
      rw [this]
      have h1 := hω' v₀
      simp only [hn, ite_true] at h1
      rw [NNReal.coe_one] at *
      rw [h1]
    · show ∃ k : ℕ, k ≤ R ∧ walk d (N ω) (s : ℝ) = (k : ℤ) • v₀.vec
      refine ⟨natOf (cnt (N ω) v₀ s), ?_, hwalk s hs⟩
      obtain ⟨m, hm⟩ := good_cnt hg v₀ s
      have hle := hmono v₀ s hs
      rw [hcnt1 v₀] at hle
      simp only [hn, ite_true] at hle
      rw [hm] at hle ⊢
      simp only [natOf, ENNReal.toReal_natCast, Nat.floor_natCast]
      exact_mod_cast hle
  have hindep := (iIndepFun_cntN hN 1)
  have hprod : P.real E = ∏ v : Dir d, po 1 (n v) := by
    have h := hindep.measure_inter_preimage_eq_mul Finset.univ
      (sets := fun v => {n v}) (fun v _ => measurableSet_singleton _)
    have e : E = ⋂ v ∈ (Finset.univ : Finset (Dir d)), (fun ω => cntN N 1 v ω) ⁻¹' {n v} := by
      ext ω; simp [hE]
    rw [e, measureReal_def, h, ENNReal.toReal_prod]
    refine Finset.prod_congr rfl fun v _ => ?_
    have := real_cntN_eq_po hN v (n v)
    rw [measureReal_def] at this
    rw [← this]
    rfl
  have hle : P.real E ≤ P.real {ω | canonical d N ω ∈ gamLine v₀ R} :=
    ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hsub)
  refine le_trans (le_of_eq ?_) (hprod ▸ hle)
  rw [← Finset.mul_prod_erase Finset.univ (fun v => po 1 (n v)) (Finset.mem_univ v₀)]
  have h1 : po 1 (n v₀) = po 1 R := by simp [hn]
  have h2 : ∏ v ∈ Finset.univ.erase v₀, po 1 (n v) = (po 1 0) ^ (2 * d - 1) := by
    rw [Finset.prod_congr rfl (fun v hv => by
      have : n v = 0 := by simp [hn, (Finset.ne_of_mem_erase hv)]
      rw [this])]
    rw [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
    simp [Fintype.card_prod]
    ring_nf
  rw [h1, h2]
  unfold po
  simp only [Nat.factorial_zero, Nat.cast_one, pow_zero, div_one, mul_one, one_pow]
  have hd0 : 0 < d := Fin.pos v₀.1
  have h2d : 1 ≤ 2 * d := by omega
  rw [← Real.exp_nat_mul, div_mul_eq_mul_div, ← Real.exp_add]
  congr 2
  rw [Nat.cast_sub h2d]
  push_cast
  ring

end SRW
end ElboimSly
