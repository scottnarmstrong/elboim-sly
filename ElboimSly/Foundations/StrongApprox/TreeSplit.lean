/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.StrongApprox.TreeLaw
public import Mathlib.Probability.Distributions.Gaussian.Fernique

/-!
# Splitting lemmas

Splitting. (a) A `Poisson(2r)` count split by the binomial quantile coupling gives
two independent `Poisson(r)` counts. (b) A `𝒩(0, 2r)` value split with an independent standard
normal `η` gives two independent `𝒩(0, r)` values.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal Real

namespace ElboimSly
namespace StrongApprox

/-- Scaling a centered Gaussian. -/
theorem gaussian_scale (c : ℝ) (v w : ℝ≥0) (h : c ^ 2 * v = w) :
    (gaussianReal 0 v).map (c * ·) = gaussianReal 0 w := by
  rw [gaussianReal_map_const_mul]
  congr 1
  · simp
  · ext; simp [h]

/-- The rotation-and-swap `(A, y) ↦ ((A + y)/√2, (A - y)/√2)` preserves `𝒩(0,1) ⊗ 𝒩(0,1)`. -/
theorem measurePreserving_hadamard :
    MeasurePreserving (fun p : ℝ × ℝ => ((p.1 + p.2) / √2, (p.1 - p.2) / √2))
      (saN.prod saN) (saN.prod saN) := by
  have : IsGaussian saN := by unfold saN; infer_instance
  have hs : (√2)⁻¹ = √2 / 2 := by
    have h := Real.sqrt_pos.2 (two_pos : (0 : ℝ) < 2)
    field_simp
    exact (Real.sq_sqrt (by norm_num)).symm
  have hrot : MeasurePreserving (ContinuousLinearMap.rotation (-(π / 4)))
      (saN.prod saN) (saN.prod saN) := by
    refine ⟨(ContinuousLinearMap.rotation (-(π / 4))).continuous.measurable, ?_⟩
    exact IsGaussian.map_rotation_eq_self (by unfold saN; exact integral_id_gaussianReal) _
  have := (Measure.measurePreserving_swap (μ := saN) (ν := saN)).comp hrot
  convert this using 1
  ext p
  · simp [ContinuousLinearMap.rotation_apply, Real.cos_neg, Real.sin_neg, Real.cos_pi_div_four,
      Real.sin_pi_div_four]
    rw [div_eq_mul_inv, hs]; ring
  · simp [ContinuousLinearMap.rotation_apply, Real.cos_neg, Real.sin_neg, Real.cos_pi_div_four,
      Real.sin_pi_div_four]
    rw [div_eq_mul_inv, hs]; ring

/-- Scaling by a nonzero constant maps `𝒩(0, v)` to `𝒩(0, w)` measure-preservingly. -/
theorem measurePreserving_gaussian_scale (c : ℝ) (v w : ℝ≥0) (h : c ^ 2 * v = w) :
    MeasurePreserving (fun x : ℝ => c * x) (gaussianReal 0 v) (gaussianReal 0 w) :=
  ⟨measurable_const.mul measurable_id, gaussian_scale c v w h⟩

/-- Splitting(b), with `r = 2^n`. -/
theorem measurePreserving_gauss_split (n : ℕ) :
    MeasurePreserving (fun p : ℝ × ℝ => (gL n p.1 p.2, gR n p.1 p.2))
      ((gaussianReal 0 (2 ^ (n + 1))).prod saN) ((gaussianReal 0 (2 ^ n)).prod
        (gaussianReal 0 (2 ^ n))) := by
  set c : ℝ := √((2 : ℝ) ^ n) with hc
  have hc0 : 0 < c := Real.sqrt_pos.2 (by positivity)
  have hcc : c ^ 2 = 2 ^ n := Real.sq_sqrt (by positivity)
  have hs2 : √(2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 < √(2 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hsc : sc n = √2 * c := by
    unfold sc; rw [pow_succ, mul_comm, Real.sqrt_mul (by positivity)]
  have m1 : MeasurePreserving (fun x : ℝ => (1 / sc n) * x) (gaussianReal 0 (2 ^ (n + 1)))
      saN := by
    refine measurePreserving_gaussian_scale _ _ _ ?_
    push_cast
    rw [hsc, div_pow, mul_pow, hs2, hcc, one_pow, pow_succ]
    field_simp
  have m3 : MeasurePreserving (fun x : ℝ => c * x) saN (gaussianReal 0 (2 ^ n)) := by
    refine measurePreserving_gaussian_scale _ _ _ ?_
    push_cast
    rw [hcc]; simp
  have := (m3.prod m3).comp (measurePreserving_hadamard.comp (m1.prod (MeasurePreserving.id saN)))
  convert this using 1
  ext p
  · simp only [Function.comp, Prod.map, gL, hsc]
    simp only [id]
    field_simp
    rw [hs2]
  · simp only [Function.comp, Prod.map, gR, hsc, id]
    field_simp
    rw [hs2]

/-- Splitting(a), with `r = 2^n`. -/
theorem measurePreserving_poisson_split (n : ℕ) :
    MeasurePreserving (fun p : ℕ × ℝ => (saq p.1 p.2, p.1 - saq p.1 p.2))
      ((poissonMeasure (2 ^ (n + 1))).prod saN)
      ((poissonMeasure (2 ^ n)).prod (poissonMeasure (2 ^ n))) := by
  have hm : Measurable (fun p : ℕ × ℝ => (saq p.1 p.2, p.1 - saq p.1 p.2)) :=
    measurable_saq.prodMk (measurable_fst.sub measurable_saq)
  refine ⟨hm, ?_⟩
  refine Measure.ext_of_measureReal_singleton fun ⟨a, c⟩ => ?_
  rw [measureReal_def, measureReal_def, Measure.map_apply hm (MeasurableSet.singleton _)]
  have hpre : (fun p : ℕ × ℝ => (saq p.1 p.2, p.1 - saq p.1 p.2)) ⁻¹' {(a, c)} =
      ({a + c} : Set ℕ) ×ˢ {y : ℝ | saq (a + c) y = a} := by
    ext ⟨m, y⟩
    simp only [mem_preimage, mem_singleton_iff, Prod.mk.injEq, mem_prod, mem_ofPred_eq]
    have := saq_le_m m y
    constructor
    · rintro ⟨h1, h2⟩
      have hm' : m = a + c := by omega
      subst hm'
      exact ⟨rfl, h1⟩
    · rintro ⟨h1, h2⟩
      subst h1
      exact ⟨h2, by omega⟩
  rw [hpre, Measure.prod_prod, ← singleton_prod_singleton, Measure.prod_prod,
    ENNReal.toReal_mul, ENNReal.toReal_mul]
  have h1 := saN_real_saq_eq (a + c) a
  rw [measureReal_def, sab_natCast] at h1
  rw [h1, ← measureReal_def, ← measureReal_def, ← measureReal_def,
    poissonMeasure_real_singleton, poissonMeasure_real_singleton, poissonMeasure_real_singleton]
  have hch : ((a + c).choose a : ℝ) = ((a + c).factorial : ℝ) / ((a.factorial : ℝ) * (c.factorial : ℝ)) := by
    rw [Nat.cast_choose ℝ (Nat.le_add_right a c), Nat.add_sub_cancel_left]
  have hexp : Real.exp (-((2 ^ (n + 1) : ℝ≥0) : ℝ)) =
      Real.exp (-((2 ^ n : ℝ≥0) : ℝ)) * Real.exp (-((2 ^ n : ℝ≥0) : ℝ)) := by
    rw [← Real.exp_add]; congr 1; push_cast; ring
  rw [hch, hexp]
  push_cast
  rw [pow_add, pow_succ, mul_pow, mul_pow]
  field_simp
  rw [pow_add]

section Induction

/-- Base case of the induction on the depth. -/
theorem tree_base {X : Type*} [MeasurableSpace X] (ν : Measure X) [IsProbabilityMeasure ν] :
    MeasurePreserving (fun p : X × DT 0 => fun _ : Fin (2 ^ 0) => p.1) (ν.prod (muDT 0))
      (Measure.pi fun _ : Fin (2 ^ 0) => ν) := by
  have hm : Measurable (fun p : X × DT 0 => fun _ : Fin (2 ^ 0) => p.1) :=
    Measurable.of_eval fun _ => measurable_fst
  refine ⟨hm, ?_⟩
  symm
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.map_apply hm (MeasurableSet.univ_pi hs)]
  have : Unique (Fin (2 ^ 0)) := inferInstanceAs (Unique (Fin 1))
  have hpre : (fun p : X × DT 0 => fun _ : Fin (2 ^ 0) => p.1) ⁻¹' (Set.univ.pi s) =
      s default ×ˢ (Set.univ : Set (DT 0)) := by
    ext ⟨x, d⟩
    simp [Set.mem_pi]
  rw [hpre, Measure.prod_prod, Fintype.prod_unique, measure_univ, mul_one]
  exact congrArg ν (congrArg s (Subsingleton.elim _ _))

/-- Laws in the tree(a). The Poisson leaves of the tree started from `Poisson(2^n)`
are i.i.d. `Poisson(1)`. -/
theorem tree_law_P (n : ℕ) :
    MeasurePreserving (fun p : ℕ × DT n => fun i : Fin (2 ^ n) => LP n p.1 p.2 i)
      ((poissonMeasure (2 ^ n)).prod (muDT n))
      (Measure.pi fun _ : Fin (2 ^ n) => poissonMeasure 1) := by
  induction n with
  | zero =>
    have := tree_base (poissonMeasure ((2 : ℝ≥0) ^ 0))
    simpa [LP] using this
  | succ n ih =>
    have := tree_step n (poissonMeasure (2 ^ (n + 1))) (poissonMeasure (2 ^ n))
      (poissonMeasure 1) _ (measurePreserving_poisson_split n)
      (fun m d i => LP n m d i) ih
    convert this using 2 with q
    funext i
    simp only [cat, LP]
    by_cases h : (i : ℕ) < 2 ^ n <;> simp [h]

/-- Laws in the tree(b). The Gaussian leaves of the tree started from `𝒩(0, 2^n)`
are i.i.d. `𝒩(0, 1)`. -/
theorem tree_law_G (n : ℕ) :
    MeasurePreserving (fun p : ℝ × DT n => fun i : Fin (2 ^ n) => LG n p.1 p.2 i)
      ((gaussianReal 0 (2 ^ n)).prod (muDT n))
      (Measure.pi fun _ : Fin (2 ^ n) => gaussianReal 0 1) := by
  induction n with
  | zero =>
    have := tree_base (gaussianReal 0 ((2 : ℝ≥0) ^ 0))
    simpa [LG] using this
  | succ n ih =>
    have := tree_step n (gaussianReal 0 (2 ^ (n + 1))) (gaussianReal 0 (2 ^ n))
      (gaussianReal 0 1) _ (measurePreserving_gauss_split n)
      (fun g d i => LG n g d i) ih
    convert this using 2 with q
    funext i
    simp only [cat, LG]
    by_cases h : (i : ℕ) < 2 ^ n <;> simp [h]

end Induction

end StrongApprox
end ElboimSly
