/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.SRW.Law1d
public import Mathlib

/-!
# The one-dimensional law at a fixed time

One-dimensional law at a fixed time.  For every SRW `Y` in dimension `1`,
`P(Y(t) = k) = ∑_m po_t(m) po_t(m + |k|)`, the law is symmetric, and `P(Y(t) ≥ 0) ≥ 1/2`,
`P(Y(t) ≤ 0) ≥ 1/2`.  The same holds for each coordinate of a `d`-dimensional SRW.  The canonical
statement ("`N^±(t)` are independent `Poi(t)` and `Y(t) = N^+(t) - N^-(t)`") is
`iIndepFun_cntN`, `map_cntN` and `walk_ae_eq`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ElboimSly
namespace SRW

/-- The difference of two independent Poisson variables of the same mean. -/
theorem real_sub_eq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {A B : Ω → ℕ} (hA : Measurable A) (hB : Measurable B) (hind : IndepFun A B P) {t : ℝ}
    (ht : 0 ≤ t) (hAl : P.map A = poissonMeasure t.toNNReal)
    (hBl : P.map B = poissonMeasure t.toNNReal) (k : ℤ) :
    P.real {ω | (A ω : ℤ) - B ω = k} = ∑' m : ℕ, po t m * po t (m + k.natAbs) := by
  set S : Set (ℕ × ℕ) := {p | (p.1 : ℤ) - p.2 = k} with hS
  have hSm : MeasurableSet S := (Set.to_countable S).measurableSet
  have hmeas : Measurable fun ω => (A ω, B ω) := hA.prodMk hB
  have hpre : {ω | (A ω : ℤ) - B ω = k} = (fun ω => (A ω, B ω)) ⁻¹' S := rfl
  have hprod : P.map (fun ω => (A ω, B ω)) =
      (poissonMeasure t.toNNReal).prod (poissonMeasure t.toNNReal) := by
    rw [(indepFun_iff_map_prod_eq_prod_map_map hA.aemeasurable hB.aemeasurable).1 hind, hAl, hBl]
  rw [Measure.real, hpre, ← Measure.map_apply hmeas hSm, hprod]
  -- the set `S` is the range of an injective map from `ℕ`
  let f : ℕ → ℕ × ℕ := fun m => if 0 ≤ k then (m + k.natAbs, m) else (m, m + k.natAbs)
  have hfinj : Function.Injective f := by
    intro a b h
    unfold f at h
    split_ifs at h <;> simp_all [Prod.ext_iff]
  have hSeq : S = ⋃ m, {f m} := by
    ext ⟨a, b⟩
    simp only [hS, mem_ofPred_eq, mem_iUnion, mem_singleton_iff, f]
    constructor
    · intro h
      by_cases hk : 0 ≤ k
      · refine ⟨b, ?_⟩
        rw [ite_eq_left hk]
        simp only [Prod.mk.injEq, and_true]
        omega
      · refine ⟨a, ?_⟩
        rw [ite_eq_right hk]
        simp only [Prod.mk.injEq, true_and]
        omega
    · rintro ⟨m, hm⟩
      split_ifs at hm with hk
      · simp only [Prod.mk.injEq] at hm
        obtain ⟨rfl, rfl⟩ := hm
        omega
      · simp only [Prod.mk.injEq] at hm
        obtain ⟨rfl, rfl⟩ := hm
        omega
  have hdisj : Pairwise (Function.onFun Disjoint fun m : ℕ => ({f m} : Set (ℕ × ℕ))) := by
    intro a b hab
    simp only [Function.onFun, disjoint_singleton]
    exact fun h => hab (hfinj h)
  rw [hSeq, measure_iUnion hdisj (fun m => measurableSet_singleton _)]
  have hterm : ∀ m : ℕ, ((poissonMeasure t.toNNReal).prod (poissonMeasure t.toNNReal)) {f m} =
      ENNReal.ofReal (po t m * po t (m + k.natAbs)) := by
    intro m
    have hpo : ∀ n : ℕ, poissonMeasure t.toNNReal {n} = ENNReal.ofReal (po t n) := by
      intro n
      rw [poissonMeasure_singleton]
      unfold po
      rw [Real.coe_toNNReal _ ht]
    have hps : ∀ a b : ℕ, ((poissonMeasure t.toNNReal).prod (poissonMeasure t.toNNReal))
        {(a, b)} = ENNReal.ofReal (po t a) * ENNReal.ofReal (po t b) := by
      intro a b
      rw [← Set.singleton_prod_singleton, Measure.prod_prod, hpo, hpo]
    unfold f
    split_ifs
    · rw [hps, ← ENNReal.ofReal_mul (po_nonneg ht _), mul_comm]
    · rw [hps, ← ENNReal.ofReal_mul (po_nonneg ht _)]
  simp_rw [hterm]
  rw [ENNReal.tsum_toReal_eq (fun _ => ENNReal.ofReal_ne_top)]
  congr 1
  funext m
  exact ENNReal.toReal_ofReal (mul_nonneg (po_nonneg ht _) (po_nonneg ht _))

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- The value of the signed count is a difference of two independent Poisson variables
(canonical walk). -/
theorem real_coordY_eq {d : ℕ} {N : Ω → Measure (Dir d × ℝ)}
    (hN : IsPoissonPointProcess N (clockIntensity (Dir d)) P) {t : ℝ} (ht : 0 ≤ t) (i : Fin d)
    (k : ℤ) :
    P.real {ω | coordY N t i ω = k} = ∑' m : ℕ, po t m * po t (m + k.natAbs) := by
  have := hN.isProbabilityMeasure
  exact real_sub_eq (measurable_cntN hN t _) (measurable_cntN hN t _)
    ((iIndepFun_cntN hN t).indepFun (by simp)) ht (map_cntN hN ht _) (map_cntN hN ht _) k

/-- One-dimensional law at a fixed time: the law of `Y(t)` for every one-dimensional SRW. -/
theorem IsSRW.real_eval_eq {Y : Ω → PathSpace 1} (hY : IsSRW P Y) (t : ℝ≥0) (k : ℤ) :
    P.real {ω | Y ω t 0 = k} = ∑' m : ℕ, po t m * po t (m + k.natAbs) := by
  obtain ⟨Ω', _, P', N', hN', hE⟩ := hY.exists_canonical
  have hev : Measurable fun γ : PathSpace 1 => γ t 0 :=
    (measurable_pi_apply (0 : Fin 1)).comp (measurable_pi_apply t)
  have hset : MeasurableSet {γ : PathSpace 1 | γ t 0 = k} := hev (measurableSet_singleton k)
  have h1 : P {ω | Y ω t 0 = k} = P' {ω | walk 1 (N' ω) t 0 = k} := hE _ hset
  have h2 : {ω | walk 1 (N' ω) t 0 = k} =ᵐ[P'] {ω | coordY N' t 0 ω = k} := by
    filter_upwards [walk_ae_eq hN' t] with ω hω
    exact propext (by rw [hω 0])
  rw [Measure.real, h1, measure_congr h2, ← Measure.real]
  exact real_coordY_eq hN' t.2 0 k

/-- One-dimensional law at a fixed time: the law is symmetric. -/
theorem IsSRW.real_eval_neg {Y : Ω → PathSpace 1} (hY : IsSRW P Y) (t : ℝ≥0) (k : ℤ) :
    P.real {ω | Y ω t 0 = k} = P.real {ω | Y ω t 0 = -k} := by
  rw [hY.real_eval_eq, hY.real_eval_eq, Int.natAbs_neg]

theorem IsSRW.measurable_eval1 {Y : Ω → PathSpace 1} (hY : IsSRW P Y) (t : ℝ≥0) :
    Measurable fun ω => Y ω t 0 :=
  (measurable_pi_apply (0 : Fin 1)).comp ((measurable_pi_apply t).comp hY.1)

/-- One-dimensional law at a fixed time: `Y(t)` and `-Y(t)` have the same law. -/
theorem IsSRW.measure_eval_neg {Y : Ω → PathSpace 1} (hY : IsSRW P Y) (t : ℝ≥0) (S : Set ℤ) :
    P {ω | -Y ω t 0 ∈ S} = P {ω | Y ω t 0 ∈ S} := by
  have := hY.isProbabilityMeasure
  have hmY := hY.measurable_eval1 t
  have hsing : ∀ k : ℤ, (P.map fun ω => Y ω t 0) {k} = P {ω | Y ω t 0 = k} := fun k => by
    rw [Measure.map_apply hmY (measurableSet_singleton k)]; rfl
  have hneg : (P.map fun ω => Y ω t 0).map (fun x : ℤ => -x) = P.map fun ω => Y ω t 0 := by
    refine Measure.ext_of_singleton fun k => ?_
    rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton k)]
    have : (fun x : ℤ => -x) ⁻¹' {k} = {-k} := by
      ext x; simp
    rw [this, hsing, hsing, ← ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _)
      (measure_ne_top _ _)]
    exact (hY.real_eval_neg t k).symm
  have hS : MeasurableSet S := (Set.to_countable S).measurableSet
  calc P {ω | -Y ω t 0 ∈ S}
      = (P.map fun ω => Y ω t 0) ((fun x : ℤ => -x) ⁻¹' S) := by
        rw [Measure.map_apply hmY ((measurable_of_countable _) hS)]; rfl
    _ = ((P.map fun ω => Y ω t 0).map (fun x : ℤ => -x)) S :=
        (Measure.map_apply (measurable_of_countable _) hS).symm
    _ = (P.map fun ω => Y ω t 0) S := by rw [hneg]
    _ = P {ω | Y ω t 0 ∈ S} := by rw [Measure.map_apply hmY hS]; rfl

/-- One-dimensional law at a fixed time: `P(Y(t) ≥ 0) ≥ 1/2` and `P(Y(t) ≤ 0) ≥ 1/2`. -/
theorem IsSRW.half_le {Y : Ω → PathSpace 1} (hY : IsSRW P Y) (t : ℝ≥0) :
    1 / 2 ≤ P.real {ω | 0 ≤ Y ω t 0} ∧ 1 / 2 ≤ P.real {ω | Y ω t 0 ≤ 0} := by
  have := hY.isProbabilityMeasure
  have hmY := hY.measurable_eval1 t
  have hsym : P.real {ω | Y ω t 0 ≤ 0} = P.real {ω | 0 ≤ Y ω t 0} := by
    have := hY.measure_eval_neg t (Ici 0)
    simp only [mem_Ici, neg_nonneg] at this
    rw [Measure.real, Measure.real, this]
  have hsum : 1 ≤ P.real {ω | 0 ≤ Y ω t 0} + P.real {ω | Y ω t 0 ≤ 0} := by
    have h1 : MeasurableSet {ω | 0 ≤ Y ω t 0} := hmY measurableSet_Ici
    have := measureReal_union_le (μ := P) {ω | 0 ≤ Y ω t 0} {ω | Y ω t 0 ≤ 0}
    have hu : {ω | 0 ≤ Y ω t 0} ∪ {ω | Y ω t 0 ≤ 0} = univ := by
      ext ω; simp [le_total]
    rw [hu] at this
    simpa using this
  rw [hsym] at hsum ⊢
  constructor <;> linarith

end SRW
end ElboimSly
