/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.PPP.MixedBinomialChar
public import ElboimSly.Foundations.PPP.Operations
public import Mathlib

/-!
# The mixed binomial process

Mixed binomial process.

`mixedBinomial K Y = ∑_{i<K} δ_{Y_i}`. If `K ~ Po(λ)` is independent of the i.i.d. sequence `Y`
with law `ν`, then it is a Poisson point process with intensity `λ ν`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Complex
open scoped ENNReal NNReal Nat

namespace ElboimSly

variable {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]

/-- `Ξ = ∑_{i<K} δ_{Y_i}`. Mixed binomial process. -/
noncomputable def mixedBinomial (K : Ω → ℕ) (Y : ℕ → Ω → S) (ω : Ω) : Measure S :=
  ∑ i ∈ Finset.range (K ω), Measure.dirac (Y i ω)

/-- The real-valued count `∑_{i<K} 1_A(Y_i)`. -/
noncomputable def mbCount (K : Ω → ℕ) (Y : ℕ → Ω → S) (A : Set S) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.range (K ω), A.indicator (fun _ => (1 : ℝ)) (Y i ω)

omit [MeasurableSpace Ω] in
theorem mixedBinomial_apply (K : Ω → ℕ) (Y : ℕ → Ω → S) (ω : Ω) {A : Set S}
    (hA : MeasurableSet A) :
    mixedBinomial K Y ω A = ENNReal.ofReal (mbCount K Y A ω) := by
  unfold mixedBinomial mbCount
  rw [Measure.coe_finsetSum, Finset.sum_apply,
    ENNReal.ofReal_sum_of_nonneg (fun i _ => Set.indicator_nonneg (fun _ _ => zero_le_one) _)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Measure.dirac_apply' _ hA]
  by_cases h : Y i ω ∈ A <;> simp [Set.indicator, h]

theorem measurable_mbCount {K : Ω → ℕ} {Y : ℕ → Ω → S} (hK : Measurable K)
    (hY : ∀ i, Measurable (Y i)) {A : Set S} (hA : MeasurableSet A) :
    Measurable (mbCount K Y A) := by
  have hF : Measurable fun p : ℕ × Ω => ∑ i ∈ Finset.range p.1,
      A.indicator (fun _ => (1 : ℝ)) (Y i p.2) :=
    measurable_from_prod_countable_right fun c => by
      have := Finset.measurable_sum (Finset.range c) fun i _ =>
        ((measurable_const (a := (1 : ℝ))).indicator hA).comp (hY i)
      exact this
  exact hF.comp (hK.prodMk measurable_id)

theorem measurable_mixedBinomial {K : Ω → ℕ} {Y : ℕ → Ω → S} (hK : Measurable K)
    (hY : ∀ i, Measurable (Y i)) : Measurable (mixedBinomial K Y) := by
  rw [measurable_measure_iff]
  intro A hA
  simp_rw [mixedBinomial_apply K Y _ hA]
  exact ENNReal.measurable_ofReal.comp (measurable_mbCount hK hY hA)

variable {P : Measure Ω} {ν : Measure S} {lam : ℝ≥0} {K : Ω → ℕ} {Y : ℕ → Ω → S}

/-- Fubini and the Poisson series for a bounded multiplicative functional. -/
theorem integral_prod_range [IsProbabilityMeasure P] (hK : Measurable K)
    (hY : ∀ i, Measurable (Y i)) (hKlaw : P.map K = poissonMeasure lam)
    (hYiid : iIndepFun Y P) (hYlaw : ∀ i, P.map (Y i) = ν)
    (hKY : IndepFun K (fun ω i => Y i ω) P) {f : S → ℂ} (hf : Measurable f)
    (hbd : ∀ y, ‖f y‖ ≤ 1) :
    ∫ ω, ∏ i ∈ Finset.range (K ω), f (Y i ω) ∂P = cexp (lam * (∫ y, f y ∂ν - 1)) := by
  have hYseq : Measurable fun ω i => Y i ω := Measurable.of_eval hY
  let G : ℕ × (ℕ → S) → ℂ := fun p => ∏ i ∈ Finset.range p.1, f (p.2 i)
  have hG : Measurable G :=
    measurable_from_prod_countable_right fun c => by
      have := Finset.measurable_prod (Finset.range c) fun i _ =>
        hf.comp (measurable_pi_apply (X := fun _ : ℕ => S) i)
      exact this
  have hGbd : ∀ p, ‖G p‖ ≤ 1 := fun p => by
    simp only [G, norm_prod]
    exact Finset.prod_le_one₀ (fun i _ => norm_nonneg _) fun i _ => hbd _
  have hW : Measurable fun ω => (K ω, fun i => Y i ω) := hK.prodMk hYseq
  have hprod := (indepFun_iff_map_prod_eq_prod_map_map hK.aemeasurable
    hYseq.aemeasurable).1 hKY
  change ∫ ω, G ((fun ω => (K ω, fun i => Y i ω)) ω) ∂P = _
  rw [← integral_map hW.aemeasurable hG.aestronglyMeasurable, hprod]
  have hint : Integrable G ((P.map K).prod (P.map fun ω i => Y i ω)) :=
    Integrable.of_bound hG.aestronglyMeasurable 1 (Filter.Eventually.of_forall hGbd)
  rw [integral_prod _ hint]
  have hinner : ∀ c : ℕ, ∫ y, G (c, y) ∂(P.map fun ω i => Y i ω) =
      (∫ y, f y ∂ν) ^ c := by
    intro c
    have hGc : Measurable fun y : ℕ → S => G (c, y) :=
      hG.comp (measurable_const.prodMk measurable_id)
    rw [integral_map hYseq.aemeasurable hGc.aestronglyMeasurable]
    have hind : iIndepFun (fun (i : Fin c) => Y i) P := hYiid.precomp Fin.val_injective
    have h1 := hind.integral_fun_prod_comp (f := fun _ => f)
      (fun i => (hY i).aemeasurable) (fun i => hf.aestronglyMeasurable)
    have h2 : ∀ i : Fin c, ∫ ω, f (Y i ω) ∂P = ∫ y, f y ∂ν := fun i => by
      rw [← hYlaw i, integral_map (hY i).aemeasurable hf.aestronglyMeasurable]
    calc ∫ ω, G (c, fun i => Y i ω) ∂P = ∫ ω, ∏ i : Fin c, f (Y i ω) ∂P := by
          congr 1; ext ω; exact (Fin.prod_univ_eq_prod_range (fun i => f (Y i ω)) c).symm
      _ = (∫ y, f y ∂ν) ^ c := by
          rw [h1]; simp only [h2, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  simp_rw [hinner, hKlaw]
  exact integral_poissonMeasure_pow lam _

section Main

theorem integral_exp_indicator_sum [IsProbabilityMeasure ν] {n : ℕ} {A : Fin n → Set S}
    (hA : ∀ j, MeasurableSet (A j)) (hd : Pairwise (Function.onFun Disjoint A))
    (t : Fin n → ℝ) :
    ∫ y, cexp ((∑ j, t j * (A j).indicator (fun _ => (1 : ℝ)) y : ℝ) * I) ∂ν =
      1 + ∑ j, (ν.real (A j) : ℂ) * (cexp (t j * I) - 1) := by
  simp_rw [exp_indicator_sum A hd t]
  have hint : ∀ j, Integrable (fun y => (A j).indicator (fun _ => (1 : ℂ)) y *
      (cexp (t j * I) - 1)) ν := fun j => by
    have : (fun y => (A j).indicator (fun _ => (1 : ℂ)) y * (cexp (t j * I) - 1)) =
        (A j).indicator (fun _ => cexp (t j * I) - 1) := by
      ext y; by_cases h : y ∈ A j <;> simp [h]
    rw [this]
    exact (integrable_const _).indicator (hA j)
  rw [integral_add (integrable_const _) (integrable_finsetSum _ fun j _ => hint j),
    integral_finsetSum _ fun j _ => hint j]
  simp only [integral_const, probReal_univ, one_smul]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  have : (fun y => (A j).indicator (fun _ => (1 : ℂ)) y * (cexp (t j * I) - 1)) =
      (A j).indicator (fun _ => cexp (t j * I) - 1) := by
    ext y; by_cases h : y ∈ A j <;> simp [h]
  rw [this, integral_indicator_const _ (hA j), Complex.real_smul]

variable [IsProbabilityMeasure P] [IsProbabilityMeasure ν]

/-- The characteristic function of the count vector. -/
theorem charFunDual_mbCount (hK : Measurable K) (hY : ∀ i, Measurable (Y i))
    (hKlaw : P.map K = poissonMeasure lam) (hYiid : iIndepFun Y P)
    (hYlaw : ∀ i, P.map (Y i) = ν) (hKY : IndepFun K (fun ω i => Y i ω) P)
    {n : ℕ} {A : Fin n → Set S} (hA : ∀ j, MeasurableSet (A j))
    (hd : Pairwise (Function.onFun Disjoint A)) (L : StrongDual ℝ (Fin n → ℝ)) :
    charFunDual (P.map fun ω j => mbCount K Y (A j) ω) L =
      cexp (lam * ∑ j, (ν.real (A j) : ℂ) *
        (cexp ((L fun l => if j = l then 1 else 0) * I) - 1)) := by
  set t : Fin n → ℝ := fun j => L fun l => if j = l then 1 else 0 with ht
  have hC : Measurable fun ω j => mbCount K Y (A j) ω :=
    Measurable.of_eval fun j => measurable_mbCount hK hY (hA j)
  set f : S → ℂ := fun y => cexp ((∑ j, t j * (A j).indicator (fun _ => (1 : ℝ)) y : ℝ) * I)
    with hf
  have hfm : Measurable f := by
    refine Complex.measurable_exp.comp ?_
    refine (Complex.measurable_ofReal.comp ?_).mul_const _
    exact Finset.measurable_sum _ fun j _ => measurable_const.mul
      (measurable_const.indicator (hA j))
  have hbd : ∀ y, ‖f y‖ ≤ 1 := fun y => by
    simp only [hf]
    rw [Complex.norm_exp_ofReal_mul_I]
  rw [charFunDual_apply, integral_map hC.aemeasurable ?_]
  swap
  · exact (Complex.measurable_exp.comp ((Complex.measurable_ofReal.comp
      (L.continuous.measurable)).mul_const _)).aestronglyMeasurable
  have hrew : ∀ ω, cexp (L (fun j => mbCount K Y (A j) ω) * I) =
      ∏ i ∈ Finset.range (K ω), f (Y i ω) := by
    intro ω
    have hL : L (fun j => mbCount K Y (A j) ω) = ∑ j, mbCount K Y (A j) ω • t j :=
      LinearMap.pi_apply_eq_sum_univ (L : (Fin n → ℝ) →ₗ[ℝ] ℝ) _
    have hreal : ∑ j, mbCount K Y (A j) ω • t j =
        ∑ i ∈ Finset.range (K ω), ∑ j, t j * (A j).indicator (fun _ => (1 : ℝ)) (Y i ω) := by
      simp only [mbCount, smul_eq_mul, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => mul_comm _ _
    rw [hL, hreal, hf]
    simp only [← Complex.exp_sum]
    congr 1
    push_cast
    rw [Finset.sum_mul]
  simp_rw [hrew]
  rw [integral_prod_range hK hY hKlaw hYiid hYlaw hKY hfm hbd, hf]
  simp only
  rw [integral_exp_indicator_sum hA hd t]
  congr 2
  ring

/-- Mixed binomial process: the mixed binomial process is `PPP(λ ν)`. -/
theorem isPoissonPointProcess_mixedBinomial (hK : Measurable K) (hY : ∀ i, Measurable (Y i))
    (hKlaw : P.map K = poissonMeasure lam) (hYiid : iIndepFun Y P)
    (hYlaw : ∀ i, P.map (Y i) = ν) (hKY : IndepFun K (fun ω i => Y i ω) P) :
    IsPoissonPointProcess (mixedBinomial K Y) ((lam : ℝ≥0∞) • ν) P := by
  refine IsPoissonPointProcess.mk' (measurable_mixedBinomial hK hY) ?_
  intro n A hA hd
  set p : Fin n → ℝ≥0 := fun j => (ν (A j)).toNNReal with hp
  have hpν : ∀ j, ν (A j) = (p j : ℝ≥0∞) := fun j => (ENNReal.coe_toNNReal (measure_ne_top _ _)).symm
  have hC : Measurable fun ω j => mbCount K Y (A j) ω :=
    Measurable.of_eval fun j => measurable_mbCount hK hY (hA j)
  have hlaw : P.map (fun ω j => mbCount K Y (A j) ω) =
      Measure.pi fun j => (poissonMeasure (lam * p j)).map (Nat.cast : ℕ → ℝ) := by
    refine (charFunDual_eq_pi_iff (E := fun _ : Fin n => ℝ)
      (μ := fun j => (poissonMeasure (lam * p j)).map (Nat.cast : ℕ → ℝ))
      (ν := P.map fun ω j => mbCount K Y (A j) ω)).1 fun L => ?_
    rw [charFunDual_mbCount hK hY hKlaw hYiid hYlaw hKY hA hd L]
    simp_rw [charFunDual_poisson_real]
    rw [← Complex.exp_sum, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    have h1 : (L.comp (ContinuousLinearMap.single ℝ (fun _ : Fin n => ℝ) j)) 1 =
        L fun l => if j = l then 1 else 0 := by
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.single_apply]
      congr 1
      ext l
      simp [Pi.single_apply, eq_comm]
    rw [h1]
    have h2 : ((lam * p j : ℝ≥0) : ℂ) = lam * (ν.real (A j) : ℂ) := by
      simp [hp, Measure.real, ENNReal.toReal]
    rw [h2]
    ring
  have hV : (fun ω j => mixedBinomial K Y ω (A j)) =
      (fun x : Fin n → ℝ => fun j => ENNReal.ofReal (x j)) ∘ fun ω j => mbCount K Y (A j) ω := by
    ext ω j
    exact mixedBinomial_apply K Y ω (hA j)
  have hofReal : Measurable fun x : Fin n → ℝ => fun j => ENNReal.ofReal (x j) :=
    Measurable.of_eval fun j => ENNReal.measurable_ofReal.comp (measurable_pi_apply j)
  rw [hV, ← Measure.map_map hofReal hC, hlaw,
    Measure.pi_map_pi (f := fun _ => ENNReal.ofReal)
      (fun _ => ENNReal.measurable_ofReal.aemeasurable)]
  congr 1
  funext j
  rw [Measure.map_map ENNReal.measurable_ofReal measurable_from_top]
  have hc : ENNReal.ofReal ∘ (Nat.cast : ℕ → ℝ) = (Nat.cast : ℕ → ℝ≥0∞) := by
    ext n; simp
  rw [hc, ← extPoissonMeasure_coe]
  congr 1
  rw [Measure.smul_apply, hpν j, smul_eq_mul, ENNReal.coe_mul]

end Main

end ElboimSly
