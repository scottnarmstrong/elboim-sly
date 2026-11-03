/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.StrongApprox.ChernoffMgf
public import Mathlib

/-!
# Chernoff bound for the clocks

Chernoff bound for the clocks (Part II).

Let `τ_1, …, τ_ℓ` be independent, nonnegative, with mean `1` and `E exp(τ_i/(36M²)) ≤ 8`. Then
for `0 < γ ≤ 2ℓ`,
`P(∃ j, |∑_{i ≤ j} (τ_i - 1)| ≥ 215 M² √(ℓγ)) ≤ 2ℓ e^{-γ}`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ElboimSly.StrongApprox

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- One-sided tail of a partial sum. -/
lemma tail_partial_sum {ℓ : ℕ} {M : ℝ} (hM : 1 ≤ M) {τ : Fin ℓ → Ω → ℝ}
    (hm : ∀ i, Measurable (τ i)) (hind : iIndepFun τ P) (hnn : ∀ i ω, 0 ≤ τ i ω)
    (hmean : ∀ i, ∫ ω, τ i ω ∂P = 1)
    (hexp : ∀ i, ∫⁻ ω, ENNReal.ofReal (Real.exp (τ i ω / (36 * M ^ 2))) ∂P ≤ 8)
    {u : ℝ} (hu : |u| ≤ 1 / (72 * M ^ 2)) (s : Finset (Fin ℓ)) :
    Integrable (fun ω => Real.exp (u * (∑ i ∈ s, fun ω => τ i ω - 1) ω)) P ∧
      mgf (∑ i ∈ s, fun ω => τ i ω - 1) P u ≤ Real.exp (11500 * u ^ 2 * M ^ 4) ^ s.card := by
  have hind' : iIndepFun (fun i ω => τ i ω - 1) P :=
    hind.comp (fun _ x => x - 1) (fun _ => measurable_id.sub_const 1)
  have hm' : ∀ i, Measurable (fun ω => τ i ω - 1) := fun i => (hm i).sub_const 1
  have hmg := fun i => mgf_clock_le hM (hm i) (hnn i) (hexp i) (hmean i) hu
  refine ⟨hind'.integrable_exp_mul_sum hm' (fun i _ => (hmg i).1), ?_⟩
  rw [hind'.mgf_sum hm' s]
  calc ∏ i ∈ s, mgf (fun ω => τ i ω - 1) P u
      ≤ ∏ _i ∈ s, Real.exp (11500 * u ^ 2 * M ^ 4) :=
        Finset.prod_le_prod₀ (fun i _ => integral_nonneg fun ω => (Real.exp_pos _).le)
          (fun i _ => (hmg i).2)
    _ = Real.exp (11500 * u ^ 2 * M ^ 4) ^ s.card := by rw [Finset.prod_const]

/-- Chernoff bound for the clocks. -/
theorem chernoff_clock {ℓ : ℕ} (hℓ : 1 ≤ ℓ) {M : ℝ} (hM : 1 ≤ M) {τ : Fin ℓ → Ω → ℝ}
    (hm : ∀ i, Measurable (τ i)) (hind : iIndepFun τ P) (hnn : ∀ i ω, 0 ≤ τ i ω)
    (hmean : ∀ i, ∫ ω, τ i ω ∂P = 1)
    (hexp : ∀ i, ∫⁻ ω, ENNReal.ofReal (Real.exp (τ i ω / (36 * M ^ 2))) ∂P ≤ 8)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ : γ ≤ 2 * ℓ) :
    P {ω | ∃ j : Fin ℓ, 215 * M ^ 2 * Real.sqrt (ℓ * γ) ≤
        |∑ i ∈ Finset.univ.filter (· ≤ j), (τ i ω - 1)|} ≤
      ENNReal.ofReal (2 * ℓ * Real.exp (-γ)) := by
  have hL : (0 : ℝ) < ℓ := by exact_mod_cast hℓ
  have hM2 : 0 < M ^ 2 := by positivity
  set sq : ℝ := Real.sqrt (γ / (11500 * ℓ)) with hsq
  set u : ℝ := sq / M ^ 2 with hu
  set a : ℝ := 2 * M ^ 2 * Real.sqrt (11500 * ℓ * γ) with ha
  have hsq0 : 0 ≤ sq := Real.sqrt_nonneg _
  have hsq_le : sq ≤ 1 / 72 := by
    rw [hsq, show (1 / 72 : ℝ) = Real.sqrt ((1 / 72) ^ 2) by
      rw [Real.sqrt_sq (by norm_num)]]
    apply Real.sqrt_le_sqrt
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hu0 : 0 ≤ u := by positivity
  have hu_le : |u| ≤ 1 / (72 * M ^ 2) := by
    rw [abs_of_nonneg hu0, hu, div_le_div_iff₀ hM2 (by positivity)]
    nlinarith
  have hprod : sq * Real.sqrt (11500 * ℓ * γ) = γ := by
    rw [hsq, ← Real.sqrt_mul (by positivity)]
    have : γ / (11500 * ℓ) * (11500 * ℓ * γ) = γ ^ 2 := by field_simp
    rw [this, Real.sqrt_sq hγ0.le]
  have hua : u * a = 2 * γ := by
    rw [hu, ha]
    calc sq / M ^ 2 * (2 * M ^ 2 * Real.sqrt (11500 * ℓ * γ))
        = 2 * (sq * Real.sqrt (11500 * ℓ * γ)) := by field_simp
      _ = 2 * γ := by rw [hprod]
  have hc : 11500 * u ^ 2 * M ^ 4 * ℓ = γ := by
    have : u ^ 2 * M ^ 4 = sq ^ 2 := by rw [hu]; field_simp
    calc 11500 * u ^ 2 * M ^ 4 * ℓ = 11500 * ℓ * (u ^ 2 * M ^ 4) := by ring
      _ = 11500 * ℓ * sq ^ 2 := by rw [this]
      _ = γ := by
        rw [hsq, Real.sq_sqrt (by positivity)]; field_simp
  have hcnn : 0 ≤ 11500 * u ^ 2 * M ^ 4 := by positivity
  have hexp1 : 1 ≤ Real.exp (11500 * u ^ 2 * M ^ 4) := Real.one_le_exp hcnn
  -- tail bounds for each `j`
  have htail : ∀ j : Fin ℓ,
      P.real {ω | a ≤ (∑ i ∈ Finset.univ.filter (· ≤ j), fun ω => τ i ω - 1) ω} ≤
          Real.exp (-γ) ∧
      P.real {ω | (∑ i ∈ Finset.univ.filter (· ≤ j), fun ω => τ i ω - 1) ω ≤ -a} ≤
          Real.exp (-γ) := by
    intro j
    set F := Finset.univ.filter (· ≤ j) with hF
    have hcard : F.card ≤ ℓ := by
      calc F.card ≤ (Finset.univ : Finset (Fin ℓ)).card := Finset.card_le_univ _
        _ = ℓ := by simp
    have hpow : Real.exp (11500 * u ^ 2 * M ^ 4) ^ F.card ≤
        Real.exp (11500 * u ^ 2 * M ^ 4) ^ ℓ := pow_le_pow_right₀ hexp1 hcard
    have e1 : Real.exp (11500 * u ^ 2 * M ^ 4) ^ ℓ = Real.exp γ := by
      rw [← Real.exp_nat_mul, ← hc]; congr 1; ring
    obtain ⟨hint1, hmgf1⟩ := tail_partial_sum hM hm hind hnn hmean hexp hu_le F
    have hu_le' : |-u| ≤ 1 / (72 * M ^ 2) := by rwa [abs_neg]
    obtain ⟨hint2, hmgf2⟩ := tail_partial_sum hM hm hind hnn hmean hexp hu_le' F
    constructor
    · have h := measure_ge_le_exp_mul_mgf (μ := P) (X := ∑ i ∈ F, fun ω => τ i ω - 1) a hu0 hint1
      refine h.trans ?_
      calc Real.exp (-u * a) * mgf (∑ i ∈ F, fun ω => τ i ω - 1) P u
          ≤ Real.exp (-u * a) * Real.exp γ := by
            gcongr
            exact hmgf1.trans (hpow.trans e1.le)
        _ = Real.exp (-γ) := by
            rw [← Real.exp_add]; congr 1; rw [neg_mul, hua]; ring
    · have h := measure_le_le_exp_mul_mgf (μ := P) (X := ∑ i ∈ F, fun ω => τ i ω - 1) (-a)
        (neg_nonpos.2 hu0) hint2
      refine h.trans ?_
      calc Real.exp (-(-u) * -a) * mgf (∑ i ∈ F, fun ω => τ i ω - 1) P (-u)
          ≤ Real.exp (-(-u) * -a) * Real.exp γ := by
            gcongr
            exact hmgf2.trans (by
              have : (-u) ^ 2 = u ^ 2 := by ring
              rw [this]; exact hpow.trans e1.le)
        _ = Real.exp (-γ) := by
            rw [← Real.exp_add]; congr 1
            have : -(-u) * -a = -(u * a) := by ring
            rw [this, hua]; ring
  -- the union bound
  have hA_le : a ≤ 215 * M ^ 2 * Real.sqrt (ℓ * γ) := by
    have h1 : Real.sqrt 11500 ≤ 107.5 := Real.sqrt_le_iff.2 ⟨by norm_num, by norm_num⟩
    have h2 : Real.sqrt (11500 * ℓ * γ) = Real.sqrt 11500 * Real.sqrt (ℓ * γ) := by
      rw [mul_assoc, Real.sqrt_mul (by norm_num)]
    rw [ha, h2]
    have h3 : 0 ≤ Real.sqrt (ℓ * γ) := Real.sqrt_nonneg _
    nlinarith [mul_nonneg (sq_nonneg M) h3, mul_nonneg h3 (sq_nonneg M)]
  set S : Fin ℓ → Ω → ℝ := fun j => ∑ i ∈ Finset.univ.filter (· ≤ j), fun ω => τ i ω - 1 with hS
  have hcov : {ω | ∃ j : Fin ℓ, 215 * M ^ 2 * Real.sqrt (ℓ * γ) ≤
        |∑ i ∈ Finset.univ.filter (· ≤ j), (τ i ω - 1)|} ⊆
      ⋃ j : Fin ℓ, ({ω | a ≤ S j ω} ∪ {ω | S j ω ≤ -a}) := by
    rintro ω ⟨j, hj⟩
    refine Set.mem_iUnion.2 ⟨j, ?_⟩
    have hsum : S j ω = ∑ i ∈ Finset.univ.filter (· ≤ j), (τ i ω - 1) := by
      simp [hS, Finset.sum_apply]
    have := hA_le.trans hj
    rw [← hsum] at this
    rcases le_abs'.1 this with h | h
    · exact Or.inr h
    · exact Or.inl h
  have hPA : ∀ j : Fin ℓ, P {ω | a ≤ S j ω} ≤ ENNReal.ofReal (Real.exp (-γ)) := fun j => by
    rw [ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) (Real.exp_pos _).le]
    exact (htail j).1
  have hPB : ∀ j : Fin ℓ, P {ω | S j ω ≤ -a} ≤ ENNReal.ofReal (Real.exp (-γ)) := fun j => by
    rw [ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) (Real.exp_pos _).le]
    exact (htail j).2
  calc P _ ≤ P (⋃ j : Fin ℓ, ({ω | a ≤ S j ω} ∪ {ω | S j ω ≤ -a})) := measure_mono hcov
    _ ≤ ∑ j : Fin ℓ, P ({ω | a ≤ S j ω} ∪ {ω | S j ω ≤ -a}) := measure_iUnion_fintype_le _ _
    _ ≤ ∑ _j : Fin ℓ, (ENNReal.ofReal (Real.exp (-γ)) + ENNReal.ofReal (Real.exp (-γ))) := by
        refine Finset.sum_le_sum fun j _ => ?_
        exact (measure_union_le _ _).trans (add_le_add (hPA j) (hPB j))
    _ = ENNReal.ofReal (2 * ℓ * Real.exp (-γ)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          ← two_mul, ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num),
          ← ENNReal.ofReal_natCast ℓ, ← ENNReal.ofReal_mul (by positivity)]
        congr 1; ring

end ElboimSly.StrongApprox
