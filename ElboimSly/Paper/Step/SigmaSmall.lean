/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Step.SigmaSrw
public import ElboimSly.Paper.Step.BlockSym
public import ElboimSly.Paper.Step.TravelLaw
public import ElboimSly.Foundations.PPP.Existence
public import Mathlib

/-!
# The `σ`-estimate for short blocks (the σ-estimate, Case 2)

The σ-estimate, Case 2: for `T ≤ β`, `W = X` on `[0,T]` (the driven regenerated walk (c)),
so `T σ² = E[𝟙_𝒜 X^{(1)}(T)²] = 2T - E[𝟙_{𝒜ᶜ} X^{(1)}(T)²]`, and with `E X^{(1)}(T)⁴ ≤ 355 T²`
(`srw_coord_fourth`) and `ℙ(𝒜ᶜ) ≤ p`, `2 - √(355 p) ≤ σ² ≤ 2` (`sigma_sq_small`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set ElboimSly.Cyclic ElboimSly.SRW
open scoped NNReal ENNReal

namespace ElboimSly.Paper.Step

open ElboimSly.Paper

variable {d : ℕ} {β : ℝ} [Fact (0 < β)]

theorem blockY_stop (T : ℝ≥0) (K : ℝ) (w : ℝ≥0 → Fin d → ℤ) :
    blockY T K (SRW.stopPath T w) = blockY T K w := by
  unfold blockY; rw [truncEnd_stop]

theorem sigma_sq_small (hd : 1 ≤ d) {n₁ n : ℕ} {t₀ : ℝ} (_hR : StepRegime d n₁ β n t₀)
    {Ωe : Type} [MeasurableSpace Ωe] {Pe : Measure Ωe} {N : Ωe → Measure (ℕ × RingSpace d β)}
    (hN : IsPoissonPointProcess N ((Measure.count : Measure ℕ).prod (ringIntensity d β)) Pe)
    {T : ℝ≥0} (hT1 : 1 ≤ (T : ℝ)) (hTβ : (T : ℝ) ≤ β) {K p : ℝ} (hp : 0 < p)
    (hFar : Pe.real {ω | ∃ s : ℝ≥0, (s : ℝ) ≤ T ∧
      K ≤ ‖regenWalk (fun j => copyEnv (N ω) j) (s : ℝ)‖} ≤ p) :
    2 - Real.sqrt (355 * p) ≤ (∫ w, (blockY T K w ⟨0, hd⟩) ^ 2 ∂ppLaw Pe N T) ∧
      (∫ w, (blockY T K w ⟨0, hd⟩) ^ 2 ∂ppLaw Pe N T) ≤ 2 := by
  have hPe := hN.isProbabilityMeasure
  obtain ⟨Ω', _, P', N₀, hP', hN₀, -⟩ := exists_isPoissonPointProcess (clockIntensity (Dir d))
  have hY : IsSRW P' (canonical d N₀) := canonical_isSRW hN₀
  have hYp : ∀ ω, canonical d N₀ ω ∈ StepPath d := fun ω => walkPath_isDriving (N₀ ω)
  have hP'prob : IsProbabilityMeasure P' := hY.isProbabilityMeasure
  set Y := canonical d N₀ with hYdef
  set s : ℕ → ℝ≥0 := fun _ => T with hs
  have hT0 : (0 : ℝ) < T := by linarith
  set i0 : Fin d := ⟨0, hd⟩ with hi0
  set f : (ℝ≥0 → Fin d → ℤ) → ℝ := fun w => (blockY T K w i0) ^ 2 with hf
  have hfm : Measurable f :=
    (((measurable_pi_apply i0).comp (measurable_blockY T K))).pow_const 2
  have hW := measurable_stepWj (β := β) hY hYp 0 s 0
  have hlaw := map_stepWj_ppLaw (β := β) hY hYp hN 0 s 0
  have e1 : ∫ w, f w ∂ppLaw Pe N T = ∫ ω, f (stepWj β 0 s (Y ω) 0) ∂P' := by
    have : ppLaw Pe N T = P'.map (fun ω => stepWj β 0 s (Y ω) 0) := hlaw.symm
    rw [this, integral_map hW.aemeasurable hfm.aestronglyMeasurable]
  have hTβ' : T ≤ β.toNNReal := (Real.le_toNNReal_iff_coe_le (Fact.out : 0 < β).le).2 hTβ
  have hae : ∀ᵐ ω ∂P', stepWj β 0 s (Y ω) 0 = SRW.stopPath T (Y ω) := by
    filter_upwards [ae_stepShift_mem_stepCF (β := β) hN₀ 0] with ω hω
    funext u
    have hcf := (stepReg_no_interaction hω).2
    have h0 : stepShift 0 (Y ω) = Y ω := shiftPath_zero (hYp ω)
    have hP0 : stepPartial s 0 = 0 := by simp [stepPartial]
    have hmin : min u T ≤ β.toNNReal := (min_le_right _ _).trans hTβ'
    have := hcf (min u T) hmin
    rw [h0] at this
    show stepReg β (stepShift (0 + stepPartial s 0) (Y ω)) (min u (s 0)) = Y ω (min u T)
    rw [hP0, zero_add, h0]
    exact this
  have e2 : ∫ ω, f (stepWj β 0 s (Y ω) 0) ∂P' = ∫ ω, f (Y ω) ∂P' := by
    refine integral_congr_ae ?_
    filter_upwards [hae] with ω hω
    simp only [hf]
    rw [hω, blockY_stop]
  set Z : Ω' → ℝ := fun ω => (Y ω T i0 : ℝ) with hZ
  have hZm : Measurable Z := (measurable_eval_real T i0).comp hY.1
  obtain ⟨hI4, hE4⟩ := srw_coord_fourth hY i0 hT1
  have hI4' : Integrable (fun ω => Z ω ^ 4) P' := hI4
  have hZ2int : Integrable (fun ω => Z ω ^ 2) P' := by
    refine Integrable.mono' ((integrable_const (1 : ℝ)).add hI4')
      (hZm.pow_const 2).aestronglyMeasurable (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_of_nonneg (by positivity)]
    show Z ω ^ 2 ≤ 1 + Z ω ^ 4
    nlinarith [sq_nonneg (Z ω ^ 2 - 1), sq_nonneg (Z ω ^ 2)]
  have hEZ2 : ∫ ω, Z ω ^ 2 ∂P' = 2 * T := by
    have := hY.integral_eval_mul T i0 i0
    simpa [pow_two, hZ] using this
  set F : Set Ω' := {ω | Y ω ∈ farSet K T} with hF
  have hFm : MeasurableSet F := (measurableSet_farSet K T).preimage hY.1
  have hgsq : ∀ ω, f (Y ω) = (T : ℝ)⁻¹ * (Z ω ^ 2 - F.indicator (fun ω => Z ω ^ 2) ω) := by
    intro ω
    have hsq : ((Real.sqrt (T : ℝ))⁻¹) ^ 2 = (T : ℝ)⁻¹ := by
      rw [inv_pow, Real.sq_sqrt hT0.le]
    by_cases hω : Y ω ∈ farSet K T
    · have hωF : ω ∈ F := hω
      simp [hf, blockY, truncEnd, hω, Set.indicator_of_mem hωF]
    · have hωF : ω ∉ F := hω
      simp [hf, blockY, truncEnd, hω, Set.indicator_of_notMem hωF, mul_pow, hZ, i0]
  -- the probability of the truncation event
  have hFP : P'.real F ≤ p := by
    have hset : F =ᵐ[P'] {ω | stepWj β 0 s (Y ω) 0 ∈ farSet K T} := by
      filter_upwards [hae] with ω hω
      show (Y ω ∈ farSet K T) = (stepWj β 0 s (Y ω) 0 ∈ farSet K T)
      rw [hω, stopPath_mem_farSet]
    rw [Measure.real, measure_congr hset, measure_stepWj_farSet hY hYp hN 0 T K 0]
    refine le_trans ?_ hFar
    rw [Measure.real]
    refine ENNReal.toReal_mono (measure_ne_top _ _) ?_
    refine (ppLaw_tail hN T K).trans (le_of_eq ?_)
    congr 1
  -- the AM-GM bound
  have hind_int : Integrable (F.indicator fun ω => Z ω ^ 2) P' := hZ2int.indicator hFm
  have hind_nn : 0 ≤ ∫ ω, F.indicator (fun ω => Z ω ^ 2) ω ∂P' :=
    integral_nonneg fun ω => Set.indicator_nonneg (fun ω _ => by positivity) ω
  have hind_le : ∫ ω, F.indicator (fun ω => Z ω ^ 2) ω ∂P' ≤ Real.sqrt 355 * T * Real.sqrt p := by
    set a : ℝ := Real.sqrt 355 * T / Real.sqrt p with ha
    have hsp : 0 < Real.sqrt p := Real.sqrt_pos.2 hp
    have hs355 : 0 < Real.sqrt 355 := Real.sqrt_pos.2 (by norm_num)
    have ha0 : 0 < a := by rw [ha]; positivity
    have hpt : ∀ ω, F.indicator (fun ω => Z ω ^ 2) ω ≤
        (a * F.indicator (fun _ => (1 : ℝ)) ω + Z ω ^ 4 / a) / 2 := by
      intro ω
      by_cases hω : ω ∈ F
      · simp only [Set.indicator_of_mem hω]
        have h1 : a + Z ω ^ 4 / a - 2 * Z ω ^ 2 = (a - Z ω ^ 2) ^ 2 / a := by
          field_simp; ring
        have h2 : 0 ≤ (a - Z ω ^ 2) ^ 2 / a := by positivity
        rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
        linarith
      · simp only [Set.indicator_of_notMem hω]
        have : 0 ≤ Z ω ^ 4 / a := by positivity
        linarith
    have hint2 : Integrable (fun ω => (a * F.indicator (fun _ => (1 : ℝ)) ω + Z ω ^ 4 / a) / 2) P' := by
      have h1 : Integrable (F.indicator fun _ => (1 : ℝ)) P' :=
        (integrable_const (1 : ℝ)).indicator hFm
      exact ((h1.const_mul a).add (hI4'.div_const a)).div_const 2
    calc ∫ ω, F.indicator (fun ω => Z ω ^ 2) ω ∂P'
        ≤ ∫ ω, (a * F.indicator (fun _ => (1 : ℝ)) ω + Z ω ^ 4 / a) / 2 ∂P' :=
          integral_mono hind_int hint2 hpt
      _ = (a * P'.real F + (∫ ω, Z ω ^ 4 ∂P') / a) / 2 := by
          rw [integral_div, integral_add ((integrable_const (1 : ℝ)).indicator hFm |>.const_mul a)
            (hI4'.div_const a), integral_const_mul, integral_div, integral_indicator_const (1 : ℝ) hFm,
            smul_eq_mul, mul_one]
      _ ≤ (a * p + 355 * (T : ℝ) ^ 2 / a) / 2 := by
          have h1 : a * P'.real F ≤ a * p := mul_le_mul_of_nonneg_left hFP ha0.le
          have h2 : (∫ ω, Z ω ^ 4 ∂P') / a ≤ 355 * (T : ℝ) ^ 2 / a :=
            div_le_div_of_nonneg_right hE4 ha0.le
          linarith
      _ = Real.sqrt 355 * T * Real.sqrt p := by
          rw [ha]
          have hp2 : Real.sqrt p ^ 2 = p := Real.sq_sqrt hp.le
          have h3 : Real.sqrt 355 ^ 2 = 355 := Real.sq_sqrt (by norm_num)
          field_simp
          nlinarith
  have hV : ∫ w, f w ∂ppLaw Pe N T = (T : ℝ)⁻¹ * (2 * T - ∫ ω, F.indicator (fun ω => Z ω ^ 2) ω ∂P') := by
    rw [e1, e2]
    simp_rw [hgsq]
    rw [integral_const_mul, integral_sub hZ2int hind_int, hEZ2]
  have hTinv : (T : ℝ)⁻¹ * (2 * T) = 2 := by field_simp
  have hTpos : 0 < (T : ℝ)⁻¹ := inv_pos.2 hT0
  refine ⟨?_, ?_⟩
  · show 2 - Real.sqrt (355 * p) ≤ ∫ w, f w ∂ppLaw Pe N T
    rw [hV, mul_sub, hTinv]
    have h1 : (T : ℝ)⁻¹ * (∫ ω, F.indicator (fun ω => Z ω ^ 2) ω ∂P') ≤
        (T : ℝ)⁻¹ * (Real.sqrt 355 * T * Real.sqrt p) :=
      mul_le_mul_of_nonneg_left hind_le hTpos.le
    have h2 : (T : ℝ)⁻¹ * (Real.sqrt 355 * T * Real.sqrt p) = Real.sqrt (355 * p) := by
      rw [Real.sqrt_mul (by norm_num)]; field_simp
    linarith
  · show ∫ w, f w ∂ppLaw Pe N T ≤ 2
    rw [hV, mul_sub, hTinv]
    have : 0 ≤ (T : ℝ)⁻¹ * (∫ ω, F.indicator (fun ω => Z ω ^ 2) ω ∂P') :=
      mul_nonneg hTpos.le hind_nn
    linarith

end ElboimSly.Paper.Step
