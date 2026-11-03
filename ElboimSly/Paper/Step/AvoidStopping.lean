/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Step.AvoidIndep
public import ElboimSly.Paper.Step.StopHit2
public import ElboimSly.Paper.Step.Regime
public import ElboimSly.Paper.Step.RelaxedStoppingApp
public import ElboimSly.Paper.Avoid.CoreMain
public import ElboimSly.Paper.Avoid.Lem41Meas
public import Mathlib

/-!
# Lemma 4.1 at stopping times of the driving filtration

ES22 Lemma 4.1 (ES22 Lemma 4.1 as used at ES22 §7).

Let `Y` be an SRW with driving paths, `F` an admissible filtration, `a ≥ 0`, `W = W_reg^{θ_a Y}`,
`𝒢_t = F_{a+t}` and `S` a `𝒢`-stopping time. For `G ∈ 𝒢_S` with `G ⊆ {S < ∞, S ∈ 𝒯(W)}`,
`P(G ∩ {thit(S) ≥ S + 4ⁿ}) ≥ (1 - C β^{-δ/30}) P(G)`, equivalently
`P(G ∩ {thit(S) < S + 4ⁿ}) ≤ C β^{-δ/30} P(G)` (`step_avoid_stopping_lt`).

The proof applies `es4_1_core` with `ℋ = 𝒢_S`, `a = α(S)`, `T = S`, `w = W` and `X = W_reg^{θ_{a+S}Y}`,
which is independent of `𝒢_S` under `P(· | S < ∞)` with the law of the regenerated walk
(`AvoidIndep`); the pathwise step is `ofReal_add_le_stepThit`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology ElboimSly.Cyclic ElboimSly.SRW
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Step

open ElboimSly.Paper

variable {d : ℕ}

theorem stepAlpha_le {β : ℝ} [Fact (0 < β)] {x : ℝ≥0 → Fin d → ℤ} (hx : x ∈ StepPath d)
    (t : ℝ≥0) : stepAlpha β x t ≤ t := by
  obtain ⟨⟨m, hm, hmt, -⟩, -⟩ := stepAlpha_spec (β := β) hx t
  rw [hm]; exact hmt

theorem stepAr_le {β : ℝ} [Fact (0 < β)] {Ω : Type*} {Y : Ω → PathSpace d}
    (hYp : ∀ ω, Y ω ∈ StepPath d) (a : ℝ≥0) (ω : Ω) (t : ℝ≥0) :
    stepAr β a Y ω (t : ℝ) ≤ (t : ℝ) := by
  have := stepAlpha_le (β := β) (stepShift_mem (hYp ω) a) t
  simp only [stepAr, Real.toNNReal_coe]
  exact_mod_cast this

/-- The regime gives (S1)-(S2) of standing assumptions and the setting of S4--S5 once `β ≥ max {10^14, 4^{n₁+2}}`. -/
theorem es4Params_of_stepRegime {n₁ n : ℕ} {β : ℝ} [Fact (0 < β)] {t₀ : ℝ} (hd : 5 ≤ d)
    (hreg : StepRegime d n₁ β n t₀) (h14 : (10 : ℝ) ^ 14 ≤ β) (h4 : (4 : ℝ) ^ (n₁ + 2) ≤ β) :
    Es4Params d β n₁ n t₀ := by
  obtain ⟨h8, -, -, ht0, hβt, hind⟩ := hreg
  refine ⟨hd, h8, ?_, h14, ht0.1, ht0.2, hβt, fun n' h1 h2 t' h3 h4 => hind n' h1 h2 t' ⟨h3, h4⟩⟩
  by_contra hle
  rw [not_lt] at hle
  have h1 : (4 : ℝ) ^ n * 4 ≤ (4 : ℝ) ^ (n₁ + 1) := by
    rw [← pow_succ]; exact pow_le_pow_right₀ (by norm_num) (by omega)
  have h2 : indScale t₀ n ≤ (4 : ℝ) ^ n * 4 := by
    unfold indScale; nlinarith [ht0.2, pow_pos (by norm_num : (0 : ℝ) < 4) n]
  have h3 : (4 : ℝ) ^ (n₁ + 1) < (4 : ℝ) ^ (n₁ + 2) :=
    pow_lt_pow_right₀ (by norm_num) (by omega)
  linarith

variable {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {Y : Ω → PathSpace d}
  {F : ℝ≥0 → MeasurableSpace Ω}

theorem stepTr_eq {Ω : Type*} {S : Ω → WithTop ℝ≥0} {ω : Ω} {t : ℝ≥0} (h : S ω = t) :
    stepTr S ω = (t : ℝ) := by
  unfold stepTr stopReal
  rw [h]
  rfl

theorem stepXat_eq {β : ℝ} [Fact (0 < β)] {Ω : Type*} [MeasurableSpace Ω] {Y : Ω → PathSpace d} (a : ℝ≥0)
    {S : Ω → WithTop ℝ≥0} {ω : Ω} {t : ℝ≥0} (h : S ω = t) :
    stepXat β a Y S ω = stepReg β (stepShift t (stepShift a (Y ω))) := by
  have hR : stepShiftStop a S ω ≠ ⊤ :=
    ne_of_lt ((stepShiftStop_lt_top_iff a S ω).2 (by rw [h]; exact WithTop.coe_lt_top t))
  unfold stepXat thetaAt
  rw [ite_eq_right hR, stopReal_stepShiftStop h]
  have : SRW.theta (t + a) (Y ω) = stepShift t (stepShift a (Y ω)) := by
    show shiftPath (Y ω) (t + a) = shiftPath (shiftPath (Y ω) a) t
    rw [shiftPath_add, add_comm]
  rw [this]

/-- **ES22 Lemma 4.1** (lower-bound form): Lemma 4.1 at stopping times of the driving
filtration. -/
theorem step_avoid_stopping (hd : 5 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ n₁ : ℕ, ∃ β41 : ℝ, ∀ (β : ℝ) [Fact (0 < β)] (n : ℕ) (t₀ : ℝ),
      β41 ≤ β → StepRegime d n₁ β n t₀ →
      ∀ {Ω : Type} [_mΩ : MeasurableSpace Ω] {P : Measure Ω} {Y : Ω → PathSpace d},
        IsSRW P Y → (∀ ω, Y ω ∈ StepPath d) →
        ∀ {F : ℝ≥0 → MeasurableSpace Ω} (hF : IsAdmissible P Y F) (a : ℝ≥0)
          {S : Ω → WithTop ℝ≥0} (hS : IsStoppingTime (stepShiftFilt hF a) S) {G : Set Ω},
          MeasurableSet[hS.measurableSpace] G →
          (∀ ω ∈ G, ∃ t : ℝ≥0, S ω = t ∧
            (t : ℝ) ∈ stepRelaxedSet β (stepWr β a Y ω) (stepAr β a Y ω)) →
          ENNReal.ofReal (1 - C * β ^ (-indDelta d / 30)) * P G ≤
            P (G ∩ {ω | ∀ t : ℝ≥0, S ω = t →
              ENNReal.ofReal ((t : ℝ) + (4 : ℝ) ^ n) ≤
                stepThit β (stepWr β a Y ω) (stepAr β a Y ω) (t : ℝ)}) := by
  obtain ⟨C, hC, H0⟩ := es4_1_core hd
  refine ⟨C, hC, fun n₁ => ?_⟩
  obtain ⟨β41, H1⟩ := H0 n₁
  refine ⟨max β41 (max ((10 : ℝ) ^ 14) ((4 : ℝ) ^ (n₁ + 2))), ?_⟩
  intro β _ n t₀ hβ hreg Ω mΩ P Y hY hYp F hF a S hS G hG hGrel
  have hβ41 : β41 ≤ β := (le_max_left _ _).trans hβ
  have hβ14 : (10 : ℝ) ^ 14 ≤ β := ((le_max_left _ _).trans (le_max_right _ _)).trans hβ
  have hβ4 : (4 : ℝ) ^ (n₁ + 2) ≤ β := ((le_max_right _ _).trans (le_max_right _ _)).trans hβ
  have hp := es4Params_of_stepRegime hd hreg hβ14 hβ4
  have hPprob : IsProbabilityMeasure P := hY.isProbabilityMeasure
  have hfin := measurableSet_finS hS
  have hGfin : ∀ ω ∈ G, S ω < ⊤ := by
    intro ω hω
    obtain ⟨t, ht, -⟩ := hGrel ω hω
    rw [ht]; exact WithTop.coe_lt_top t
  by_cases hne : P {ω | S ω < ⊤} = 0
  · have : P G = 0 := measure_mono_null (fun ω hω => hGfin ω hω) hne
    simp [this]
  have hne' : P {ω | S ω < ⊤} ≠ ⊤ := measure_ne_top _ _
  have : IsProbabilityMeasure (P[|{ω | S ω < ⊤}]) := cond_isProbabilityMeasure hne
  -- the environment
  obtain ⟨Ω₀, mΩ₀, Pr₀, N₀, hPr₀, hN₀, -⟩ := exists_isPoissonPointProcess (cycIntensity ℕ d β)
  -- the data of the core lemma
  set Pr' := P[|{ω | S ω < ⊤}] with hPr'
  have hXm := measurable_stepXat (β := β) hY hYp hF a hS
  have hXr := isRegPath_stepXat (β := β) hYp a S
  have hcore := H1 β n t₀ hβ41 hp Pr₀ N₀ hN₀ hS.measurableSpace hS.measurableSpace_le Pr'
    (fun ω => stepAr β a Y ω (stepTr S ω)) (stepTr S) (stepWr β a Y) (stepXat β a Y S)
    (fun ω => stepAr_le hYp a ω _) (measurable_stepAlphaStop hF hYp a hS)
    (measurable_stepTr hF a hS) (measurable_stepHist hF hYp a hS) ?_ (hXm) (fun ω => (hXr ω).rc)
    (stepAvoid_indep hY hYp hF a hS hne) ?_
  · obtain ⟨-, hcore2⟩ := hcore
    have hrel : ∀ ω ∈ G, IsRelaxedTimeWrt β (stepWr β a Y ω) (stepAr β a Y ω (stepTr S ω))
        (stepTr S ω) := by
      intro ω hω
      obtain ⟨t, ht, hrel⟩ := hGrel ω hω
      rw [stepTr_eq ht]; exact hrel.2
    have hAR := hcore2 (A := G) hG hrel
    have hsub : G ⊆ {ω | S ω < ⊤} := fun ω hω => hGfin ω hω
    have hPG : Pr' G = (P {ω | S ω < ⊤})⁻¹ * P G := by
      rw [hPr', cond_apply hfin, inter_eq_right.2 hsub]
    have hP2 : Pr' (G ∩ {ω | ENNReal.ofReal ((4 : ℝ) ^ n) ≤ hitTime β (stepWr β a Y ω)
        (stepAr β a Y ω (stepTr S ω)) (stepTr S ω) (fun r => stepWr β a Y ω (stepTr S ω) +
          stepXat β a Y S ω r.toNNReal)}) ≤
        (P {ω | S ω < ⊤})⁻¹ * P (G ∩ {ω | ∀ t : ℝ≥0, S ω = t →
          ENNReal.ofReal ((t : ℝ) + (4 : ℝ) ^ n) ≤
            stepThit β (stepWr β a Y ω) (stepAr β a Y ω) (t : ℝ)}) := by
      rw [hPr', cond_apply hfin]
      refine mul_le_mul' le_rfl (measure_mono_ae ?_)
      filter_upwards [ae_stepShift_mem_stepCF_of_isSRW (β := β) hY hYp a] with ω hCF hω
      obtain ⟨-, hωG, hωhit⟩ := hω
      refine ⟨hωG, fun t ht => ?_⟩
      have hT := stepTr_eq ht
      have hA : stepAr β a Y ω (t : ℝ) = (stepAlpha β (stepShift a (Y ω)) t : ℝ) := by
        simp [stepAr]
      have hrel' := hrel ω hωG
      rw [hT, hA] at hrel'
      have hhit : ENNReal.ofReal ((4 : ℝ) ^ n) ≤ hitTime β (stepWr β a Y ω)
          (stepAr β a Y ω (stepTr S ω)) (stepTr S ω) (fun r => stepWr β a Y ω (stepTr S ω) +
            stepXat β a Y S ω r.toNNReal) := hωhit
      rw [hT, hA, stepXat_eq a ht] at hhit
      exact ofReal_add_le_stepThit (by omega) hreg.2.1 hCF t hrel' hhit
    have hinv0 : (P {ω | S ω < ⊤})⁻¹ ≠ 0 := ENNReal.inv_ne_zero.2 hne'
    have hinvt : (P {ω | S ω < ⊤})⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.2 hne
    rw [hPG] at hAR
    have h3 : (P {ω | S ω < ⊤})⁻¹ * (ENNReal.ofReal (1 - C * β ^ (-indDelta d / 30)) * P G) ≤
        (P {ω | S ω < ⊤})⁻¹ * P (G ∩ {ω | ∀ t : ℝ≥0, S ω = t →
          ENNReal.ofReal ((t : ℝ) + (4 : ℝ) ^ n) ≤
            stepThit β (stepWr β a Y ω) (stepAr β a Y ω) (t : ℝ)}) := by
      calc (P {ω | S ω < ⊤})⁻¹ * (ENNReal.ofReal (1 - C * β ^ (-indDelta d / 30)) * P G) =
          ENNReal.ofReal (1 - C * β ^ (-indDelta d / 30)) * ((P {ω | S ω < ⊤})⁻¹ * P G) :=
            mul_left_comm _ _ _
        _ ≤ _ := hAR.trans hP2
    have h4 := mul_le_mul' (le_refl (P {ω | S ω < ⊤})) h3
    have hcancel : ∀ x : ℝ≥0∞, P {ω | S ω < ⊤} * ((P {ω | S ω < ⊤})⁻¹ * x) = x := fun x => by
      rw [← mul_assoc, ENNReal.mul_inv_cancel hne hne', one_mul]
    rwa [hcancel, hcancel] at h4
  · intro ω
    have e : (fun s : ℝ≥0 => stepWr β a Y ω (min (stepAr β a Y ω (stepTr S ω) + (s : ℝ))
        (stepTr S ω))) = (stepReg β (stepShift a (Y ω))) ∘ fun s : ℝ≥0 =>
          (min (stepAr β a Y ω (stepTr S ω) + (s : ℝ)) (stepTr S ω)).toNNReal := rfl
    show IsRCPath (fun s : ℝ≥0 => stepWr β a Y ω (min (stepAr β a Y ω (stepTr S ω) + (s : ℝ))
        (stepTr S ω)))
    rw [e]
    refine isRCPath_comp_mono
      (isRegPath_stepReg (isDrivingPath_shiftPath (hYp ω) a).toIsRegPath).rc ?_ ?_
    · exact continuous_real_toNNReal.comp (by fun_prop)
    · intro s s' hss
      have h : (s : ℝ) ≤ s' := by exact_mod_cast hss
      exact Real.toNNReal_mono (min_le_min (by linarith) le_rfl)
  · ext Γ hΓ
    have hfm := measurable_stepReg_comp (β := β) hY hYp
    calc (Pr'.map (stepXat β a Y S)) Γ = Pr' (stepXat β a Y S ⁻¹' Γ) :=
          Measure.map_apply hXm hΓ
      _ = P {ω | stepReg β (Y ω) ∈ Γ} := stepAvoid_prob hY hYp hF a hS hne hΓ
      _ = (P.map (fun ω t => stepReg β (Y ω) t)) Γ := (Measure.map_apply hfm hΓ).symm
      _ = (Pr₀.map (avoidPath N₀)) Γ := by rw [stepReg_law hY hYp hN₀]; rfl

end ElboimSly.Paper.Step
