/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Step.SigmaClose
public import ElboimSly.Paper.Step.TransCoupling
public import ElboimSly.Paper.Step.BlockSym
public import ElboimSly.Paper.Base.BaseH4
public import ElboimSly.Foundations.Brownian.Moments
public import Mathlib

/-!
# The `σ`-estimate for long blocks (the σ-estimate, Case 1)

The σ-estimate, Case 1: compare `σ² = E[Y₁²]` with `σ'²` for the (H4) coupling at
level `n(T)`. `sigma_sq_close` shows
`|σ² - σ'²| ≤ (ε/√T)(K/√T + (1+σ'²)/2) + (K/√T)² q + √(80 σ'⁴ q)`,
where `q = η + p_F` bounds the probability that the coupling fails or the truncation is active.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set ElboimSly.Cyclic ElboimSly.SRW
open scoped NNReal ENNReal

namespace ElboimSly.Paper.Step

open ElboimSly.Paper ElboimSly.Paper.Base ElboimSly.Bridge

variable {d : ℕ}

/-- Extension of a path on `[0,T]` by its terminal value. -/
def extIcc (T : ℝ≥0) (w : Set.Icc (0 : ℝ≥0) T → Fin d → ℤ) : ℝ≥0 → Fin d → ℤ :=
  fun t => w ⟨min t T, zero_le, min_le_right _ _⟩

theorem measurable_extIcc (T : ℝ≥0) : Measurable (extIcc (d := d) T) :=
  measurable_pi_iff.2 fun _ => measurable_pi_apply _

theorem extIcc_restrictIcc (T : ℝ≥0) (γ : ℝ≥0 → Fin d → ℤ) :
    extIcc T (restrictIcc T γ) = SRW.stopPath T γ := rfl

variable {β : ℝ} [Fact (0 < β)] {Ωe : Type} [MeasurableSpace Ωe] {Pe : Measure Ωe}
  {N : Ωe → Measure (ℕ × RingSpace d β)}

/-- The law of the stopped path is the image of the law of the restricted path. -/
theorem ppLaw_eq_map_ext
    (hN : IsPoissonPointProcess N ((Measure.count : Measure ℕ).prod (ringIntensity d β)) Pe)
    (T : ℝ≥0) :
    ppLaw Pe N T = (Pe.map (fun ω (t : Set.Icc (0 : ℝ≥0) T) =>
      regenWalk (fun k => copyEnv (N ω) k) ((t : ℝ≥0) : ℝ))).map (extIcc T) := by
  have hae := aemeasurable_ppPath hN
  have e1 : (fun ω (t : Set.Icc (0 : ℝ≥0) T) =>
      regenWalk (fun k => copyEnv (N ω) k) ((t : ℝ≥0) : ℝ)) =
      restrictIcc T ∘ ppPath N := rfl
  have e2 : extIcc T ∘ restrictIcc T = SRW.stopPath T (d := d) := funext (extIcc_restrictIcc T)
  rw [e1, ← AEMeasurable.map_map_of_aemeasurable (measurable_restrictIcc T).aemeasurable hae,
    Measure.map_map (measurable_extIcc T) (measurable_restrictIcc T), e2]
  rfl

/-- **the σ-estimate, Case 1**: second moments of the block functional and of the Brownian
increment agree up to the coupling error. -/
theorem sigma_sq_close (hd : 1 ≤ d)
    (hN : IsPoissonPointProcess N ((Measure.count : Measure ℕ).prod (ringIntensity d β)) Pe)
    {T : ℝ≥0} (hT : 0 < T) {σ' ε η K pF : ℝ} (hσ' : 0 < σ') (hε : 0 ≤ ε) (hη : 0 ≤ η)
    (hK : 0 ≤ K) (hpF : 0 ≤ pF) (hq : 0 < η + pF)
    (hC : AdmitsBMCoupling d T
      (Pe.map (fun ω (t : Set.Icc (0 : ℝ≥0) T) =>
        regenWalk (fun k => copyEnv (N ω) k) ((t : ℝ≥0) : ℝ))) σ' ε η)
    (hF : ppLaw Pe N T (farSet K T) ≤ ENNReal.ofReal pF) :
    |(∫ w, (blockY T K w ⟨0, hd⟩) ^ 2 ∂ppLaw Pe N T) - σ' ^ 2| ≤
      ε / Real.sqrt T * (K / Real.sqrt T + (1 + σ' ^ 2) / 2) +
        (K / Real.sqrt T) ^ 2 * (η + pF) + Real.sqrt (80 * σ' ^ 4 * (η + pF)) := by
  obtain ⟨Q, hQ, hlaw, hB, -, hbd⟩ := exists_standardBrownianMotion_of_admitsBMCoupling hC
  have := hQ
  set Bz := zeroMod (Prod.snd : WalkPath d T × C(ℝ≥0, Fin d → ℝ) → _) with hBz
  set i0 : Fin d := ⟨0, hd⟩ with hi0
  have hTR : (0 : ℝ) < T := by exact_mod_cast hT
  have hsT : 0 < Real.sqrt (T : ℝ) := Real.sqrt_pos.2 hTR
  have hfst : Measurable fun p : WalkPath d T × C(ℝ≥0, Fin d → ℝ) => p.1.1 :=
    measurable_subtype_coe.comp measurable_fst
  have hext : Measurable fun p : WalkPath d T × C(ℝ≥0, Fin d → ℝ) => extIcc T p.1.1 :=
    (measurable_extIcc T).comp hfst
  set a : WalkPath d T × C(ℝ≥0, Fin d → ℝ) → ℝ := fun p => blockY T K (extIcc T p.1.1) i0 with ha
  set b : WalkPath d T × C(ℝ≥0, Fin d → ℝ) → ℝ := fun p => σ' * Bz T p i0 / Real.sqrt T with hb
  have ham : Measurable a := ((measurable_pi_apply i0).comp (measurable_blockY T K)).comp hext
  have hBm : Measurable fun p : WalkPath d T × C(ℝ≥0, Fin d → ℝ) => Bz T p i0 :=
    (measurable_pi_apply i0).comp (hB.measurable T)
  have hbm : Measurable b := (hBm.const_mul σ').div_const _
  -- the law of the stopped path
  have hlaw2 : ppLaw Pe N T = Q.map (fun p => extIcc T p.1.1) := by
    rw [ppLaw_eq_map_ext hN T, ← hlaw, Measure.map_map (measurable_extIcc T) hfst]; rfl
  have hV : ∫ w, (blockY T K w i0) ^ 2 ∂ppLaw Pe N T = ∫ p, a p ^ 2 ∂Q := by
    have hφ : Measurable fun w : ℝ≥0 → Fin d → ℤ => blockY T K w i0 ^ 2 :=
      ((measurable_pi_apply i0).comp (measurable_blockY T K)).pow_const 2
    rw [hlaw2, integral_map hext.aemeasurable hφ.aestronglyMeasurable]
  -- the good event
  set G : Set (WalkPath d T × C(ℝ≥0, Fin d → ℝ)) := {p | extIcc T p.1.1 ∉ farSet K T ∧
    ‖(fun i => ((p.1.1 ⟨T, zero_le, le_rfl⟩ i : ℤ) : ℝ)) - σ' • Bz T p‖ < ε} with hG
  have hGm : MeasurableSet G := by
    have h1 : MeasurableSet {p : WalkPath d T × C(ℝ≥0, Fin d → ℝ) | extIcc T p.1.1 ∉ farSet K T} :=
      (measurableSet_farSet K T).compl.preimage hext
    have h2 : MeasurableSet {p : WalkPath d T × C(ℝ≥0, Fin d → ℝ) |
        ‖(fun i => ((p.1.1 ⟨T, zero_le, le_rfl⟩ i : ℤ) : ℝ)) - σ' • Bz T p‖ < ε} := by
      have hm : Measurable fun p : WalkPath d T × C(ℝ≥0, Fin d → ℝ) =>
          (fun i => ((p.1.1 ⟨T, zero_le, le_rfl⟩ i : ℤ) : ℝ)) - σ' • Bz T p := by
        refine Measurable.sub ?_ ((hB.measurable T).const_smul σ')
        exact measurable_pi_iff.2 fun i => (measurable_of_countable (Int.cast : ℤ → ℝ)).comp
          ((measurable_pi_apply i).comp ((measurable_pi_apply (⟨T, zero_le, le_rfl⟩ :
            Set.Icc (0 : ℝ≥0) T)).comp hfst))
      exact measurableSet_lt hm.norm measurable_const
    exact h1.inter h2
  -- the probability of the complement
  have hGc : Q.real Gᶜ ≤ η + pF := by
    have hsub : Gᶜ ⊆ {p | extIcc T p.1.1 ∈ farSet K T} ∪
        {p | ENNReal.ofReal ε ≤ ⨆ t : Set.Icc (0 : ℝ≥0) T,
          ENNReal.ofReal ‖(fun i => ((p.1.1 t i : ℤ) : ℝ)) - σ' • Bz (t : ℝ≥0) p‖} := by
      intro p hp
      by_cases h1 : extIcc T p.1.1 ∈ farSet K T
      · exact Or.inl h1
      · refine Or.inr ?_
        have h2 : ¬ ‖(fun i => ((p.1.1 ⟨T, zero_le, le_rfl⟩ i : ℤ) : ℝ)) - σ' • Bz T p‖ < ε :=
          fun h => hp ⟨h1, h⟩
        rw [not_lt] at h2
        exact le_trans (ENNReal.ofReal_le_ofReal h2)
          (le_iSup (fun t : Set.Icc (0 : ℝ≥0) T =>
            ENNReal.ofReal ‖(fun i => ((p.1.1 t i : ℤ) : ℝ)) - σ' • Bz (t : ℝ≥0) p‖)
            ⟨T, zero_le, le_rfl⟩)
    have h1 : Q {p | extIcc T p.1.1 ∈ farSet K T} ≤ ENNReal.ofReal pF := by
      have : Q {p | extIcc T p.1.1 ∈ farSet K T} = ppLaw Pe N T (farSet K T) := by
        rw [hlaw2, Measure.map_apply hext (measurableSet_farSet K T)]; rfl
      rw [this]; exact hF
    have h2 := hbd
    have h3 : Q Gᶜ ≤ ENNReal.ofReal pF + ENNReal.ofReal η :=
      (measure_mono hsub).trans ((measure_union_le _ _).trans (add_le_add h1 h2))
    rw [Measure.real]
    have := ENNReal.toReal_mono (by simp) h3
    rw [ENNReal.toReal_add ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hpF,
      ENNReal.toReal_ofReal hη] at this
    linarith
  -- pointwise bounds
  have hab : ∀ p, |a p| ≤ K / Real.sqrt T := fun p => by
    have h1 := norm_blockY_le (T := T) (K := K) hK (extIcc T p.1.1)
    have h2 := norm_le_pi_norm (blockY T K (extIcc T p.1.1)) i0
    rw [Real.norm_eq_abs] at h2
    exact h2.trans h1
  have hGab : ∀ p ∈ G, |a p - b p| ≤ ε / Real.sqrt T := by
    rintro p ⟨hp1, hp2⟩
    have hTe : truncEnd T K (extIcc T p.1.1) = p.1.1 ⟨T, zero_le, le_rfl⟩ := by
      rw [truncEnd, Set.indicator_of_mem (show extIcc T p.1.1 ∈ (farSet K T)ᶜ from hp1)]
      simp [extIcc]
    have hne : a p - b p = (Real.sqrt T)⁻¹ * (((p.1.1 ⟨T, zero_le, le_rfl⟩ i0 : ℤ) : ℝ) -
        σ' * Bz T p i0) := by
      simp only [ha, hb, blockY, hTe, Pi.smul_apply, smul_eq_mul]
      field_simp
    rw [hne, abs_mul, abs_of_pos (inv_pos.2 hsT)]
    have h1 : |((p.1.1 ⟨T, zero_le, le_rfl⟩ i0 : ℤ) : ℝ) - σ' * Bz T p i0| ≤ ε := by
      have := norm_le_pi_norm ((fun i => ((p.1.1 ⟨T, zero_le, le_rfl⟩ i : ℤ) : ℝ)) - σ' • Bz T p) i0
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Real.norm_eq_abs] at this
      exact this.trans hp2.le
    calc (Real.sqrt T)⁻¹ * |((p.1.1 ⟨T, zero_le, le_rfl⟩ i0 : ℤ) : ℝ) - σ' * Bz T p i0|
        ≤ (Real.sqrt T)⁻¹ * ε := mul_le_mul_of_nonneg_left h1 (inv_pos.2 hsT).le
      _ = ε / Real.sqrt T := by rw [inv_mul_eq_div]
  -- Gaussian facts
  have hlawB : HasLaw (fun p : WalkPath d T × C(ℝ≥0, Fin d → ℝ) => Bz T p i0)
      (gaussianReal 0 T) Q := (hB.isPreBrownianReal i0).hasLaw_eval T
  have hB2 : Integrable (fun p => Bz T p i0 ^ 2) Q :=
    (Brownian.memLp_two_eval hB i0 T).integrable_sq
  have hB4 : Integrable (fun p => Bz T p i0 ^ 4) Q := by
    have := hlawB.memLp_comp (f := fun x : ℝ => x) (p := 4) (memLp_id_gaussianReal' 4 (by simp))
    have h2 := this.integrable_norm_pow (p := 4) (by norm_num)
    simpa [Real.norm_eq_abs, pow_abs, abs_pow, Even.pow_abs (by decide : Even 4)] using h2
  have hB2I : ∫ p, Bz T p i0 ^ 2 ∂Q = T := by
    have := hB.integral_mul_eval i0 i0 T
    simpa [sq] using this
  have hB4I : ∫ p, Bz T p i0 ^ 4 ∂Q ≤ 80 * (T : ℝ) ^ 2 :=
    Brownian.integral_pow_four_le_of_hasLaw hlawB
  have hb2 : Integrable (fun p => b p ^ 2) Q := by
    have : (fun p => b p ^ 2) = fun p => (σ' / Real.sqrt T) ^ 2 * Bz T p i0 ^ 2 := by
      funext p; simp only [hb]; ring
    rw [this]; exact hB2.const_mul _
  have hb4 : Integrable (fun p => b p ^ 4) Q := by
    have : (fun p => b p ^ 4) = fun p => (σ' / Real.sqrt T) ^ 4 * Bz T p i0 ^ 4 := by
      funext p; simp only [hb]; ring
    rw [this]; exact hB4.const_mul _
  have hbs : ∫ p, b p ^ 2 ∂Q = σ' ^ 2 := by
    have : (fun p => b p ^ 2) = fun p => (σ' / Real.sqrt T) ^ 2 * Bz T p i0 ^ 2 := by
      funext p; simp only [hb]; ring
    rw [this, integral_const_mul, hB2I, div_pow, Real.sq_sqrt hTR.le]
    field_simp
  have hbM : ∫ p, b p ^ 4 ∂Q ≤ 80 * σ' ^ 4 := by
    have : (fun p => b p ^ 4) = fun p => (σ' / Real.sqrt T) ^ 4 * Bz T p i0 ^ 4 := by
      funext p; simp only [hb]; ring
    rw [this, integral_const_mul]
    have h1 : (σ' / Real.sqrt T) ^ 4 = σ' ^ 4 / (T : ℝ) ^ 2 := by
      have h4 : Real.sqrt (T : ℝ) ^ 4 = (T : ℝ) ^ 2 := by
        rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, Real.sq_sqrt hTR.le]
      rw [div_pow, h4]
    rw [h1]
    calc σ' ^ 4 / (T : ℝ) ^ 2 * ∫ p, Bz T p i0 ^ 4 ∂Q
        ≤ σ' ^ 4 / (T : ℝ) ^ 2 * (80 * (T : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_left hB4I (by positivity)
      _ = 80 * σ' ^ 4 := by field_simp
  have key := second_moment_close ham hbm hGm (e := ε / Real.sqrt T) (A := K / Real.sqrt T)
    (s := σ') (M := 80 * σ' ^ 4) (q := η + pF) (by positivity) (by positivity) hq hGab hab hb2
    hb4 hbs hbM (by positivity) hGc
  rw [hV]
  exact key

end ElboimSly.Paper.Step
