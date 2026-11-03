/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Step.Lemma78H1Aux
public import ElboimSly.Paper.Step.Lemma78H1Num
public import ElboimSly.Paper.Step.Lemma78H1Coupling
public import ElboimSly.Paper.Step.Lemma78H1Regen
public import ElboimSly.Paper.Step.Lemma78BadGamma
public import ElboimSly.Paper.Step.Lemma78Setting2
public import ElboimSly.Paper.Step.Chain
public import ElboimSly.Paper.Step.Es61All
public import ElboimSly.Paper.Step.Cor72Interface
public import ElboimSly.Paper.Step.StepH234
public import ElboimSly.Frozen.Defs.CycOmega
public import ElboimSly.Frozen.Defs.IndScaleReduced
public import Mathlib

/-!
# The event `ℋ_1`

The event cH_1 (ES22 §7, deviation D11). For `β ≥ max{β_bm(n₁), β_§6(n₁)}`
and `n` large, `P(Ω ∩ ℋ_1ᶜ) ≤ A_n e^{-c_♭ n³} + e^{-c_bm n³} + e^{-n³}`, for the walk
`W₁ = W^N_{0,0}` of a single Poisson environment `N`.

The proof follows the source: `W₁ ∈ Γ_n` off probability `A_n e^{-c_♭ n³}` (mathbbP(𝒢(i))ge1-e^-cn^3,
`heavyGamma_single`) gives `τ̂(W₁) > t'_n` on `Ω`; the event `Osc_1` is controlled by the Brownian
coupling of ES22 Lemma 7.6 (`StepBm`, here produced from `HeavyEscInterfaceAll` through
`stepEs61_of_interfaceAll` and `step_lemmas_of_es61`) for the regenerated walk with first piece
`W₁`, which agrees with `W₁` on `[0, t'_n]` on `Ω`, together with the Brownian oscillation estimate
Oscillation (`step78_osc_pathbound`).
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped NNReal ENNReal

namespace ElboimSly.Paper.Step

open ElboimSly ElboimSly.Paper ElboimSly.Paper.Heavy ElboimSly.Cyclic


/-- `2 t_n^{θ_H} ≤ 1.9^n / 2`. -/
theorem step78_h1_eps {n : ℕ} {t₀ : ℝ} (hsc : 0 < indScale t₀ n)
    (hle : indScale t₀ n ≤ (4 : ℝ) ^ (n + 1))
    (hth : 4 * ((4 : ℝ) ^ (n + 1)) ^ ((41 : ℝ) / 100) ≤ (19 / 10 : ℝ) ^ n) :
    2 * indScale t₀ n ^ indThetaH ≤ (1.9 : ℝ) ^ n / 2 := by
  have h1 : indScale t₀ n ^ indThetaH ≤ ((4 : ℝ) ^ (n + 1)) ^ ((41 : ℝ) / 100) := by
    unfold indThetaH
    exact Real.rpow_le_rpow hsc.le hle (by norm_num)
  have h19 : (1.9 : ℝ) = 19 / 10 := by norm_num
  rw [h19]
  linarith

/-- The Brownian oscillation bound is at most `e^{-n³}`. -/
theorem step78_h1_num {d n : ℕ} {t₀ σ : ℝ} (hsc : 0 < indScale t₀ n)
    (hle : indScale t₀ n ≤ (4 : ℝ) ^ (n + 1)) (hσ0 : 0 < σ) (hσ2 : σ ≤ 2)
    (hex : (4 * d * ⌈(4 : ℝ) ^ (n + 1) / (36 / 10 : ℝ) ^ n⌉₊ : ℝ) *
      Real.exp (-((19 / 10 : ℝ) ^ n / 2) ^ 2 / (16 * 2 ^ 2 * (36 / 10 : ℝ) ^ n)) ≤
        Real.exp (-(n : ℝ) ^ 3)) :
    (4 * d * (⌈(indScale t₀ n).toNNReal / ((3.6 : ℝ) ^ n).toNNReal⌉₊ : ℕ) : ℝ≥0∞) *
      ENNReal.ofReal (Real.exp (-((1.9 : ℝ) ^ n / 2) ^ 2 / (16 * σ ^ 2 * (3.6 : ℝ) ^ n))) ≤
        ENNReal.ofReal (Real.exp (-(n : ℝ) ^ 3)) := by
  have h36 : (3.6 : ℝ) = 36 / 10 := by norm_num
  have h19 : (1.9 : ℝ) = 19 / 10 := by norm_num
  rw [h36, h19]
  have hh0 : (0 : ℝ) < (36 / 10 : ℝ) ^ n := by positivity
  have hK : (⌈(indScale t₀ n).toNNReal / ((36 / 10 : ℝ) ^ n).toNNReal⌉₊ : ℕ) ≤
      ⌈(4 : ℝ) ^ (n + 1) / (36 / 10 : ℝ) ^ n⌉₊ := by
    refine Nat.ceil_le.2 ?_
    rw [← NNReal.coe_le_coe, NNReal.coe_div, NNReal.coe_natCast,
      Real.coe_toNNReal _ hsc.le, Real.coe_toNNReal _ hh0.le]
    calc indScale t₀ n / (36 / 10 : ℝ) ^ n ≤ (4 : ℝ) ^ (n + 1) / (36 / 10 : ℝ) ^ n := by
          gcongr
      _ ≤ _ := Nat.le_ceil _
  have hexp : Real.exp (-((19 / 10 : ℝ) ^ n / 2) ^ 2 / (16 * σ ^ 2 * (36 / 10 : ℝ) ^ n)) ≤
      Real.exp (-((19 / 10 : ℝ) ^ n / 2) ^ 2 / (16 * 2 ^ 2 * (36 / 10 : ℝ) ^ n)) := by
    apply Real.exp_le_exp.2
    have hq : 0 < ((19 / 10 : ℝ) ^ n / 2) ^ 2 := by positivity
    rw [neg_div, neg_div, neg_le_neg_iff]
    apply div_le_div_of_nonneg_left hq.le (by positivity)
    have : σ ^ 2 ≤ 2 ^ 2 := by nlinarith
    nlinarith [hh0]
  calc (4 * d * (⌈(indScale t₀ n).toNNReal / ((36 / 10 : ℝ) ^ n).toNNReal⌉₊ : ℕ) : ℝ≥0∞) *
        ENNReal.ofReal (Real.exp (-((19 / 10 : ℝ) ^ n / 2) ^ 2 / (16 * σ ^ 2 * (36 / 10 : ℝ) ^ n)))
      ≤ ENNReal.ofReal (4 * d * (⌈(4 : ℝ) ^ (n + 1) / (36 / 10 : ℝ) ^ n⌉₊ : ℕ)) *
        ENNReal.ofReal (Real.exp (-((19 / 10 : ℝ) ^ n / 2) ^ 2 /
          (16 * 2 ^ 2 * (36 / 10 : ℝ) ^ n))) := by
        refine mul_le_mul' ?_ (ENNReal.ofReal_le_ofReal hexp)
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]
        simp only [ENNReal.ofReal_natCast, ENNReal.ofReal_ofNat]
        exact mul_le_mul' le_rfl (by exact_mod_cast hK)
    _ = ENNReal.ofReal ((4 * d * (⌈(4 : ℝ) ^ (n + 1) / (36 / 10 : ℝ) ^ n⌉₊ : ℕ) : ℝ) *
        Real.exp (-((19 / 10 : ℝ) ^ n / 2) ^ 2 / (16 * 2 ^ 2 * (36 / 10 : ℝ) ^ n))) :=
        (ENNReal.ofReal_mul (by positivity)).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal hex

/-- The event cH_1. For `d ≥ 5` and the interface `HeavyEscInterfaceAll d E` (§5),
there are `c_bm > 0` and thresholds `β_H1(n₁)` such that, in the step regime `SR(n₁; β, n, t₀)` with
`β ≥ β_H1(n₁)`, for a Poisson point process `N` of intensity `μ_β`, `u ∈ ℤ^d`, `q ∈ [0, β]`:
`P(Ω(0,u,0,q;t'_n) ∩ ℋ_1ᶜ) ≤ A_n e^{-c_♭ n³} + e^{-c_bm n³} + e^{-n³}`, where `ℋ_1` is
`Step78H1` for the walk `W^N_{0,0}` and the horizon `t'_n`. -/
theorem step78_H1 {d : ℕ} (hd5 : 5 ≤ d) {E : ℕ → HeavyEscConsts}
    (hI : HeavyEscInterfaceAll d E) :
    ∃ cBm : ℝ, 0 < cBm ∧ ∃ βH1 : ℕ → ℝ, ∀ n₁ : ℕ, 8 * d ≤ n₁ →
      ∀ (β : ℝ) [Fact (0 < β)] (n : ℕ) (t₀ : ℝ), βH1 n₁ ≤ β → StepRegime d n₁ β n t₀ →
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (N : Ω → Measure (RingSpace d β)),
        IsPoissonPointProcess N (ringIntensity d β) P →
        ∀ (u : Fin d → ℤ) (q : ℝ), q ∈ Set.Icc 0 β →
          P {ω | cycOmega (N ω) 0 u 0 q (indScaleReduced t₀ n) ∧
              ¬ Step78H1 d β t₀ n (indScaleReduced t₀ n) (fun s => cycWalk (N ω) 0 0 s)} ≤
            ENNReal.ofReal (heavyA d n * Real.exp (-(heavyc d (E 0) * (n : ℝ) ^ 3)) +
              Real.exp (-(cBm * (n : ℝ) ^ 3)) + Real.exp (-(n : ℝ) ^ 3)) := by
  obtain ⟨-, -, ⟨cBm, hcBm, βBm, hBm⟩, -⟩ :=
    step_lemmas_of_es61 hd5 (heavyC6_pos (by omega) (E 0)) (stepEs61_of_interfaceAll hd5 hI)
  obtain ⟨N0, hN0⟩ := eventually_atTop.1
    ((h1_eventually_theta.and (h1_eventually_exp d)).and (eventually_ge_atTop 4))
  let Nb : ℕ → ℕ := fun n₁ => max (max N0 (heavyN6 d n₁ (E n₁))) n₁
  refine ⟨cBm, hcBm, fun n₁ => max (max (βBm n₁) (E n₁).beta5)
    (max (max ((10 : ℝ) ^ 14) ((6 : ℝ) ^ 16)) ((4 : ℝ) ^ (Nb n₁ + 1))), ?_⟩
  intro n₁ h8 β _ n t₀ hβ hR Ω _ P N hN u q hq
  have hβ0 : 0 < β := Fact.out
  have hβ1 := (le_max_left _ _).trans hβ
  have hβ2 := (le_max_right _ _).trans hβ
  have hβBm : βBm n₁ ≤ β := (le_max_left _ _).trans hβ1
  have hβ5 : (E n₁).beta5 ≤ β := (le_max_right _ _).trans hβ1
  have hβ14 : (10 : ℝ) ^ 14 ≤ β := ((le_max_left _ _).trans (le_max_left _ _)).trans hβ2
  have hβ16 : (6 : ℝ) ^ 16 ≤ β := ((le_max_right _ _).trans (le_max_left _ _)).trans hβ2
  have hβN : (4 : ℝ) ^ (Nb n₁ + 1) ≤ β := (le_max_right _ _).trans hβ2
  have hnNb : Nb n₁ < n := step_n_gt hR hβN
  have hnN0 : N0 ≤ n := by
    have : N0 ≤ Nb n₁ := (le_max_left _ _).trans (le_max_left _ _)
    omega
  have hnN6 : heavyN6 d n₁ (E n₁) ≤ n := by
    have : heavyN6 d n₁ (E n₁) ≤ Nb n₁ := (le_max_right _ _).trans (le_max_left _ _)
    omega
  have hn₁n : n₁ < n := by
    have : n₁ ≤ Nb n₁ := le_max_right _ _
    omega
  obtain ⟨⟨hth, hex⟩, hn4⟩ := hN0 n hnN0
  have hR' := hR
  obtain ⟨-, hβ1', hn1, ht, hlt, hind⟩ := hR'
  have hp : Es4Params d β n₁ n t₀ :=
    ⟨hd5, h8, hn₁n, hβ14, ht.1, ht.2, hlt,
      fun n' h1 h2 t' h3 h4 => hind n' h1 h2 t' ⟨h3, h4⟩⟩
  have hT : HeavyT d n₁ (E n₁) n := HeavyT.of_ge_N6 (by omega) hnN6
  -- the first term: `W₁ ∈ Γ_n`
  have hΓ := heavyGamma_single (hI.2 n₁ β n t₀) hp hT hβ5 (by linarith [ht.1]) hn1 hN
  have hc : heavyc d (E n₁) = heavyc d (E 0) := by
    unfold heavyc; rw [hI.1 n₁]
  rw [hc] at hΓ
  -- scales
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hsc : 0 < indScale t₀ n := by
    unfold indScale; have := ht.1; positivity
  have hle : indScale t₀ n ≤ (4 : ℝ) ^ (n + 1) := by
    unfold indScale
    have := ht.2
    rw [pow_succ]
    nlinarith [pow_pos (by norm_num : (0 : ℝ) < 4) n]
  set Tr : ℝ := indScaleReduced t₀ n with hTr
  have hTr0 : 0 ≤ Tr := by unfold indScaleReduced at hTr; rw [hTr]; positivity
  have hn4' : (4 : ℝ) ≤ n := by exact_mod_cast hn4
  have hTrlt : Tr < indScale t₀ n := by
    have h1 : (1 : ℝ) < (n : ℝ) ^ 4 := one_lt_pow₀ (by linarith) (by norm_num)
    rw [hTr]; unfold indScaleReduced
    rw [div_lt_iff₀ (by positivity)]
    nlinarith
  -- the second term: Brownian coupling
  obtain ⟨Ω', mΩ', P', N', hP', hN', -⟩ :=
    exists_isPoissonPointProcess ((Measure.count : Measure ℕ).prod (ringIntensity d β))
  obtain ⟨σ, hσ, hcoup⟩ := hBm n₁ h8 β n t₀ hβBm hR Ω' P' N' hN'
  obtain ⟨hσ0, hσ2⟩ := step78_sigma_bounds hβ16 hsc hσ
  set T' : ℝ≥0 := (indScale t₀ n).toNNReal with hT'
  set T : ℝ≥0 := Tr.toNNReal with hT
  have hTT' : T < T' := by
    rw [hT, hT']; exact Real.toNNReal_lt_toNNReal_iff hsc |>.2 hTrlt
  have hT'pos : 0 < T' := lt_of_le_of_lt zero_le hTT'
  obtain ⟨c, hTc, hcT', hcβ⟩ := exists_h1_cutoff hβ0 hTT'
  have h36 : (3.6 : ℝ) = 36 / 10 := by norm_num
  have h19 : (1.9 : ℝ) = 19 / 10 := by norm_num
  set h : ℝ := (3.6 : ℝ) ^ n with hh
  set r : ℝ := (1.9 : ℝ) ^ n with hr
  have hh0 : 0 < h := by positivity
  have hr0 : 0 < r := by positivity
  have hεpos : 0 < indScale t₀ n ^ indThetaH := Real.rpow_pos_of_pos hsc _
  have hεr : 2 * indScale t₀ n ^ indThetaH ≤ r / 2 := step78_h1_eps hsc hle hth
  have hFae := aemeasurable_regenWalk_Icc hN' T'
  have hpath := step78_osc_pathbound P' c _ hT'pos hFae hσ0 hεpos hh0 hr0 hεr hcoup
  have htrans := step78_osc_transfer (r := r) hN hN' hTc hcT' hh0 hcβ
  have hTcoe : ((T : ℝ≥0) : ℝ) = Tr := Real.coe_toNNReal _ hTr0
  rw [hTcoe] at htrans
  have hnum := step78_h1_num (d := d) hsc hle hσ0 hσ2 hex
  -- assembly
  have hsub : {ω | cycOmega (N ω) 0 u 0 q Tr ∧
        ¬ Step78H1 d β t₀ n Tr (fun s => cycWalk (N ω) 0 0 s)} ⊆
      {ω | ¬ heavyGamma d β t₀ n (fun s => cycWalk (N ω) 0 0 s)} ∪
      {ω | ¬ cycClosesBy (N ω) 0 0 Tr ∧ ¬ ∀ s ∈ Icc (0 : ℝ) Tr, ∀ s' ∈ Icc (0 : ℝ) Tr,
        |s - s'| ≤ h → ‖cycWalk (N ω) 0 0 s - cycWalk (N ω) 0 0 s'‖ ≤ r} := by
    rintro ω ⟨hΩ, hnH⟩
    by_cases hg : heavyGamma d β t₀ n (fun s => cycWalk (N ω) 0 0 s)
    · right
      refine ⟨hΩ.2.1, fun hosc => hnH ⟨?_, hosc⟩⟩
      refine step78_tauHat_of_gamma hTr0 hg ?_ hTrlt
      refine ofReal_lt_cycClosingTime hβ0 hTr0 fun ⟨k, hk1, hk2, hk3⟩ => hΩ.2.1 ⟨k, hk1, hk2, hk3⟩
    · left; exact hg
  have hfinal : P {ω | cycOmega (N ω) 0 u 0 q Tr ∧
        ¬ Step78H1 d β t₀ n Tr (fun s => cycWalk (N ω) 0 0 s)} ≤
      ENNReal.ofReal (heavyA d n * Real.exp (-(heavyc d (E 0) * (n : ℝ) ^ 3))) +
        (ENNReal.ofReal (Real.exp (-(cBm * (n : ℝ) ^ 3))) +
          ENNReal.ofReal (Real.exp (-(n : ℝ) ^ 3))) := by
    calc _ ≤ P ({ω | ¬ heavyGamma d β t₀ n (fun s => cycWalk (N ω) 0 0 s)} ∪ _) :=
          measure_mono hsub
      _ ≤ _ := measure_union_le _ _
      _ ≤ _ := add_le_add hΓ ((htrans.trans hpath).trans (add_le_add le_rfl hnum))
  have hA : 0 ≤ heavyA d n * Real.exp (-(heavyc d (E 0) * (n : ℝ) ^ 3)) :=
    mul_nonneg (by unfold heavyA heavyCJ; positivity) (Real.exp_pos _).le
  refine hfinal.trans_eq ?_
  rw [← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1
  ring

end ElboimSly.Paper.Step

end
