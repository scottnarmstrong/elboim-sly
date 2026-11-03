/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Step.Lemma78Assemble
public import ElboimSly.Paper.Step.Lemma78Numerics
public import ElboimSly.Paper.Step.Lemma78Ext
public import ElboimSly.Paper.Step.Lemma78Congr
public import ElboimSly.Paper.Step.Lemma78J
public import ElboimSly.Paper.Step.Lemma78Conn
public import ElboimSly.Paper.Step.Lemma78MeasH1Osc
public import Mathlib

/-!
# Few excursions

Few excursions (ES22 §7): for `β ≥ β_ex(n₁)` and `n ≥ 3`,
`P(ℋ₁ ∩ {J > n³}) ≤ e^{-n³/17}`. The proof extends the probability space by the independent
processes of w_2 after zeta_i, given ℱ^+_zeta_i (`step78_ext`), applies the abstract few-excursions bound
`step78_few_excursions` with the filtration `(ℱ⁺_t)`, the stopping times `ζ_i`, `ζ'_i` of
`Step78Data`, `ℋ₁ ∈ ℱ⁺_{ζ₁}` (`step78_measurableSet_H1_stopping`) and the one-excursion bound
`step78_excursion` (with the bracket `≤ 1/2` for `n` and `β` large, `step78_numerics`), and
transfers the event back to the original space (`step78_measure_le_prod`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Step

open ElboimSly ElboimSly.Cyclic ElboimSly.Paper ElboimSly.Paper.Heavy

variable {d : ℕ}

theorem step78_claimJ (hd : 5 ≤ d) : Step78ClaimJ d := by
  obtain ⟨Cτ, C42, hCτ, hC42, Hex⟩ := step78_excursion.{0} hd
  choose β₀ hβ₀ using Hex
  choose Nn Bβ hBβ hNum using fun n₁ => step78_numerics hd hCτ hC42 n₁
  refine ⟨fun n₁ => max (max (β₀ n₁) (Bβ n₁)) ((4 : ℝ) ^ (Nn n₁ + 1)), ?_⟩
  intro n₁ h8 β _ n t₀ hβ hreg hn3 Ω _ P N hN u q hq
  have hβ0 : 0 < β := Fact.out
  have hβa : β₀ n₁ ≤ β := ((le_max_left _ _).trans (le_max_left _ _)).trans hβ
  have hβb : Bβ n₁ ≤ β := ((le_max_right _ _).trans (le_max_left _ _)).trans hβ
  have hβc : (4 : ℝ) ^ (Nn n₁ + 1) ≤ β := (le_max_right _ _).trans hβ
  have hnN : Nn n₁ < n := step_n_gt hreg hβc
  have ht1 : 1 < t₀ := hreg.2.2.2.1.1
  have ht4 : t₀ ≤ 4 := hreg.2.2.2.1.2
  have ht0 : 0 < t₀ := by linarith
  obtain ⟨hHT, h4, hL1, hL2, hL3, hL4, hTn, hbr⟩ := hNum n₁ n hnN.le t₀ ht1 ht4 β hβb
  obtain ⟨Ω', mΩ', P', f, Nc, Nc', Nc'', hP', hf, hmap, hNeq, hN1, hN2, hN3, hI1, hI2, hI3,
    hcover⟩ := step78_ext hN
  set Tn : ℝ≥0 := (indScaleReduced t₀ n).toNNReal with hTnd
  have hT0 : 0 ≤ indScaleReduced t₀ n := by
    unfold indScaleReduced indScale; positivity
  have hTnR : (Tn : ℝ) = indScaleReduced t₀ n := Real.coe_toNNReal _ hT0
  have hTnlt : (Tn : ℝ) < (4 : ℝ) ^ n := by rw [hTnR]; exact hTn
  have h𝒢 : (⊥ : MeasurableSpace Ω') ≤ mΩ' := bot_le
  set ρ : ℝ := step78Rho d n with hρ
  set D := step78SliceData (cycNgood Nc) u q Tn n ρ with hD
  have hF := step78_frame u q Tn ⊥ hN1 h𝒢 (by omega : 1 ≤ d) hreg.2.1 n ρ
  set ℱ := step78Filt u q Tn ⊥ hN1 h𝒢 with hℱ
  have hζ : ∀ i, IsStoppingTime ℱ (D.zeta i) := fun i =>
    (Step78Data.isStoppingTime_zp_zeta hF i).2
  have hζ' : ∀ i, IsStoppingTime ℱ (D.zp i) := fun i =>
    (Step78Data.isStoppingTime_zp_zeta hF i).1
  set H : Set Ω' := {ω | Step78H1 d β t₀ n (Tn : ℝ)
    (fun s : ℝ => cycWalk (cycSlice () (cycNgood Nc ω)) 0 0 s)} with hH
  have hHm : MeasurableSet[(hζ 1).measurableSpace] H :=
    step78_measurableSet_H1_stopping u q Tn ⊥ hN1 h𝒢 ht0 (by omega) (hζ 1)
  have hex : ∀ i, 1 ≤ i → ∀ G : Set Ω', MeasurableSet[(hζ i).measurableSpace] G →
      G ⊆ H ∩ {ω | D.zeta i ω < (Tn : WithTop ℝ≥0)} →
        P'.real (G ∩ {ω | D.zp i ω < (Tn : WithTop ℝ≥0)}) ≤ (1 / 2) * P'.real G := by
    intro i hi G hG hGsub
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    have h := hβ₀ n₁ β n t₀ hβa hreg hHT hL1 hL2 hL3 hL4 u q Tn hTnlt ⊥ hN1 hN2 hN3 hI1 hI2 hI3
      h𝒢 j hG (fun ω hω => (hGsub hω).1) (fun ω hω => (hGsub hω).2)
    have h1 : P' (G ∩ {ω | D.zp (j + 1) ω < (Tn : WithTop ℝ≥0)}) ≤
        ENNReal.ofReal (1 / 2) * P' G :=
      h.trans (by gcongr)
    show (P' _).toReal ≤ 1 / 2 * (P' G).toReal
    calc (P' (G ∩ {ω | D.zp (j + 1) ω < (Tn : WithTop ℝ≥0)})).toReal
        ≤ (ENNReal.ofReal (1 / 2) * P' G).toReal :=
          ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)) h1
      _ = 1 / 2 * (P' G).toReal := by
          rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by norm_num)]
  have hfew := step78_few_excursions (μ := P') (ℱ := ℱ) (ζ := D.zeta) (ζ' := D.zp) Tn hζ hζ'
    (fun i ω => Step78Data.zeta_le_T _ ω i) (fun i ω => Step78Data.zeta_le_zp _ ω i)
    (fun i ω => Step78Data.zp_le_zeta_succ _ ω i) hHm hex hn3
  -- the set in the extension
  set B'' : Set Ω' := H ∩ {ω | ∀ i : ℕ, 1 ≤ i → i ≤ n ^ 3 → D.zeta i ω < (Tn : WithTop ℝ≥0)}
    with hB''
  have hPB : P' B'' ≤ ENNReal.ofReal (Real.exp (-((n : ℝ) ^ 3 / 17))) := by
    rw [← ENNReal.ofReal_toReal (measure_ne_top P' B'')]
    exact ENNReal.ofReal_le_ofReal hfew
  -- comparison of the data
  have hgood : ∀ᵐ ω ∂P', cycNgood Nc ω = Nc ω := ae_cycNgood_eq hN1
  have hslice : ∀ ω', cycNgood Nc ω' = Nc ω' → cycSlice () (cycNgood Nc ω') = N (f ω') := by
    intro ω' hg
    rw [hg, hNeq]; exact cycSlice_map_unit _
  have hincl : f ⁻¹' {ω | Step78H1 d β t₀ n (indScaleReduced t₀ n)
        (fun s => cycWalk (N ω) 0 0 s) ∧ ∀ i : ℕ, 1 ≤ i → i ≤ n ^ 3 →
          (step78DataOf d β n (indScaleReduced t₀ n) u q N).zeta i ω <
            ((indScaleReduced t₀ n).toNNReal : WithTop ℝ≥0)} ≤ᵐ[P'] B'' := by
    filter_upwards [hgood] with ω' hg hmem
    obtain ⟨hH1, hzeta⟩ := hmem
    have hsl := hslice ω' hg
    refine ⟨?_, ?_⟩
    · show Step78H1 d β t₀ n (Tn : ℝ) (fun s : ℝ => cycWalk (cycSlice () (cycNgood Nc ω')) 0 0 s)
      rw [hsl, hTnR]; exact hH1
    · intro i hi1 hi2
      have hag : Step78Data.AgreeAt ((step78DataOf d β n (indScaleReduced t₀ n) u q N).comap f)
          D ω' := by
        refine ⟨rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
        · intro t
          show cycWalk (cycSlice () (cycNgood Nc ω')) u q t = cycWalk (N (f ω')) u q t
          rw [hsl]
        · show (fun s : ℝ => cycWalk (cycSlice () (cycNgood Nc ω')) 0 0 s) ''
              Icc 0 (Tn : ℝ) = (fun s : ℝ => cycWalk (N (f ω')) 0 0 s) '' Icc 0 (indScaleReduced t₀ n)
          rw [hsl, hTnR]
      have h1 := (Step78Data.zp_zeta_congr hag i).2
      have h2 := congrFun (Step78Data.comap_zp_zeta
        (step78DataOf d β n (indScaleReduced t₀ n) u q N) f i).2 ω'
      rw [h2] at h1
      rw [h1]
      exact hzeta i hi1 hi2
  have hmeas := hcover _ (toMeasurable P' B'') (measurableSet_toMeasurable _ _)
    (hincl.trans (Filter.Eventually.of_forall (fun x hx => subset_toMeasurable _ _ hx)))
  rw [measure_toMeasurable] at hmeas
  exact hmeas.trans hPB

end ElboimSly.Paper.Step

end
