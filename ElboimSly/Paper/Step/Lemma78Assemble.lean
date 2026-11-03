/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Step.Lemma78Det
public import ElboimSly.Paper.Step.Lemma78Bad
public import ElboimSly.Paper.Step.Lemma78Arith
public import ElboimSly.Paper.Step.Lemma78Num3
public import ElboimSly.Paper.Step.Lemma78Stmt
public import ElboimSly.Paper.Step.StepH234
public import ElboimSly.Paper.Step.Es61Env
public import ElboimSly.Paper.Heavy.EscInterfaceAll
public import ElboimSly.Paper.Heavy.ThrE
public import Mathlib

/-!
# Lemma 7.8: the union bound

ES22 Lemma 7.8 (§7), proof. The union bound over
The event cH_1 (`Step78ClaimH1`), discovered bad blocks for two walks (`step78_bad`), few excursions
(`Step78ClaimJ`), with covering fP_n and short gaps (`step78_vol_lt`) on the
complement. `c_pp = ½ min(c_♭/2, c_bm)` and `β_pp(n₁)` is the maximum of the thresholds.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Step

open ElboimSly ElboimSly.Paper ElboimSly.Paper.Heavy ElboimSly.Interchange

/-- The event cH_1, exactly as proved by `step78_H1`: the constant `c_bm`, and a threshold
`β_H1(n₁)` absorbing `n` large. -/
def Step78ClaimH1 (d : ℕ) (E : ℕ → HeavyEscConsts) : Prop :=
  ∃ cBm : ℝ, 0 < cBm ∧ ∃ βH1 : ℕ → ℝ, ∀ n₁ : ℕ, 8 * d ≤ n₁ →
    ∀ (β : ℝ) [Fact (0 < β)] (n : ℕ) (t₀ : ℝ), βH1 n₁ ≤ β → StepRegime d n₁ β n t₀ →
    ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (N : Ω → Measure (RingSpace d β)),
      IsPoissonPointProcess N (ringIntensity d β) P →
      ∀ (u : Fin d → ℤ) (q : ℝ), q ∈ Set.Icc 0 β →
        P {ω | cycOmega (N ω) 0 u 0 q (indScaleReduced t₀ n) ∧
            ¬ Step78H1 d β t₀ n (indScaleReduced t₀ n) (fun s => cycWalk (N ω) 0 0 s)} ≤
          ENNReal.ofReal (heavyA d n * Real.exp (-(heavyc d (E 0) * (n : ℝ) ^ 3)) +
            Real.exp (-(cBm * (n : ℝ) ^ 3)) + Real.exp (-(n : ℝ) ^ 3))

/-- Few excursions (in the `{J > n³}` form): for `β ≥ β_ex(n₁)` and `n ≥ 3`,
`P(ℋ_1 ∩ {ζ_1, …, ζ_{n³} < t'_n}) ≤ e^{-n³/17}`. (`J > n³` means that none of
`ζ_1, …, ζ_{n³}` equals `t'_n`, and `ζ_i ≤ t'_n`.) -/
def Step78ClaimJ (d : ℕ) : Prop :=
  ∃ βJ : ℕ → ℝ, ∀ n₁ : ℕ, 8 * d ≤ n₁ →
    ∀ (β : ℝ) [Fact (0 < β)] (n : ℕ) (t₀ : ℝ), βJ n₁ ≤ β → StepRegime d n₁ β n t₀ → 3 ≤ n →
    ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (N : Ω → Measure (RingSpace d β)),
      IsPoissonPointProcess N (ringIntensity d β) P →
      ∀ (u : Fin d → ℤ) (q : ℝ), q ∈ Set.Icc 0 β →
        P {ω | Step78H1 d β t₀ n (indScaleReduced t₀ n) (fun s => cycWalk (N ω) 0 0 s) ∧
            ∀ i : ℕ, 1 ≤ i → i ≤ n ^ 3 →
              (step78DataOf d β n (indScaleReduced t₀ n) u q N).zeta i ω <
                ((indScaleReduced t₀ n).toNNReal : WithTop ℝ≥0)} ≤
          ENNReal.ofReal (Real.exp (-((n : ℝ) ^ 3 / 17)))

theorem heavyc_le_cflat {d : ℕ} (E : HeavyEscConsts) : heavyc d E ≤ step78Cflat d :=
  le_min ((min_le_right _ _).trans (min_le_right _ _)) ((min_le_right _ _).trans (min_le_left _ _))

theorem heavyc_congr {d : ℕ} {E E' : HeavyEscConsts} (h : E.c5 = E'.c5) :
    heavyc d E = heavyc d E' := by
  unfold heavyc; rw [h]

/-- ES22 Lemma 7.8, conditional on the event cH_1 and few excursions
(which also carry the thresholds `β_bm(n₁)`, `β_ex(n₁)`). -/
theorem step78_assemble {d : ℕ} (hd : 5 ≤ d) (E : ℕ → HeavyEscConsts)
    (hI : HeavyEscInterfaceAll d E) (hH1 : Step78ClaimH1 d E) (hJ : Step78ClaimJ d) :
    ∃ cPp βPp, StepPp d cPp βPp := by
  obtain ⟨cBm, hcBm, βH1, hH1'⟩ := hH1
  obtain ⟨βJ, hJ'⟩ := hJ
  obtain ⟨Na, hNa⟩ := step78_asym hd
  set c : ℝ := heavyc d (E 0) with hcdef
  have hc : 0 < c := heavyc_pos (by omega)
  have hc17 : c ≤ 1 / 17 := heavyc_le
  set m : ℝ := min (c / 2) cBm with hm
  have hm0 : 0 < m := lt_min (by linarith) hcBm
  set K : ℕ := max Na (3000 * d ^ 2 * 2 ^ d) with hK
  refine ⟨m / 2, fun n₁ => max (max (βH1 n₁) (βJ n₁)) (max (stepBeta6 d (E n₁) n₁)
    ((4 : ℝ) ^ (K + 1))), by positivity, ?_⟩
  intro n₁ h8 β _ n t₀ hβ hR hn Ω _ P N hN u q hq
  have hβ0 : 0 < β := Fact.out
  have hβ1 : max (βH1 n₁) (βJ n₁) ≤ β := (le_max_left _ _).trans hβ
  have hβ2 : max (stepBeta6 d (E n₁) n₁) ((4 : ℝ) ^ (K + 1)) ≤ β := (le_max_right _ _).trans hβ
  have hβH : βH1 n₁ ≤ β := (le_max_left _ _).trans hβ1
  have hβJ : βJ n₁ ≤ β := (le_max_right _ _).trans hβ1
  have hβ6 : stepBeta6 d (E n₁) n₁ ≤ β := (le_max_left _ _).trans hβ2
  have hβN : (4 : ℝ) ^ (K + 1) ≤ β := (le_max_right _ _).trans hβ2
  have hb14 : (10 : ℝ) ^ 14 ≤ β := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hβ6
  have hb5 : (E n₁).beta5 ≤ β := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hβ6
  have hb4 : (4 : ℝ) ^ (max (heavyN6 d n₁ (E n₁)) n₁ + 1) ≤ β := le_trans (le_max_right _ _) hβ6
  have hnM : max (heavyN6 d n₁ (E n₁)) n₁ < n := step_n_gt hR hb4
  have hnK : K < n := step_n_gt hR hβN
  obtain ⟨-, hβ1', -, ⟨ht1, ht4⟩, hlt, hind⟩ := hR
  have hp : Es4Params d β n₁ n t₀ :=
    ⟨hd, h8, lt_of_le_of_lt (le_max_right _ _) hnM, hb14, ht1, ht4, hlt,
      fun n' h1 h2 t' h3 h4 => hind n' h1 h2 t' ⟨h3, h4⟩⟩
  have hT : HeavyT d n₁ (E n₁) n :=
    HeavyT.of_ge_N6 (by omega) (le_of_lt (lt_of_le_of_lt (le_max_left _ _) hnM))
  have hR : StepRegime d n₁ β n t₀ := ⟨h8, hβ1', by have := hT.t4; omega, ⟨ht1, ht4⟩, hlt, hind⟩
  have hn3 : 3 ≤ n := by have := hT.t4; omega
  have hA := hNa n (by omega) t₀ ht1 ht4 hT.t1.2 β hβ0.le
  have hnum1 : 3000 * (d : ℝ) ^ 2 * 2 ^ d ≤ 7 * n := by
    have : 3000 * d ^ 2 * 2 ^ d ≤ n := by omega
    have h' : ((3000 * d ^ 2 * 2 ^ d : ℕ) : ℝ) ≤ n := by exact_mod_cast this
    push_cast at h'
    linarith
  have hI1 : HeavyEscInterface d β (E n₁) n₁ n t₀ := hI.2 n₁ β n t₀
  have hceq : heavyc d (E n₁) = c := heavyc_congr (hI.1 n₁)
  have hq0 : 0 ≤ q := hq.1
  -- the four bounds
  obtain ⟨hb1, hb2⟩ := step78_bad hd h8 ht1 ht4 hp hT hb5 hb14 hlt hI1 hp.ind hN u q
  have hh1 := hH1' n₁ h8 β n t₀ hβH ⟨h8, hβ1', by omega, ⟨ht1, ht4⟩, hlt, hind⟩ Ω P N hN u q hq
  have hjj := hJ' n₁ h8 β n t₀ hβJ ⟨h8, hβ1', by omega, ⟨ht1, ht4⟩, hlt, hind⟩ hn3 Ω P N hN u q hq
  rw [hceq] at hb1
  -- the inclusion
  have hgood := ae_good hN
  set Tn := indScaleReduced t₀ n with hTn
  have hsub : {ω | cycOmega (N ω) 0 u 0 q Tn ∧
      ENNReal.ofReal ((39 / 10 : ℝ) ^ n) ≤
        volume {s₂ : ℝ | s₂ ∈ Icc 0 Tn ∧ ∃ s₁ ∈ Icc 0 Tn,
          ‖cycWalk (N ω) 0 0 s₁ - cycWalk (N ω) u q s₂‖ ≤ (19 / 10 : ℝ) ^ n}} ≤ᵐ[P]
      ({ω | cycOmega (N ω) 0 u 0 q Tn ∧
          ¬ Step78H1 d β t₀ n Tn (fun s => cycWalk (N ω) 0 0 s)} ∪
        {ω | ¬ (heavyGamma d β t₀ n (fun s : ℝ => cycWalk (N ω) 0 0 s) ∧
          heavyGamma d β t₀ n (fun s : ℝ => cycWalk (N ω) u q s - u))}) ∪
      {ω | cycOmega (N ω) 0 u 0 q Tn ∧
        (heavyGamma d β t₀ n (fun s : ℝ => cycWalk (N ω) 0 0 s) ∧
          heavyGamma d β t₀ n (fun s : ℝ => cycWalk (N ω) u q s - u)) ∧
        step78TauBad d β t₀ n q Tn u (fun s : ℝ => cycWalk (N ω) 0 0 s)
          (fun s : ℝ => cycWalk (N ω) u q s) ≤ ENNReal.ofReal Tn} ∪
      {ω | Step78H1 d β t₀ n Tn (fun s => cycWalk (N ω) 0 0 s) ∧
        ∀ i : ℕ, 1 ≤ i → i ≤ n ^ 3 →
          (step78DataOf d β n Tn u q N).zeta i ω < ((Tn.toNNReal : ℝ≥0) : WithTop ℝ≥0)} := by
    filter_upwards [hgood] with ω hω hmem
    obtain ⟨hΩ, hvol⟩ := hmem
    simp only [Set.mem_union, mem_ofPred_eq]
    by_contra hcon
    push Not at hcon
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hcon
    have hH1ω := h1 hΩ
    obtain ⟨hΓ₁, hΓ₂⟩ := h2
    have hτ : ENNReal.ofReal Tn < step78TauBad d β t₀ n q Tn u
        (fun s : ℝ => cycWalk (N ω) 0 0 s) (fun s : ℝ => cycWalk (N ω) u q s) :=
      h3 hΩ ⟨hΓ₁, hΓ₂⟩
    obtain ⟨i, hi1, hi2, hi3⟩ := h4 hH1ω
    have hzi : (step78DataOf d β n Tn u q N).zeta i ω = ((Tn.toNNReal : ℝ≥0) : WithTop ℝ≥0) :=
      le_antisymm (Step78Data.zeta_le_T _ ω i) hi3
    have hlt' := step78_vol_lt hd h8 ht1 ht4 hlt hT hq0 u N ω hω hnum1 hA hΩ hH1ω hΓ₂ hτ
      ⟨i, hi1, hi2, hzi⟩
    exact absurd hvol (not_le.2 hlt')
  have hX12 := (measure_union_le _ _).trans (add_le_add hh1 hb1)
  have hX := (measure_union_le _ _).trans (add_le_add hX12 hb2)
  have htot := (measure_union_le _ _).trans (add_le_add hX hjj)
  refine (measure_mono_ae hsub).trans (htot.trans ?_)
  have hA0 : 0 ≤ heavyA d n := by
    unfold heavyA; have := heavyCJ_pos (d := d); positivity
  rw [← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have ht11 := hT.t11
  unfold heavyC6 at ht11
  rw [hceq] at ht11
  refine step78_arith hA0 hc hc17 (hceq ▸ heavyc_le_cflat (E n₁)) hcBm ?_ ht11
  have : 1 / (m / 2) = 2 / m := by field_simp
  rw [← this]; exact hn

end ElboimSly.Paper.Step

end
