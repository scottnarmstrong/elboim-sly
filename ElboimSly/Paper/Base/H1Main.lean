/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Base.H1Assemble
public import ElboimSly.Paper.Base.H1Arith
public import ElboimSly.Foundations.SRW.BaseBounds
public import ElboimSly.Foundations.StrongApprox.BaseCoupling
public import Mathlib

/-!
# ES22 Lemma 8.1: (H1) at the base

ES22 Lemma 8.1 (§8).

* `es8_lemma_8_1`: for `d ≥ 5`, `β ≥ β₀(d)`, `n ≥ max(20, 2d, n₁(d))`, `t₀ ∈ (1,4]` with
  `t_n ≤ β`, the regenerated walk satisfies `P(W|[0,t_n] is a relaxed path) ≥ 1 - e^{-n³}`.

The transfer from the regenerated walk to the SRW of the coupling is done through the regular
set `h1Set` (`H1Version`): the relaxed-path event is measurable only on regular paths, and
`regenPath_prob_eq_srw` identifies the two probabilities.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Paper

open ElboimSly.SRW ElboimSly.Brownian

/-- **ES22 Lemma 8.1** (Lemma 8.1): (H1) at the base. -/
theorem es8_lemma_8_1 {d : ℕ} (hd : 5 ≤ d) {β : ℝ} [Fact (0 < β)] (hβ : es8Beta0 d ≤ β)
    {n : ℕ} (hn20 : 20 ≤ n) (hn2d : 2 * d ≤ n) (hn1 : es8n1 d ≤ n) {t0 : ℝ} (ht1 : 1 < t0)
    (ht4 : t0 ≤ 4) (htβ : indScale t0 n ≤ β) {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {N : Ω → Measure (ℕ × RingSpace d β)}
    (hN : IsPoissonPointProcess N ((Measure.count : Measure ℕ).prod (ringIntensity d β)) P) :
    ENNReal.ofReal (1 - Real.exp (-(n : ℝ) ^ 3)) ≤
      P {ω | IsRelaxedPath (fun k => copyEnv (N ω) k) (indScale t0 n)} := by
  have hβpos : 0 < β := Fact.out
  have hd1 : 1 ≤ d := by omega
  have : NeZero d := ⟨by omega⟩
  obtain ⟨hβ1, hBC⟩ := es8Beta0_spec hd1
  obtain ⟨hB1, hB2, hB3, hB4⟩ := hBC β hβ
  have ht0pos : 0 < t0 := by linarith
  set b : ℝ := β ^ indDelta d with hb
  have hb0 : 0 < b := by linarith
  set t0n : ℝ≥0 := t0.toNNReal with ht0n
  set T : ℝ≥0 := 4 ^ n * t0n with hT
  have ht0nr : (t0n : ℝ) = t0 := Real.coe_toNNReal _ ht0pos.le
  have hTr : (T : ℝ) = indScale t0 n := by
    simp only [hT, NNReal.coe_mul, NNReal.coe_pow, NNReal.coe_ofNat, ht0nr, indScale]
  have hTle : (T : ℝ) ≤ 4 ^ (n + 1) := by
    rw [hTr, indScale, pow_succ]; nlinarith [pow_pos (show (0 : ℝ) < 4 by norm_num) n]
  have hTβ : (T : ℝ) ≤ β := hTr ▸ htβ
  have h4nT : (4 : ℝ) ^ n < T := by
    rw [hTr, indScale]; nlinarith [pow_pos (show (0 : ℝ) < 4 by norm_num) n]
  have h4nβ : (4 : ℝ) ^ n < β := h4nT.trans_le hTβ
  have hn1' : Classical.choose (StrongApprox.sa_base_coupling d hd1) ≤ n := by
    unfold es8n1 at hn1; rwa [dite_eq_left hd1] at hn1
  obtain ⟨Ω', mΩ', P', N', B, hPr, hN', hB, hSRW, hcplP⟩ :=
    Classical.choose_spec (StrongApprox.sa_base_coupling d hd1) n hn1' (T : ℝ) T.2 hTle
  have := hPr
  -- parameters
  set R : ℝ := (n : ℝ) ^ 2 * √(T : ℝ) with hRdef
  set M : ℕ := ⌈(2 * R + 1) ^ ((2 * d : ℝ) / 5)⌉₊ with hMdef
  set m0 : ℕ := ⌊b⌋₊ with hm0def
  have hR0 : 0 ≤ R := by positivity
  have hy0 : 0 ≤ (2 * R + 1) ^ ((2 * d : ℝ) / 5) := by positivity
  have hM : (2 * R + 1) ^ d ≤ (M : ℝ) ^ (5 / 2 : ℝ) := by
    have h1 : (2 * R + 1) ^ ((2 * d : ℝ) / 5) ≤ M := Nat.le_ceil _
    calc (2 * R + 1) ^ d = ((2 * R + 1) ^ ((2 * d : ℝ) / 5)) ^ (5 / 2 : ℝ) := by
          rw [← Real.rpow_mul (by positivity)]
          have : (2 * d : ℝ) / 5 * (5 / 2) = d := by ring
          rw [this, Real.rpow_natCast]
      _ ≤ (M : ℝ) ^ (5 / 2 : ℝ) := Real.rpow_le_rpow hy0 h1 (by norm_num)
  obtain ⟨hm2, hm5⟩ := hB2 n (by omega) h4nβ
  have hm0b : (m0 : ℝ) ≤ b := Nat.floor_le hb0.le
  have hm0b' : b - 1 ≤ m0 := by have := Nat.lt_floor_add_one b; linarith
  -- events
  set Z' : Ω' → SRW.PathSpace d := canonical d N' with hZ'
  have h1t : 1 < t0n := by rw [← NNReal.coe_lt_coe, ht0nr]; simpa using ht1
  have h4t : t0n ≤ 4 := by rw [← NNReal.coe_le_coe, ht0nr]; simpa using ht4
  set Ef : Set Ω' := {ω | ∃ s, s ≤ 4 ^ n * t0n ∧
    (n : ℝ) ^ 2 * √((4 ^ n * t0n : ℝ≥0) : ℝ) ≤ ‖Z' ω s‖} with hEf
  set Efast : Set Ω' := {ω | ∃ s s', s ≤ s' ∧ s' ≤ 4 ^ n * t0n ∧ s' - s ≤ 1 ∧
    (n : ℝ) ^ 5 < SRW.l1 (Z' ω s' - Z' ω s)} with hEfast
  set Ec : Set Ω' := {ω | ENNReal.ofReal ((n : ℝ) ^ 10) ≤ ⨆ t : {t : ℝ≥0 // (t : ℝ) ≤ T},
    ENNReal.ofReal ‖(fun i => ((walk d (N' ω) (t : ℝ≥0) i : ℤ) : ℝ)) -
      √2 • B (t : ℝ≥0) ω‖} with hEc
  set Eo : Set Ω' := {ω | ∃ x : Fin d → ℤ, ‖x‖ < R ∧ ∃ m : ℕ, m0 ≤ m ∧ m ≤ M ∧
    ¬ OccGood (fun u => B u ω) x m} with hEo
  set El : Set Ω' := h1LagEvent d b (T : ℝ) B with hEl
  -- probabilities
  have pEf : P' Ef ≤ ENNReal.ofReal (4 * (d : ℝ) * Real.exp (-((n : ℝ) ^ 4 / 8))) := by
    have := hSRW.base_far (n := n) (by omega) h1t
    exact (ofReal_measureReal (measure_ne_top P' _)).symm.le.trans (ENNReal.ofReal_le_ofReal this)
  have pEfast : P' Efast ≤ ENNReal.ofReal (Real.exp (-(n : ℝ) ^ 4)) := by
    have := hSRW.base_fast hd1 hn2d h1t h4t
    exact (ofReal_measureReal (measure_ne_top P' _)).symm.le.trans (ENNReal.ofReal_le_ofReal this)
  have pEc : P' Ec ≤ ENNReal.ofReal (Real.exp (-(n : ℝ) ^ 4)) := hcplP
  have pEo : P' Eo ≤ ENNReal.ofReal (2 * (2 * R + 1) ^ d * ((M : ℝ) + 1) *
      Real.exp (-(cocc d) * (b - 1) ^ (1 / 10 : ℝ) / 4)) :=
    h1_occ_prob hB (by omega) hR0 (by linarith) hm0b'
  have pEl : P' El ≤ ENNReal.ofReal (es8C94 d * Real.exp (-(b / 2) ^ (es8Zeta d ^ 2 / 4))) := by
    by_cases hT3 : b ^ 3 ≤ (T : ℝ)
    · set ts : ℝ := (T : ℝ) / (2 * b ^ 2) with hts
      have hb2 : 0 < 2 * b ^ 2 := by positivity
      have hts_ge : b / 2 ≤ ts := by
        rw [hts, le_div_iff₀ hb2]; nlinarith [sq_nonneg b]
      have hspec := (es8C94_spec hd1 hd (h1Scaled_isBM hB hb0) ts (by linarith)).2
      refine (measure_mono (fun ω hω => hω.2)).trans (hspec.trans (ENNReal.ofReal_le_ofReal ?_))
      have hq : 0 ≤ es8Zeta d ^ 2 / 4 := by positivity
      have h1 : (b / 2) ^ (es8Zeta d ^ 2 / 4) ≤ ts ^ (es8Zeta d ^ 2 / 4) :=
        Real.rpow_le_rpow (by positivity) hts_ge hq
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by linarith))
        (es8C94_nonneg d)
    · have : El = ∅ := by
        ext ω; simp only [hEl, h1LagEvent, mem_ofPred_eq, mem_empty_iff_false, iff_false]
        exact fun h => hT3 h.1
      rw [this]; simp
  -- the total bound
  have hbudget := h1_budget (d := d) (n := n) (by omega) hn2d
  have hB4' := hB4 n (by omega) h4nβ
  have hR' : R ≤ (n : ℝ) ^ 2 * √β := by
    rw [hRdef]; gcongr
  have ha4 : 2 * (2 * R + 1) ^ d * ((M : ℝ) + 1) *
        Real.exp (-(cocc d) * (b - 1) ^ (1 / 10 : ℝ) / 4) ≤
      2 * (2 * ((n : ℝ) ^ 2 * √β) + 1) ^ d *
        ((2 * ((n : ℝ) ^ 2 * √β) + 1) ^ ((2 * d : ℝ) / 5) + 2) *
        Real.exp (-es8Cocc d * (b - 1) ^ ((1 : ℝ) / 10) / 4) := by
    have hMlt : (M : ℝ) < (2 * R + 1) ^ ((2 * d : ℝ) / 5) + 1 := Nat.ceil_lt_add_one hy0
    have h2 : (2 * R + 1) ^ ((2 * d : ℝ) / 5) ≤
        (2 * ((n : ℝ) ^ 2 * √β) + 1) ^ ((2 * d : ℝ) / 5) :=
      Real.rpow_le_rpow (by positivity) (by linarith) (by positivity)
    have h3 : (2 * R + 1) ^ d ≤ (2 * ((n : ℝ) ^ 2 * √β) + 1) ^ d :=
      pow_le_pow_left₀ (by positivity) (by linarith) d
    have hE : Real.exp (-es8Cocc d * (b - 1) ^ ((1 : ℝ) / 10) / 4) =
        Real.exp (-(cocc d) * (b - 1) ^ (1 / 10 : ℝ) / 4) := rfl
    rw [hE]
    have hE0 := (Real.exp_pos (-(cocc d) * (b - 1) ^ (1 / 10 : ℝ) / 4)).le
    have hM1 : (M : ℝ) + 1 ≤ (2 * ((n : ℝ) ^ 2 * √β) + 1) ^ ((2 * d : ℝ) / 5) + 2 := by
      linarith
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul (mul_le_mul_of_nonneg_left h3 (by norm_num)) hM1 (by positivity)
        (by positivity)) hE0
  have hsum : P' (Ef ∪ Efast ∪ Ec ∪ Eo ∪ El) ≤ ENNReal.ofReal (Real.exp (-(n : ℝ) ^ 3)) := by
    have u1 := measure_union_le (μ := P') (Ef ∪ Efast ∪ Ec ∪ Eo) El
    have u2 := measure_union_le (μ := P') (Ef ∪ Efast ∪ Ec) Eo
    have u3 := measure_union_le (μ := P') (Ef ∪ Efast) Ec
    have u4 := measure_union_le (μ := P') Ef Efast
    refine (u1.trans (add_le_add (u2.trans (add_le_add (u3.trans (add_le_add u4 le_rfl))
      le_rfl)) le_rfl)).trans ?_
    refine (add_le_add (add_le_add (add_le_add (add_le_add pEf pEfast) pEc) pEo) pEl).trans ?_
    have hC := es8C94_nonneg d
    rw [← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    linarith
  -- good sample points
  have hgood : ∀ ω, ω ∉ Ef ∪ Efast ∪ Ec ∪ Eo ∪ El →
      Z' ω ∈ h1Set β T ((9 / 10 + 1 / (n : ℝ)) * (T : ℝ)) := by
    intro ω hω
    simp only [mem_union, not_or] at hω
    obtain ⟨⟨⟨⟨hf, hfa⟩, hc⟩, ho⟩, hl⟩ := hω
    have hg : H1Good n T R M m0 (Z' ω) (fun u => B u ω) := by
      refine ⟨fun s hs => ?_, fun s s' h1 h2 h3 => ?_, fun s hs => ?_, fun x hx m h1 h2 => ?_⟩
      · by_contra hcon
        push Not at hcon
        exact hf ⟨s, hs, hcon⟩
      · by_contra hcon
        push Not at hcon
        exact hfa ⟨s, s', h1, h2, h3, lt_of_lt_of_le hcon (h1_norm_le_l1 _)⟩
      · have hle : ENNReal.ofReal ‖latR (Z' ω s) - √2 • B s ω‖ ≤
            ⨆ t : {t : ℝ≥0 // (t : ℝ) ≤ T},
              ENNReal.ofReal ‖(fun i => ((walk d (N' ω) (t : ℝ≥0) i : ℤ) : ℝ)) -
                √2 • B (t : ℝ≥0) ω‖ :=
          le_iSup (fun t : {t : ℝ≥0 // (t : ℝ) ≤ T} =>
            ENNReal.ofReal ‖(fun i => ((walk d (N' ω) (t : ℝ≥0) i : ℤ) : ℝ)) -
              √2 • B (t : ℝ≥0) ω‖) ⟨s, by exact_mod_cast hs⟩
        by_contra hcon
        push Not at hcon
        exact hc (le_trans (ENNReal.ofReal_le_ofReal hcon) hle)
      · by_contra hcon
        exact ho ⟨x, hx, m, h1, h2, hcon⟩
    have hvol := h1_relTimes_of_good hd1 B ω (Z' ω) T (n := n) (by omega) hβpos hTβ hB1 hB3 hR0
      hM (by exact_mod_cast hm2) (by exact_mod_cast hm5) hm0b hg hl
    refine le_trans (ENNReal.ofReal_le_ofReal ?_) hvol
    have hn20' : (20 : ℝ) ≤ n := by exact_mod_cast hn20
    have : 1 / (n : ℝ) ≤ 1 / 20 := one_div_le_one_div_of_le (by norm_num) hn20'
    have hT0 : (0 : ℝ) ≤ T := T.2
    nlinarith
  -- transfer
  have hΓ : (1 : ℝ≥0∞) ≤ P' {ω | Z' ω ∈ h1Set β T ((9 / 10 + 1 / (n : ℝ)) * (T : ℝ))} +
      ENNReal.ofReal (Real.exp (-(n : ℝ) ^ 3)) := by
    calc (1 : ℝ≥0∞) = P' univ := (measure_univ).symm
      _ ≤ P' ({ω | Z' ω ∈ h1Set β T ((9 / 10 + 1 / (n : ℝ)) * (T : ℝ))} ∪
            (Ef ∪ Efast ∪ Ec ∪ Eo ∪ El)) := by
          refine measure_mono fun ω _ => ?_
          by_cases h : ω ∈ Ef ∪ Efast ∪ Ec ∪ Eo ∪ El
          · exact Or.inr h
          · exact Or.inl (hgood ω h)
      _ ≤ _ := (measure_union_le _ _).trans (add_le_add le_rfl hsum)
  have hex : Real.exp (-(n : ℝ) ^ 3) ≤ 1 := Real.exp_le_one_iff.2 (by
    have : (0 : ℝ) ≤ (n : ℝ) ^ 3 := by positivity
    linarith)
  have hP' : ENNReal.ofReal (1 - Real.exp (-(n : ℝ) ^ 3)) ≤
      P' {ω | Z' ω ∈ h1Set β T ((9 / 10 + 1 / (n : ℝ)) * (T : ℝ))} := by
    have e : ENNReal.ofReal (1 - Real.exp (-(n : ℝ) ^ 3)) +
        ENNReal.ofReal (Real.exp (-(n : ℝ) ^ 3)) = 1 := by
      rw [← ENNReal.ofReal_add (by linarith) (Real.exp_pos _).le]; simp
    rw [← e] at hΓ
    exact (ENNReal.add_le_add_iff_right ENNReal.ofReal_ne_top).1 hΓ
  refine hP'.trans ((srw_h1Set_le_regen hN hTβ _ hSRW).trans (measure_mono fun ω hω => ?_))
  unfold IsRelaxedPath
  rw [scaleIndex_indScale ht1 ht4 n, ← hTr]
  exact hω

end ElboimSly.Paper

end
