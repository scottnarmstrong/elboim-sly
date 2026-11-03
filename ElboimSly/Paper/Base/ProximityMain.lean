/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Base.Proximity
public import Mathlib

/-!
# Proximity times of an independent walk: the probability bound

Proximity times of an independent walk (ES22 §8).

* `es8_proximity`: `P(|U| > n⁴ 3.89ⁿ) ≤ e^{-n⁴} + 2^{-n⁴}`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Paper

open ElboimSly.SRW ElboimSly.Paper.Base

variable {d : ℕ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {Ñ : Ω → Measure ((Dir d × Fin 2) × ℝ)}

/-- Proximity times of an independent walk.  Let `d ≥ 5`, `n ≥ max(n_C(d), n_2(d))`, `t₀ ∈ (1, 4]`,
`T = 2 t'_n = lem82T n t₀`, `L ∈ [0, T]`, `V = {a + X₁(s) : s ∈ [0, L]}` and
`U = {s ∈ [0, T] : d(b + X₂(s), V) ≤ 1.9^{n+1}}` (`baseProxSet`).  Then
`P(|U| > n⁴ 3.89ⁿ) ≤ e^{-n⁴} + 2^{-n⁴}`. -/
theorem es8_proximity (h : IsPoissonPointProcess Ñ (clockIntensity (Dir d × Fin 2)) P)
    (hd : 5 ≤ d) {n : ℕ} (hnC : lem82nC d ≤ n) (hn2 : lem82n2 d ≤ n) {t₀ : ℝ}
    (ht1 : 1 < t₀) (ht4 : t₀ ≤ 4) (a b : Fin d → ℤ) {L : ℝ≥0}
    (hL : L ≤ (lem82T n t₀).toNNReal) :
    P {ω | (n : ℝ) ^ 4 * (3.89 : ℝ) ^ n <
        (volume (baseProxSet Ñ a b (lem82T n t₀).toNNReal L ((1.9 : ℝ) ^ (n + 1)) ω)).toReal} ≤
      ENNReal.ofReal (Real.exp (-(n : ℝ) ^ 4)) + ENNReal.ofReal ((1 / 2 : ℝ) ^ (n ^ 4)) := by
  have : NeZero d := ⟨by omega⟩
  have hX0 := drivers_isSRW h 0
  have hX1 := drivers_isSRW h 1
  have hF := drivers_admissible h 1
  have := hX0.isProbabilityMeasure
  set T : ℝ≥0 := (lem82T n t₀).toNNReal with hT
  set hh : ℝ≥0 := ((3.89 : ℝ) ^ n).toNNReal with hhh
  set ρ : ℝ := (1.9 : ℝ) ^ (n + 1) with hρ
  -- the good event, a measurable version
  obtain ⟨V, hVm, hV⟩ := isRegSet_pair (d := d) (fun x y => (1.9 : ℝ) ^ n < ‖y - x‖) T
    (lem82h n)
  set A : Set Ω := {ω | drvX Ñ 0 ω ∉ V} with hA
  have hm0 : Measurable[drvFil Ñ 1 0] (drvX Ñ 0) := by
    have := comap_measurable (m := (inferInstance : MeasurableSpace (PathSpace d)))
      (drvX Ñ 0)
    rw [drvFil_one]
    exact this.mono le_sup_left le_rfl
  have hAmeas : MeasurableSet[drvFil Ñ 1 0] A := (hm0 hVm).compl
  have hAcP : P Aᶜ ≤ ENNReal.ofReal (Real.exp (-(n : ℝ) ^ 4)) := by
    set Y := drvX Ñ 0 with hY
    have hc := lemma82_c hX0 hnC ht1 ht4 Y
      (measurable_pi_iff.2 fun s => (measurable_pi_apply (min s T)).comp hX0.1)
      (fun ω => (hX0.2.1 ω).stop T) rfl
    have hsub : Aᶜ ⊆ {ω | ∃ s s' : ℝ≥0, s ≤ s' ∧ s' ≤ T ∧ s' - s ≤ lem82h n ∧
        (1.9 : ℝ) ^ n < ‖Y ω s' - Y ω s‖} := by
      intro ω hω
      have hω' : Y ω ∈ V := not_not.1 hω
      obtain ⟨s, s', -, h1, h2, h3, h4⟩ := (hV _ (hX0.2.1 ω)).2 hω'
      exact ⟨s, s', h1, h2, h3, h4⟩
    calc P Aᶜ ≤ P _ := measure_mono hsub
      _ = ENNReal.ofReal (P.real _) := (ofReal_measureReal (measure_ne_top P _)).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal hc
  -- covering by `A`
  have hcov : ∀ ω ∈ A, ∀ s s' : ℝ≥0, s ≤ s' → s' ≤ T → s' - s ≤ lem82h n →
      ‖(fun ω s => a + drvX Ñ 0 ω (min s L)) ω s' - (fun ω s => a + drvX Ñ 0 ω (min s L)) ω s‖
        ≤ (1.9 : ℝ) ^ n := by
    intro ω hω s s' hss hs'T hsh
    by_contra hcon
    push Not at hcon
    refine hω ((hV _ (hX0.2.1 ω)).1 ⟨min s L, min s' L, bot_le, min_le_min_right L hss,
      (min_le_right _ _).trans hL, (min_sub_min_le s s' L hss).trans hsh, ?_⟩)
    simpa [add_sub_add_left_eq_sub] using hcon
  -- the stopping times
  have hstop : ∀ i, IsStoppingTime hF.filtration
      (hitSeq (proxY Ñ b) (proxK Ñ a L ρ) hh i) :=
    hitSeq_isStoppingTime hF.filtration (fun t => measurable_proxY t b)
      (isStepPath_proxY b) (fun z => measurableSet_proxK_mem h a L ρ z)
  have hY₀ : Measurable[drvFil Ñ 1 0] (fun ω s => a + drvX Ñ 0 ω (min s L)) :=
    measurable_shiftStop_gen (m := drvFil Ñ 1 0) (measurable_drvX0_comap) a L
  have hdecay : ∀ i, P (A ∩ {ω | hitSeq (proxY Ñ b) (proxK Ñ a L ρ) hh i ω < ⊤}) ≤
      (ENNReal.ofReal (1 / 2)) ^ i := by
    intro i
    induction i with
    | zero => simpa using prob_le_one
    | succ i ih =>
      have hAs : MeasurableSet[(hstop i).measurableSpace] A :=
        (hstop i).le_measurableSpace_of_const_le (i := 0) (fun ω => bot_le) _ hAmeas
      have hle := lemma82_e hX1 hF hd hn2 ht1 ht4 (hstop i)
        (fun ω s => a + drvX Ñ 0 ω (min s L)) hY₀ (fun _ => b) (measurable_const) A
        (fun ω hω s s' h1 h2 h3 => hcov ω hω s s' h1 h2 h3) hAs subset_rfl
      have hsub : A ∩ {ω | hitSeq (proxY Ñ b) (proxK Ñ a L ρ) hh (i + 1) ω < ⊤} ⊆
          A ∩ {ω | hitSeq (proxY Ñ b) (proxK Ñ a L ρ) hh i ω < ⊤} ∩
            {ω | ∃ s : ℝ≥0, (3.89 : ℝ) ^ n ≤ s ∧ ∃ s' : ℝ≥0, s' ≤ (lem82T n t₀).toNNReal ∧
              ‖(fun _ => b) ω + drvX Ñ 1 ω (stopReal (hitSeq (proxY Ñ b) (proxK Ñ a L ρ) hh i) ω
                + s) - (fun ω s => a + drvX Ñ 0 ω (min s L)) ω s'‖ ≤ (1.9 : ℝ) ^ (n + 1)} := by
        rintro ω ⟨hωA, hωlt⟩
        have hne : hitSeq (proxY Ñ b) (proxK Ñ a L ρ) hh (i + 1) ω ≠ ⊤ := ne_of_lt hωlt
        obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.1 hne
        obtain ⟨hz, hle', y, hyL, hy⟩ := hitAfter_attained (isStepPath_proxY b)
          (K := proxK Ñ a L ρ) (σ := hitSeq (proxY Ñ b) (proxK Ñ a L ρ) hh i) (h := hh)
          (ω := ω) (t := t) ht.symm
        have hst : stopReal (hitSeq (proxY Ñ b) (proxK Ñ a L ρ) hh i) ω ≤ t :=
          le_of_add_le_left hle'
        refine ⟨⟨hωA, lt_top_iff_ne_top.2 hz⟩, t - stopReal (hitSeq (proxY Ñ b)
          (proxK Ñ a L ρ) hh i) ω, ?_, y, hyL.trans hL, ?_⟩
        · exact (Real.toNNReal_le_iff_le_coe).1 (le_tsub_of_add_le_left hle')
        · have e1 : stopReal (hitSeq (proxY Ñ b) (proxK Ñ a L ρ) hh i) ω +
              (t - stopReal (hitSeq (proxY Ñ b) (proxK Ñ a L ρ) hh i) ω) = t :=
            add_tsub_cancel_of_le hst
          simp only [e1, min_eq_left hyL]
          exact hy
      calc P (A ∩ {ω | hitSeq (proxY Ñ b) (proxK Ñ a L ρ) hh (i + 1) ω < ⊤})
          ≤ P _ := measure_mono hsub
        _ ≤ ENNReal.ofReal (1 / 2) * P (A ∩ {ω | hitSeq (proxY Ñ b) (proxK Ñ a L ρ) hh i ω < ⊤}) :=
            hle
        _ ≤ ENNReal.ofReal (1 / 2) * (ENNReal.ofReal (1 / 2)) ^ i := by gcongr
        _ = (ENNReal.ofReal (1 / 2)) ^ (i + 1) := by rw [pow_succ']
  -- assembly
  have hE : {ω | (n : ℝ) ^ 4 * (3.89 : ℝ) ^ n < (volume (baseProxSet Ñ a b T L ρ ω)).toReal} ⊆
      Aᶜ ∪ (A ∩ {ω | hitSeq (proxY Ñ b) (proxK Ñ a L ρ) hh (n ^ 4) ω < ⊤}) := by
    intro ω hω
    by_cases hωA : ω ∈ A
    · right
      refine ⟨hωA, ?_⟩
      by_contra hlt
      have htop : hitSeq (proxY Ñ b) (proxK Ñ a L ρ) hh (n ^ 4) ω = ⊤ := by
        simpa using hlt
      have hv := volume_proxSet_le (Ñ := Ñ) b a T L ρ hh (n ^ 4) ω htop
      have e : ((n ^ 4 : ℕ) : ℝ) * (hh : ℝ) = (n : ℝ) ^ 4 * (3.89 : ℝ) ^ n := by
        rw [hhh, Real.coe_toNNReal _ (by positivity)]; push_cast; ring
      rw [e] at hv
      exact absurd hω (not_lt.2 hv)
    · left; exact hωA
  calc P _ ≤ P (Aᶜ ∪ (A ∩ {ω | hitSeq (proxY Ñ b) (proxK Ñ a L ρ) hh (n ^ 4) ω < ⊤})) :=
        measure_mono hE
    _ ≤ P Aᶜ + P (A ∩ {ω | hitSeq (proxY Ñ b) (proxK Ñ a L ρ) hh (n ^ 4) ω < ⊤}) :=
        measure_union_le _ _
    _ ≤ ENNReal.ofReal (Real.exp (-(n : ℝ) ^ 4)) + ENNReal.ofReal ((1 / 2 : ℝ) ^ (n ^ 4)) := by
        gcongr
        rw [ENNReal.ofReal_pow (by norm_num)]; exact hdecay _

end ElboimSly.Paper
