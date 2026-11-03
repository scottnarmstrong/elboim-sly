/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Avoid.Claim3
public import Mathlib

/-!
# ES22 §4: Claim 4.3, final form

ES22 Claim 4.3. Survival form, for `W`, and for `x₀ + X̃` with `‖· - x₀‖` for every
process `X̃` with right-continuous paths and the law of `W`.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Paper

open ElboimSly.Cyclic

/-- **ES22 Claim 4.3** (ES22 Claim 4.3, re-tuned: range `t^{θ_H} ≤ L ≤ t^{1/2}`, deviation D11;
`t ≥ 4^{n₀+1}`, deviation F03). -/
theorem es4_claim3 {d : ℕ} (hd : 5 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (β : ℝ) [Fact (0 < β)] (n₀ n : ℕ) (t₀ : ℝ),
      Es4Params d β n₀ n t₀ → ∀ {Ω : Type} [MeasurableSpace Ω] (Pr : Measure Ω)
        (N : Ω → Measure (CycS ℕ d β)), IsPoissonPointProcess N (cycIntensity ℕ d β) Pr →
        ∀ {t L : ℝ}, (4 : ℝ) ^ (n₀ + 1) ≤ t → t ≤ (4 : ℝ) ^ n → t ^ indThetaH ≤ L →
        L ≤ t ^ (1 / 2 : ℝ) →
        ENNReal.ofReal (1 - C * L ^ (d - 2) * t ^ (-((d - 2 : ℕ) : ℝ) / 2)) ≤
          Pr {ω | ∀ s : ℝ, t ≤ s → s ≤ (4 : ℝ) ^ n → L ≤ ‖avoidWalk N ω s‖} ∧
        ∀ {Ω' : Type*} [MeasurableSpace Ω'] (Pr' : Measure Ω') (X : Ω' → ℝ≥0 → Fin d → ℤ)
          (x₀ : Fin d → ℤ), AEMeasurable X Pr' → (∀ ω, IsRCPath (X ω)) →
          Pr'.map X = Pr.map (avoidPath N) →
          ENNReal.ofReal (1 - C * L ^ (d - 2) * t ^ (-((d - 2 : ℕ) : ℝ) / 2)) ≤
            Pr' {ω | ∀ s : ℝ≥0, t ≤ (s : ℝ) → (s : ℝ) ≤ (4 : ℝ) ^ n →
              L ≤ ‖(x₀ + X ω s) - x₀‖} := by
  obtain ⟨C, hC, H⟩ := es4_claim3_bad hd
  refine ⟨C, hC, ?_⟩
  intro β _ n₀ n t₀ hp Ω _ Pr N hN t L ht1 ht2 htL _
  have := hN.isProbabilityMeasure
  have ht1' : (1 : ℝ) < t := lt_of_lt_of_le (one_lt_pow₀ (by norm_num) (by omega)) ht1
  have hL1 : 1 ≤ L :=
    le_trans (Real.one_le_rpow ht1'.le (by norm_num [indThetaH])) htL
  have hc : 0 ≤ C * L ^ (d - 2) * t ^ (-((d - 2 : ℕ) : ℝ) / 2) := by
    have : 0 < t := by linarith
    have : 0 < L := by linarith
    positivity
  have hbad := H β n₀ n t₀ hp Pr N hN ht1 ht2 htL
  refine ⟨?_, ?_⟩
  · have := ofReal_one_sub_le_compl (μ := Pr) measure_univ hc hbad
    refine this.trans (measure_mono ?_)
    intro ω hω s hs1 hs2
    by_contra hcon
    exact hω ⟨s, hs1, hs2, not_le.1 hcon⟩
  · intro Ω' _ Pr' X x₀ hX hrc hlaw
    have hu : Pr' univ = 1 := by
      have := Measure.map_apply_of_aemeasurable hX MeasurableSet.univ
      rw [hlaw, Measure.map_apply_of_aemeasurable (aemeasurable_avoidPath hN)
        MeasurableSet.univ] at this
      simpa using this.symm
    set a : ℝ≥0 := t.toNNReal with ha
    set b : ℝ≥0 := ((4 : ℝ) ^ n).toNNReal with hb
    have haR : (a : ℝ) = t := Real.coe_toNNReal _ (by linarith)
    have hbR : (b : ℝ) = 4 ^ n := Real.coe_toNNReal _ (by positivity)
    have hab : a ≤ b := by rw [← NNReal.coe_le_coe, haR, hbR]; exact ht2
    have hq : Pr' {ω | ∃ s : ℝ≥0, t ≤ (s : ℝ) ∧ (s : ℝ) ≤ (4 : ℝ) ^ n ∧
        ‖(x₀ + X ω s) - x₀‖ < L} ≤
        ENNReal.ofReal (C * L ^ (d - 2) * t ^ (-((d - 2 : ℕ) : ℝ) / 2)) := by
      have e : {ω | ∃ s : ℝ≥0, t ≤ (s : ℝ) ∧ (s : ℝ) ≤ (4 : ℝ) ^ n ∧
          ‖(x₀ + X ω s) - x₀‖ < L} = {ω | ∃ q ∈ qSet a b, ‖X ω q‖ < L} := by
        ext ω
        simp only [add_sub_cancel_left, mem_ofPred_eq]
        have := exists_Icc_iff_qSet (hrc ω) hab (fun v => ‖v‖ < L)
        rw [← this]
        constructor
        · rintro ⟨s, h1, h2, h3⟩
          exact ⟨s, by rw [← NNReal.coe_le_coe, haR]; exact h1,
            by rw [← NNReal.coe_le_coe, hbR]; exact h2, h3⟩
        · rintro ⟨s, h1, h2, h3⟩
          exact ⟨s, by rw [← haR]; exact_mod_cast h1, by rw [← hbR]; exact_mod_cast h2, h3⟩
      rw [e, prob_cyl_eq hX (aemeasurable_avoidPath hN) hlaw a b (fun v => ‖v‖ < L)]
      refine le_trans (measure_mono ?_) hbad
      rintro ω ⟨q, hq, hqL⟩
      have := mem_qSet_Icc hab hq
      exact ⟨(q : ℝ), by rw [← haR]; exact_mod_cast this.1,
        by rw [← hbR]; exact_mod_cast this.2, hqL⟩
    have := ofReal_one_sub_le_compl (μ := Pr') hu hc hq
    refine this.trans (measure_mono ?_)
    intro ω hω s hs1 hs2
    by_contra hcon
    exact hω ⟨s, hs1, hs2, not_le.1 hcon⟩

end ElboimSly.Paper

end
