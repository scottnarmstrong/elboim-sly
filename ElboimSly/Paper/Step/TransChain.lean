/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Step.TransNat
public import ElboimSly.Paper.Step.Cor72
public import ElboimSly.Paper.Step.DrivenLaw
public import ElboimSly.Foundations.PPP.Existence
public import Mathlib

/-!
# The chain of estimates of Lemma 7.7 (conditional on Corollary 7.2)

ES22 Lemma 7.7. `trans_chain` combines Corollary 7.2 (as `StepCor72`, with `ℓ = 2` lengths
`(s₁, r)`) with the independence estimate `trans_key`:
`ℙ(W(t) = u) ≤ e^{-c n³} + (2R+1)^d (ℙ(‖W(r)‖ > ρ) + q ℙ(‖W(s₁) - v‖ ≤ ρ))`, where
`R = 2 t_n^{2ε}`, `ℙ(W(r) = x) ≤ q` and the sup over `v` of the last probability is at most `α`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology ElboimSly.Cyclic ElboimSly.SRW
open scoped NNReal ENNReal

namespace ElboimSly.Paper.Step

open ElboimSly.Paper

variable {d : ℕ} {β : ℝ} [Fact (0 < β)]

theorem trans_chain {cCat : ℝ} {βCat : ℕ → ℝ} (hCor : StepCor72 d cCat βCat)
    {n₁ n : ℕ} {t₀ : ℝ} (hR : StepRegime d n₁ β n t₀) (hβc : βCat n₁ ≤ β)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {N : Ω → Measure (ℕ × RingSpace d β)}
    (hN : IsPoissonPointProcess N ((Measure.count : Measure ℕ).prod (ringIntensity d β)) P)
    {s₁ r t : ℝ} (hs1 : 0 < s₁) (hr : 0 < r) (hst : s₁ + r = t) (ht : t ≤ indScale t₀ n)
    {q a2 α : ℝ≥0∞}
    (hq : ∀ x : Fin d → ℤ, P {ω | regenWalk (fun k => copyEnv (N ω) k) r = x} ≤ q)
    (ρ : ℝ) (hA2 : P {ω | ρ < ‖regenWalk (fun k => copyEnv (N ω) k) r‖} ≤ a2)
    (hα : ∀ v : Fin d → ℤ,
      P {ω | ‖regenWalk (fun k => copyEnv (N ω) k) s₁ - v‖ ≤ ρ} ≤ α) (u : Fin d → ℤ) :
    P {ω | regenWalk (fun k => copyEnv (N ω) k) t = u} ≤
      ENNReal.ofReal (Real.exp (-(cCat * (n : ℝ) ^ 3))) +
        ENNReal.ofReal ((2 * (2 * indScale t₀ n ^ (2 * heavyEps d)) + 1) ^ d) *
          (a2 + q * α) := by
  have hPe := hN.isProbabilityMeasure
  obtain ⟨Ω', _, P', N₀, hP', hN₀, -⟩ := exists_isPoissonPointProcess (clockIntensity (Dir d))
  have hY : IsSRW P' (canonical d N₀) := canonical_isSRW hN₀
  have hYp : ∀ ω, canonical d N₀ ω ∈ StepPath d := fun ω => walkPath_isDriving (N₀ ω)
  have hP'prob : IsProbabilityMeasure P' := hY.isProbabilityMeasure
  set Y := canonical d N₀ with hYdef
  set s₁' : ℝ≥0 := s₁.toNNReal with hs₁'
  set r' : ℝ≥0 := r.toNNReal with hr'
  have hs₁c : (s₁' : ℝ) = s₁ := Real.coe_toNNReal s₁ hs1.le
  have hrc : (r' : ℝ) = r := Real.coe_toNNReal r hr.le
  have hs₁pos : 0 < s₁' := by rw [← NNReal.coe_pos, hs₁c]; exact hs1
  have hrpos : 0 < r' := by rw [← NNReal.coe_pos, hrc]; exact hr
  set s : ℕ → ℝ≥0 := fun j => if j = 0 then s₁' else r' with hs
  have hspos : ∀ j, 0 < s j := fun j => by
    by_cases hj : j = 0 <;> simp [hs, hj, hs₁pos, hrpos]
  have hP2 : stepPartial s 2 = s₁' + r' := by
    simp [stepPartial, Finset.sum_range_succ, hs]
  have hP2c : ((stepPartial s 2 : ℝ≥0) : ℝ) = t := by
    rw [hP2]; push_cast; rw [hs₁c, hrc, hst]
  set t' : ℝ≥0 := s₁' + r' with ht'
  have ht'c : (t' : ℝ) = t := by rw [ht']; push_cast; rw [hs₁c, hrc, hst]
  -- Step A: transfer to the SRW space
  have hlaw := stepReg_law hY hYp hN
  have hm : Measurable fun ω (t : ℝ≥0) => stepReg β (Y ω) t :=
    measurable_stepReg_path hY.1 fun ω => (hYp ω).toIsRegPath
  have hEm : MeasurableSet {w : ℝ≥0 → Fin d → ℤ | w t' = u} := by
    have : {w : ℝ≥0 → Fin d → ℤ | w t' = u} = (fun w => w t') ⁻¹' {u} := rfl
    rw [this]; exact measurable_pi_apply t' (measurableSet_singleton u)
  have hae := aemeasurable_ppPath hN
  have stepA : P {ω | regenWalk (fun k => copyEnv (N ω) k) t = u} =
      P' {ω | stepReg β (Y ω) t' = u} := by
    have hlaw' : P'.map (fun ω (t : ℝ≥0) => stepReg β (Y ω) t) = P.map (ppPath N) := hlaw
    have e1 : P' {ω | stepReg β (Y ω) t' = u} = (P'.map fun ω (t : ℝ≥0) => stepReg β (Y ω) t)
        {w | w t' = u} := by rw [Measure.map_apply hm hEm]; rfl
    have e2 : P {ω | regenWalk (fun k => copyEnv (N ω) k) t = u} = (P.map (ppPath N))
        {w | w t' = u} := by
      rw [Measure.map_apply_of_aemeasurable hae hEm]
      simp only [preimage_ofPred_eq, ppPath, ht'c]
    rw [e1, e2, hlaw']
  rw [stepA]
  -- Step B: Corollary 7.2
  have hcor := hCor n₁ hR.1 β n t₀ hβc hR Ω' P' Y hY hYp 0 2 s (by norm_num) hspos
    (by rw [hP2c]; exact ht)
  set Ec : Set Ω' := {ω | ∃ u' : ℝ≥0, u' ≤ stepPartial s 2 ∧
    ((2 : ℕ) : ℝ) * indScale t₀ n ^ (2 * heavyEps d) ≤
      ‖stepReg β (stepShift 0 (Y ω)) u' - stepNatTilde β 0 s 2 (Y ω) u'‖} with hEc
  set R : ℝ := 2 * indScale t₀ n ^ (2 * heavyEps d) with hRdef
  have htn0 : 0 ≤ indScale t₀ n := by
    have ht0 : 0 < t₀ := lt_trans one_pos hR.2.2.2.1.1
    unfold indScale; positivity
  have hR0 : 0 ≤ R := by rw [hRdef]; have := Real.rpow_nonneg htn0 (2 * heavyEps d); positivity
  set Bs := (lattice_ball_finite u R).toFinset with hBs
  have hsub : {ω | stepReg β (Y ω) t' = u} ⊆ Ec ∪ ⋃ v ∈ Bs,
      {ω | stepNatTilde β 0 s 2 (Y ω) (s₁' + r') = v} := by
    intro ω hω
    by_cases hbad : ω ∈ Ec
    · exact Or.inl hbad
    · refine Or.inr (mem_iUnion₂.2 ⟨stepNatTilde β 0 s 2 (Y ω) t', ?_, rfl⟩)
      simp only [hBs, Set.Finite.mem_toFinset, mem_ofPred_eq]
      have h1 : ‖stepReg β (stepShift 0 (Y ω)) t' - stepNatTilde β 0 s 2 (Y ω) t'‖ < R := by
        by_contra hcon
        rw [not_lt] at hcon
        apply hbad
        refine ⟨t', by rw [hP2], ?_⟩
        simpa [hRdef] using hcon
      rw [stepShift, shiftPath_zero (hYp ω)] at h1
      have h2 : stepReg β (Y ω) t' = u := hω
      rw [h2] at h1
      rw [norm_sub_rev] at h1
      exact h1.le
  have hEc_le : P' Ec ≤ ENNReal.ofReal (Real.exp (-(cCat * (n : ℝ) ^ 3))) := by
    have : P' Ec = ENNReal.ofReal (P'.real Ec) := by
      rw [Measure.real, ENNReal.ofReal_toReal (measure_ne_top _ _)]
    rw [this]
    refine ENNReal.ofReal_le_ofReal (hcor.trans (le_of_eq ?_))
    norm_num
  have hq' : ∀ x : Fin d → ℤ,
      P {ω | regenWalk (fun k => copyEnv (N ω) k) ((r' : ℝ≥0) : ℝ) = x} ≤ q := by
    rw [hrc]; exact hq
  have hterm : ∀ v : Fin d → ℤ,
      P' {ω | stepNatTilde β 0 s 2 (Y ω) (s₁' + r') = v} ≤ a2 + q * α := by
    intro v
    refine (trans_key hY hYp hN hrpos hq' v ρ).trans (add_le_add ?_ ?_)
    · rw [hrc]; exact hA2
    · gcongr
      rw [hs₁c]; exact hα v
  have hcard : (Bs.card : ℝ≥0∞) ≤ ENNReal.ofReal ((2 * R + 1) ^ d) := by
    rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal (ncard_lattice_ball_le u hR0)
  calc P' {ω | stepReg β (Y ω) t' = u} ≤ P' (Ec ∪ ⋃ v ∈ Bs,
        {ω | stepNatTilde β 0 s 2 (Y ω) (s₁' + r') = v}) := measure_mono hsub
    _ ≤ P' Ec + P' (⋃ v ∈ Bs, {ω | stepNatTilde β 0 s 2 (Y ω) (s₁' + r') = v}) :=
        measure_union_le _ _
    _ ≤ P' Ec + ∑ v ∈ Bs, P' {ω | stepNatTilde β 0 s 2 (Y ω) (s₁' + r') = v} := by
        gcongr; exact measure_biUnion_finset_le _ _
    _ ≤ ENNReal.ofReal (Real.exp (-(cCat * (n : ℝ) ^ 3))) + ∑ v ∈ Bs, (a2 + q * α) := by
        gcongr with v hv
        exact hterm v
    _ = ENNReal.ofReal (Real.exp (-(cCat * (n : ℝ) ^ 3))) + (Bs.card : ℝ≥0∞) * (a2 + q * α) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := by gcongr

end ElboimSly.Paper.Step
