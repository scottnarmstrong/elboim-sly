/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.SRW.FarWindows
public import Mathlib

/-!
# Claim 2.3 for the SRW

ES22 Claim 2.3.  `fastTime γ L = inf {t > 0 : ∃ s ∈ [t-1,t], ‖γ t - γ s‖ ≥ L}` with
`γ s := 0` for `s < 0`.  (The maximum over `s ∈ [t-1,t]` is read as an existential quantifier.)
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ElboimSly
namespace SRW

variable {d : ℕ}

/-- The path extended by `0` to negative times. -/
noncomputable def extPath (γ : PathSpace d) (s : ℝ) : Fin d → ℤ :=
  if 0 ≤ s then γ s.toNNReal else 0

/-- Times at which the path moves by at least `L` within a unit time window. -/
def fastSet (γ : PathSpace d) (L : ℝ) : Set ℝ≥0 :=
  {t | 0 < t ∧ ∃ s : ℝ, (t : ℝ) - 1 ≤ s ∧ s ≤ t ∧ L ≤ ‖γ t - extPath γ s‖}

/-- Hitting the history; moving fast (`tfast`), for a path. -/
noncomputable def fastTime (γ : PathSpace d) (L : ℝ) : ℝ≥0∞ :=
  ⨅ t ∈ fastSet γ L, (t : ℝ≥0∞)

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {Z : Ω → PathSpace d}

theorem IsSRW.ae_zero (hZ : IsSRW P Z) : ∀ᵐ ω ∂P, Z ω 0 = 0 := by
  have hm : MeasurableSet {γ : PathSpace d | γ 0 ≠ 0} :=
    (measurableSet_singleton (0 : Fin d → ℤ)).compl.preimage (measurable_pi_apply (0 : ℝ≥0))
  obtain ⟨Ω', _, P', N', hN', hE⟩ := hZ.exists_canonical
  rw [ae_iff]
  have : {ω | ¬ Z ω 0 = 0} = Z ⁻¹' {γ : PathSpace d | γ 0 ≠ 0} := rfl
  rw [this, hE _ hm]
  have h2 : ∀ᵐ ω ∂P', canonical d N' ω 0 = 0 := Filter.Eventually.of_forall fun ω => by
    simp [canonical, walk_zero]
  rw [ae_iff] at h2
  exact h2

theorem fastTime_le_imp {γ : PathSpace d} (hγ : IsRegularPath γ) (h0 : γ 0 = 0) {L : ℝ}
    (hL : 0 < L) {t : ℝ≥0} (h : fastTime γ L ≤ t) :
    ∃ s s', s ≤ s' ∧ s' ≤ t ∧ s' - s ≤ 1 ∧ L ≤ ‖γ s' - γ s‖ := by
  obtain ⟨δ, hδ, hc⟩ := hγ t
  have hlt : fastTime γ L < ((t + δ : ℝ≥0) : ℝ≥0∞) :=
    lt_of_le_of_lt h (by exact_mod_cast lt_add_of_pos_right t hδ)
  unfold fastTime at hlt
  simp only [iInf_lt_iff] at hlt
  obtain ⟨t₁, ⟨ht₁, s₁, hs1, hs2, hL1⟩, hlt1⟩ := hlt
  have hlt1' : t₁ < t + δ := by exact_mod_cast hlt1
  have hs₁ : (0 : ℝ) ≤ (max s₁ 0) := le_max_right _ _
  set s : ℝ≥0 := (max s₁ 0).toNNReal with hs
  have hsr : (s : ℝ) = max s₁ 0 := Real.coe_toNNReal _ hs₁
  have hext : extPath γ s₁ = γ s := by
    unfold extPath
    by_cases h' : 0 ≤ s₁
    · rw [ite_eq_left h']; congr 1; rw [hs, max_eq_left h']
    · rw [ite_eq_right h']
      have : s = 0 := by
        rw [hs, max_eq_right (not_le.1 h').le]; simp
      rw [this, h0]
  have ht₁r : (0 : ℝ) < t₁ := ht₁
  rcases le_or_gt t₁ t with hle | hgt
  · refine ⟨s, t₁, ?_, hle, ?_, ?_⟩
    · rw [← NNReal.coe_le_coe, hsr]; exact max_le hs2 ht₁r.le
    · rw [← NNReal.coe_le_coe, NNReal.coe_sub (by rw [← NNReal.coe_le_coe, hsr]; exact max_le hs2 ht₁r.le), hsr]
      push_cast
      rcases le_total s₁ 0 with h' | h'
      · rw [max_eq_right h']; linarith
      · rw [max_eq_left h']; linarith
    · rw [← hext]; exact hL1
  · have hγt : γ t₁ = γ t := hc t₁ hgt.le hlt1'
    have ht₁δ : (t₁ : ℝ) < t + δ := by exact_mod_cast hlt1'
    have hs₁t : s₁ ≤ t := by
      by_contra hcon
      push Not at hcon
      have h' : 0 ≤ s₁ := by linarith [t.2]
      have hw : γ s₁.toNNReal = γ t := hc _
        (by rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ h']; exact hcon.le)
        (by rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ h']; push_cast; linarith)
      have : extPath γ s₁ = γ t₁ := by unfold extPath; rw [ite_eq_left h', hw, hγt]
      rw [this, sub_self, norm_zero] at hL1
      linarith
    refine ⟨s, t, ?_, le_rfl, ?_, ?_⟩
    · rw [← NNReal.coe_le_coe, hsr]; exact max_le hs₁t t.2
    · have hst : s ≤ t := by rw [← NNReal.coe_le_coe, hsr]; exact max_le hs₁t t.2
      rw [← NNReal.coe_le_coe, NNReal.coe_sub hst, hsr]
      push_cast
      have htt : (t : ℝ) < t₁ := by exact_mod_cast hgt
      rcases le_total s₁ 0 with h' | h'
      · rw [max_eq_right h']; linarith
      · rw [max_eq_left h']; linarith
    · rw [← hγt, ← hext]; exact hL1

/-- ES22 Claim 2.3: `P(tfast(L) ≤ t) ≤ (t+1) e^{4d(e-1)} e^{-L}`. -/
theorem IsSRW.fast (hZ : IsSRW P Z) {L : ℝ} (hL : 0 < L) (t : ℝ≥0) :
    P.real {ω | fastTime (Z ω) L ≤ t} ≤
      ((t : ℝ) + 1) * Real.exp (4 * d * (Real.exp 1 - 1)) * Real.exp (-L) := by
  have := hZ.isProbabilityMeasure
  have hsub : {ω | fastTime (Z ω) L ≤ t} ≤ᵐ[P]
      {ω | ∃ s s', s ≤ s' ∧ s' ≤ t ∧ s' - s ≤ 1 ∧ L ≤ l1 (Z ω s' - Z ω s)} := by
    filter_upwards [hZ.ae_zero] with ω h0 h
    obtain ⟨s, s', h1, h2, h3, h4⟩ := fastTime_le_imp (hZ.2.1 ω) h0 hL h
    exact ⟨s, s', h1, h2, h3, h4.trans (norm_le_l1 _)⟩
  refine (measureReal_mono_ae' hsub).trans ?_
  have := hZ.unit_windows t 1 one_pos L
  refine this.trans (le_of_eq ?_)
  simp only [NNReal.coe_one, div_one, mul_one]
  rw [show ∀ x y : ℝ, Real.exp (x - y) = Real.exp x * Real.exp (-y) from fun x y => by
    rw [← Real.exp_add]; ring_nf, ← mul_assoc]

end SRW
end ElboimSly
