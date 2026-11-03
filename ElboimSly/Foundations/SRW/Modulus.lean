/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.SRW.Maximal
public import ElboimSly.Foundations.SRW.FarWindows
public import Mathlib

/-!
# Modulus of continuity

Modulus of continuity.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ElboimSly
namespace SRW

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {Z : Ω → PathSpace d}

theorem IsRegularPath.theta {γ : PathSpace d} (hγ : IsRegularPath γ) (a : ℝ≥0) :
    IsRegularPath (SRW.theta a γ) := by
  intro t
  obtain ⟨δ, hδ, h⟩ := hγ (a + t)
  refine ⟨δ, hδ, fun s hs1 hs2 => ?_⟩
  unfold SRW.theta
  rw [h (a + s) (by gcongr) (by rw [add_assoc]; gcongr)]

/-- The shifted process `θ_a Z` of an SRW is an SRW (Markov property at the fixed time `a`). -/
theorem IsSRW.theta (hZ : IsSRW P Z) (a : ℝ≥0) : IsSRW P (fun ω => SRW.theta a (Z ω)) := by
  refine ⟨(measurable_theta a).comp hZ.1, fun ω => (hZ.2.1 ω).theta a, ?_⟩
  obtain ⟨Ω', _, P', N', hN', hlaw⟩ := hZ.2.2
  exact ⟨Ω', inferInstance, P', N', hN', (hZ.map_theta a).trans hlaw⟩

/-- Modulus of continuity. -/
theorem IsSRW.modulus [NeZero d] (hZ : IsSRW P Z) (T h : ℝ≥0) (hh : 0 < h) {a : ℝ} (ha : 0 ≤ a) :
    P.real {ω | ∃ s s', s ≤ s' ∧ s' ≤ T ∧ s' - s ≤ h ∧ a ≤ ‖Z ω s' - Z ω s‖} ≤
      ((T : ℝ) / h + 1) * (4 * d * Real.exp (-min (a ^ 2 / (64 * h)) (a / 4))) := by
  have := hZ.isProbabilityMeasure
  have hh' : (0 : ℝ) < h := hh
  set K : ℕ := ⌊(T : ℝ) / h⌋₊ with hK
  let A : ℕ → Set Ω := fun k => {ω | ∃ u, u ≤ 2 * h ∧ a / 2 ≤ ‖SRW.theta ((k : ℝ≥0) * h) (Z ω) u‖}
  have hsub : {ω | ∃ s s', s ≤ s' ∧ s' ≤ T ∧ s' - s ≤ h ∧ a ≤ ‖Z ω s' - Z ω s‖} ⊆
      ⋃ k ∈ Finset.range (K + 1), A k := by
    rintro ω ⟨s, s', hss', hs'T, hsh, hn⟩
    simp only [mem_iUnion]
    have hss'r : (s : ℝ) ≤ s' := by exact_mod_cast hss'
    have hshr : (s' : ℝ) - s ≤ h := by
      have := hsh
      rw [← NNReal.coe_le_coe, NNReal.coe_sub hss'] at this
      exact this
    set k : ℕ := ⌊(s : ℝ) / h⌋₊ with hk
    have hk1 : (k : ℝ) * h ≤ s := by
      have := Nat.floor_le (show 0 ≤ (s : ℝ) / h by positivity)
      rw [← hk, le_div_iff₀ hh'] at this; exact this
    have hk2 : (s : ℝ) < (k + 1) * h := by
      have := Nat.lt_floor_add_one ((s : ℝ) / h)
      rw [← hk, div_lt_iff₀ hh'] at this; exact this
    have hkK : k ≤ K := by
      apply Nat.floor_le_floor
      exact div_le_div_of_nonneg_right (by exact_mod_cast hss'.trans hs'T) hh'.le
    have hks : (k : ℝ≥0) * h ≤ s := by
      rw [← NNReal.coe_le_coe]; push_cast; exact hk1
    have hks' : (k : ℝ≥0) * h ≤ s' := hks.trans hss'
    refine ⟨k, Finset.mem_range.2 (Nat.lt_succ_of_le hkK), ?_⟩
    set u := s - (k : ℝ≥0) * h with hu
    set u' := s' - (k : ℝ≥0) * h with hu'
    have hu2 : u ≤ 2 * h := by
      rw [← NNReal.coe_le_coe, hu, NNReal.coe_sub hks]; push_cast; nlinarith
    have hu2' : u' ≤ 2 * h := by
      rw [← NNReal.coe_le_coe, hu', NNReal.coe_sub hks']; push_cast; nlinarith
    have e1 : (k : ℝ≥0) * h + u = s := by rw [hu]; exact add_tsub_cancel_of_le hks
    have e2 : (k : ℝ≥0) * h + u' = s' := by rw [hu']; exact add_tsub_cancel_of_le hks'
    have hdiff : Z ω s' - Z ω s =
        SRW.theta ((k : ℝ≥0) * h) (Z ω) u' - SRW.theta ((k : ℝ≥0) * h) (Z ω) u := by
      unfold SRW.theta; rw [e1, e2]; abel
    have hle : a ≤ ‖SRW.theta ((k : ℝ≥0) * h) (Z ω) u'‖ +
        ‖SRW.theta ((k : ℝ≥0) * h) (Z ω) u‖ := by
      calc a ≤ _ := hn
        _ = ‖SRW.theta ((k : ℝ≥0) * h) (Z ω) u' - SRW.theta ((k : ℝ≥0) * h) (Z ω) u‖ := by
          rw [hdiff]
        _ ≤ _ := norm_sub_le _ _
    by_cases hc : a / 2 ≤ ‖SRW.theta ((k : ℝ≥0) * h) (Z ω) u'‖
    · exact ⟨u', hu2', hc⟩
    · exact ⟨u, hu2, by linarith [not_le.1 hc]⟩
  have hcard : ((Finset.range (K + 1)).card : ℝ) ≤ (T : ℝ) / h + 1 := by
    rw [Finset.card_range]
    push_cast
    have := Nat.floor_le (show 0 ≤ (T : ℝ) / h by positivity)
    linarith
  have hA : ∀ k : ℕ, P.real (A k) ≤ 4 * d * Real.exp (-min (a ^ 2 / (64 * h)) (a / 4)) := by
    intro k
    have h2h : (0 : ℝ≥0) < 2 * h := by positivity
    have := (hZ.theta ((k : ℝ≥0) * h)).maximal h2h (a := a / 2) (by positivity)
    refine this.trans (le_of_eq ?_)
    congr 2
    push_cast
    have e : (a / 2) ^ 2 / (8 * (2 * (h : ℝ))) = a ^ 2 / (64 * h) := by
      field_simp; ring
    have e' : a / 2 / 2 = a / 4 := by ring
    rw [e, e']
  calc P.real _ ≤ P.real (⋃ k ∈ Finset.range (K + 1), A k) :=
        measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ ∑ k ∈ Finset.range (K + 1), P.real (A k) := measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _k ∈ Finset.range (K + 1), 4 * d * Real.exp (-min (a ^ 2 / (64 * h)) (a / 4)) :=
        Finset.sum_le_sum fun k _ => hA k
    _ = (Finset.range (K + 1)).card * (4 * d * Real.exp (-min (a ^ 2 / (64 * h)) (a / 4))) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((T : ℝ) / h + 1) * (4 * d * Real.exp (-min (a ^ 2 / (64 * h)) (a / 4))) := by
        gcongr

end SRW
end ElboimSly
