/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.SRW.Lemma82B
public import Mathlib

/-!
# Lemma 8.2 (b), model-law form

SRW content of Lemma 8.2 (b).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal Real

namespace ElboimSly
namespace SRW

variable {d : ℕ}

/-- Transfer of a regular exceedance event from `Y_v` to the model SRW. -/
theorem transfer_exceed_model {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (Tn : ℝ≥0) (Yv : Ω → PathSpace d) (v : Fin d → ℤ)
    (hm : Measurable fun ω s => Yv ω (min s Tn) - v)
    (hr : ∀ ω, IsRegularPath fun s => Yv ω (min s Tn) - v)
    (hlaw : P.map (fun ω s => Yv ω (min s Tn) - v) =
      (srwP d).map (fun ω s => srwZ d ω (min s Tn))) (a : ℝ) :
    P {ω | ∃ s : ℝ≥0, s ≤ Tn ∧ a ≤ ‖Yv ω s - v‖} =
      srwP d {ω | ∃ s : ℝ≥0, s ≤ Tn ∧ a ≤ ‖srwZ d ω s‖} := by
  obtain ⟨V, hVm, hV⟩ := isRegSet_exists_le (d := d) {z : Fin d → ℤ | a ≤ ‖z‖} Tn
  have hXs : ∀ ω, IsRegularPath fun s => srwZ d ω (min s Tn) :=
    fun ω => ((srwZ_isSRW d).2.1 ω).stop Tn
  have hXm : Measurable fun ω s => srwZ d ω (min s Tn) :=
    measurable_pi_iff.2 fun s => (measurable_pi_apply (min s Tn)).comp (srwZ_isSRW d).1
  have e1 : {ω | ∃ s : ℝ≥0, s ≤ Tn ∧ a ≤ ‖Yv ω s - v‖} =
      (fun ω s => Yv ω (min s Tn) - v) ⁻¹' V := by
    ext ω
    simp only [mem_ofPred_eq, mem_preimage]
    rw [← hV _ (hr ω)]
    constructor
    · rintro ⟨s, hs, h⟩; exact ⟨s, hs, by simpa [min_eq_left hs] using h⟩
    · rintro ⟨s, hs, h⟩; exact ⟨s, hs, by simpa [min_eq_left hs] using h⟩
  have e2 : {ω | ∃ s : ℝ≥0, s ≤ Tn ∧ a ≤ ‖srwZ d ω s‖} =
      (fun ω s => srwZ d ω (min s Tn)) ⁻¹' V := by
    ext ω
    simp only [mem_ofPred_eq, mem_preimage]
    rw [← hV _ (hXs ω)]
    constructor
    · rintro ⟨s, hs, h⟩; exact ⟨s, hs, by simpa [min_eq_left hs] using h⟩
    · rintro ⟨s, hs, h⟩; exact ⟨s, hs, by simpa [min_eq_left hs] using h⟩
  rw [e1, e2, ← Measure.map_apply hm hVm, ← Measure.map_apply hXm hVm, hlaw]

/-- SRW content of Lemma 8.2 (b), stated against the model SRW law (no `IsSRW` on the
ambient space is needed). -/
theorem lemma82_b_model {d : ℕ} [NeZero d] {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {n : ℕ} (hn : 4 ≤ n) {t₀ : ℝ} (ht1 : 1 < t₀) (ht4 : t₀ ≤ 4)
    (Y : (Fin d → ℤ) → Ω → PathSpace d)
    (hYm : ∀ v, Measurable fun ω s => Y v ω (min s (lem82T n t₀).toNNReal) - v)
    (hYr : ∀ v ω, IsRegularPath fun s => Y v ω (min s (lem82T n t₀).toNNReal) - v)
    (hlaw : ∀ v, P.map (fun ω s => Y v ω (min s (lem82T n t₀).toNNReal) - v) =
      (srwP d).map (fun ω s => srwZ d ω (min s (lem82T n t₀).toNNReal))) :
    P {ω | ¬ ∀ v : Fin d → ℤ, (4 : ℝ) ^ n ≤ ‖v‖ → ∀ s₁ s₂ : ℝ≥0,
        s₁ ≤ (lem82T n t₀).toNNReal → s₂ ≤ (lem82T n t₀).toNNReal →
          (1.9 : ℝ) ^ n < ‖Y v ω s₂ - Y 0 ω s₁‖} ≤
      ENNReal.ofReal (4 * d * (1 + latConst (1 / 6) d) * Real.exp (-((4 : ℝ) ^ n / 12))) := by
  classical
  have := (srwZ_isSRW d).isProbabilityMeasure
  set Tn : ℝ≥0 := (lem82T n t₀).toNNReal with hTn
  have hTpos := lem82T_pos hn ht1
  have hTc : (Tn : ℝ) = lem82T n t₀ := Real.coe_toNNReal _ hTpos.le
  have hTp : 0 < Tn := by
    have : (0 : ℝ) < Tn := by rw [hTc]; exact hTpos
    exact_mod_cast this
  have h4T : 4 * (Tn : ℝ) ≤ 4 ^ n / 8 := by rw [hTc]; exact four_lem82T_le hn ht4
  have hR : (0 : ℝ) < 4 ^ n := by positivity
  set R : ℝ := 4 ^ n with hRdef
  -- the bad events
  set B0 : Set Ω := {ω | ∃ s : ℝ≥0, s ≤ Tn ∧ R / 3 ≤ ‖Y 0 ω s - 0‖} with hB0
  set B : (Fin d → ℤ) → Set Ω := fun v =>
    if R ≤ ‖v‖ then {ω | ∃ s : ℝ≥0, s ≤ Tn ∧ ‖v‖ / 3 ≤ ‖Y v ω s - v‖} else ∅ with hB
  have hsub : {ω | ¬ ∀ v : Fin d → ℤ, R ≤ ‖v‖ → ∀ s₁ s₂ : ℝ≥0, s₁ ≤ Tn → s₂ ≤ Tn →
      (1.9 : ℝ) ^ n < ‖Y v ω s₂ - Y 0 ω s₁‖} ⊆ B0 ∪ ⋃ v, B v := by
    intro ω hω
    simp only [mem_ofPred_eq, not_forall, not_lt] at hω
    obtain ⟨v, hv, s₁, s₂, hs₁, hs₂, hcl⟩ := hω
    have hcl' : ‖fun i => ((Y v ω s₂ i - Y 0 ω s₁ i : ℤ) : ℝ)‖ ≤ 1.9 ^ n := by
      rw [norm_cast_vec]; exact hcl
    rcases lemma82_a_det (by omega) hv (Y 0 ω) (Y v ω) hs₁ hs₂ hcl' with ⟨s, hs, h⟩ | ⟨s, hs, h⟩
    · left
      refine ⟨s, hs, ?_⟩
      have : R / 3 ≤ ‖v‖ / 3 := by linarith
      simpa using this.trans h
    · right
      refine mem_iUnion.2 ⟨v, ?_⟩
      simp only [hB, ite_eq_left hv]
      exact ⟨s, hs, h⟩
  have hB0p : P B0 ≤ ENNReal.ofReal (4 * d * Real.exp (-(R / 6))) := by
    have := transfer_exceed_model Tn (Y 0) 0 (hYm 0) (hYr 0) (hlaw 0) (R / 3)
    have e : B0 = {ω | ∃ s : ℝ≥0, s ≤ Tn ∧ R / 3 ≤ ‖Y 0 ω s - 0‖} := rfl
    rw [e, this]
    have := (srwZ_isSRW d).maximal_exp hTp (a := R / 3) (by linarith)
    have e2 : -(R / 3 / 2) = -(R / 6) := by ring
    rw [e2] at this
    rw [← ofReal_measureReal]
    exact ENNReal.ofReal_le_ofReal this
  have hBp : ∀ v, P (B v) ≤ ENNReal.ofReal (if R ≤ ‖v‖ then 4 * d * Real.exp (-(‖v‖ / 6)) else 0) := by
    intro v
    by_cases hv : R ≤ ‖v‖
    · simp only [hB, ite_eq_left hv]
      rw [transfer_exceed_model Tn (Y v) v (hYm v) (hYr v) (hlaw v) (‖v‖ / 3)]
      have := (srwZ_isSRW d).maximal_exp hTp (a := ‖v‖ / 3) (by linarith)
      have e2 : -(‖v‖ / 3 / 2) = -(‖v‖ / 6) := by ring
      rw [e2] at this
      rw [← ofReal_measureReal]
      exact ENNReal.ofReal_le_ofReal this
    · simp [hB, hv]
  have hsum : ∑' v, P (B v) ≤ ENNReal.ofReal (4 * d * latConst (1 / 6) d * Real.exp (-(R / 12))) := by
    refine (ENNReal.tsum_le_tsum hBp).trans ?_
    have hsm := summable_lattice d (c := 1 / 6) (by norm_num) hR.le
    have hg : ∀ v : Fin d → ℤ, (if R ≤ ‖v‖ then 4 * (d : ℝ) * Real.exp (-(‖v‖ / 6)) else 0) =
        4 * d * (if R ≤ ‖v‖ then Real.exp (-(1 / 6) * ‖v‖) else 0) := by
      intro v; split_ifs
      · congr 2; ring
      · simp
    simp_rw [hg]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun v => by split_ifs <;> positivity)
      (hsm.mul_left _), tsum_mul_left]
    apply ENNReal.ofReal_le_ofReal
    have := lattice_sum d (c := 1 / 6) (by norm_num) hR.le
    have e : -(1 / 6 : ℝ) * R / 2 = -(R / 12) := by ring
    rw [e] at this
    calc 4 * (d : ℝ) * ∑' v : Fin d → ℤ, (if R ≤ ‖v‖ then Real.exp (-(1 / 6) * ‖v‖) else 0)
        ≤ 4 * d * (latConst (1 / 6) d * Real.exp (-(R / 12))) := by gcongr
      _ = _ := by ring
  have hfin : P (B0 ∪ ⋃ v, B v) ≤
      ENNReal.ofReal (4 * d * (1 + latConst (1 / 6) d) * Real.exp (-(R / 12))) := by
    refine (measure_union_le _ _).trans ?_
    refine (add_le_add hB0p ((measure_iUnion_le _).trans hsum)).trans ?_
    rw [← ENNReal.ofReal_add (by positivity) (by
      have : 0 ≤ latConst (1 / 6) d := latConst_nonneg (by norm_num) d
      positivity)]
    apply ENNReal.ofReal_le_ofReal
    have h6 : Real.exp (-(R / 6)) ≤ Real.exp (-(R / 12)) := Real.exp_le_exp.2 (by linarith)
    have hd0 : (0 : ℝ) ≤ 4 * d := by positivity
    nlinarith [mul_le_mul_of_nonneg_left h6 hd0]
  exact (measure_mono hsub).trans hfin

end SRW
end ElboimSly
