/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.SRW.TransienceLine
public import ElboimSly.Foundations.SRW.Freeze
public import ElboimSly.Foundations.SRW.EscapeParams
public import Mathlib

/-!
# Transience: escape from the unit box

Transience: escape from the unit box.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Real

namespace ElboimSly
namespace SRW

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {Z : Ω → PathSpace d}

theorem IsSRW.prob_gamLine (hZ : IsSRW P Z) (v₀ : Dir d) (R : ℕ) :
    Real.exp (-(2 * d)) / R.factorial ≤ P.real {ω | Z ω ∈ gamLine v₀ R} := by
  obtain ⟨Ω', mΩ', P', N, hP, hN, -⟩ := exists_isPoissonPointProcess_clockIntensity (Dir d)
  have hZ' := canonical_isSRW hN
  have h := hZ.prob_regSet_eq hZ' (isRegSet_evalForall (d := d) _ _ 1 :
    IsRegSet (gamLine v₀ R))
  have := prob_gamLine_canonical hN v₀ R
  simp only [measureReal_def]
  have e : P {ω | Z ω ∈ gamLine v₀ R} = P' {ω | canonical d N ω ∈ gamLine v₀ R} := h
  rw [e]
  exact this

/-- Positions along a line path starting at `x` with `|x_i| ≥ 2` stay at norm `≥ 2`. -/
theorem line_norm_ge {x : Fin d → ℤ} {i : Fin d} (hxi : 2 ≤ |x i|) {b : Bool}
    (hb : (b = true ∧ 0 ≤ x i) ∨ (b = false ∧ x i < 0)) {k : ℕ} :
    2 ≤ ‖fun l => ((x l + ((k : ℤ) • (Dir.vec ((i, b) : Dir d))) l : ℤ) : ℝ)‖ := by
  have h1 : ‖((x i + ((k : ℤ) • (Dir.vec ((i, b) : Dir d))) i : ℤ) : ℝ)‖ ≤
      ‖fun l => ((x l + ((k : ℤ) • (Dir.vec ((i, b) : Dir d))) l : ℤ) : ℝ)‖ :=
    norm_le_pi_norm (fun l => ((x l + ((k : ℤ) • (Dir.vec ((i, b) : Dir d))) l : ℤ) : ℝ)) i
  refine le_trans ?_ h1
  rw [Real.norm_eq_abs]
  have hv : (Dir.vec ((i, b) : Dir d)) i = if b then 1 else -1 := by simp [Dir.vec]
  simp only [Pi.smul_apply, hv, smul_eq_mul]
  rcases hb with ⟨rfl, h0⟩ | ⟨rfl, h0⟩
  · have : (2 : ℤ) ≤ x i := by rw [abs_of_nonneg h0] at hxi; exact hxi
    have h3 : (2 : ℝ) ≤ ((x i + (k : ℤ) * 1 : ℤ) : ℝ) := by
      have : (2 : ℤ) ≤ x i + (k : ℤ) * 1 := by simp; omega
      exact_mod_cast this
    simp only [ite_true]
    exact h3.trans (le_abs_self _)
  · have : x i ≤ -2 := by rw [abs_of_neg h0] at hxi; omega
    have h3 : ((x i + (k : ℤ) * (-1) : ℤ) : ℝ) ≤ -2 := by
      have : x i + (k : ℤ) * (-1) ≤ -2 := by omega
      exact_mod_cast this
    simp only [Bool.false_eq_true, ite_false]
    have := neg_abs_le ((x i + (k : ℤ) * (-1) : ℤ) : ℝ)
    linarith

theorem line_norm_ge_k {x : Fin d → ℤ} {i : Fin d} {b : Bool}
    (hb : (b = true ∧ 0 ≤ x i) ∨ (b = false ∧ x i < 0)) {k : ℕ} :
    (k : ℝ) ≤ ‖fun l => ((x l + ((k : ℤ) • (Dir.vec ((i, b) : Dir d))) l : ℤ) : ℝ)‖ := by
  have h1 : ‖((x i + ((k : ℤ) • (Dir.vec ((i, b) : Dir d))) i : ℤ) : ℝ)‖ ≤
      ‖fun l => ((x l + ((k : ℤ) • (Dir.vec ((i, b) : Dir d))) l : ℤ) : ℝ)‖ :=
    norm_le_pi_norm (fun l => ((x l + ((k : ℤ) • (Dir.vec ((i, b) : Dir d))) l : ℤ) : ℝ)) i
  refine le_trans ?_ h1
  rw [Real.norm_eq_abs]
  have hv : (Dir.vec ((i, b) : Dir d)) i = if b then 1 else -1 := by simp [Dir.vec]
  simp only [Pi.smul_apply, hv, smul_eq_mul]
  rcases hb with ⟨rfl, h0⟩ | ⟨rfl, h0⟩
  · have h3 : (k : ℝ) ≤ ((x i + (k : ℤ) * 1 : ℤ) : ℝ) := by
      have : (k : ℤ) ≤ x i + (k : ℤ) * 1 := by simp; omega
      exact_mod_cast this
    simp only [ite_true]
    exact h3.trans (le_abs_self _)
  · have h3 : ((x i + (k : ℤ) * (-1) : ℤ) : ℝ) ≤ -(k : ℝ) := by
      have : x i + (k : ℤ) * (-1) ≤ -(k : ℤ) := by omega
      exact_mod_cast this
    simp only [Bool.false_eq_true, ite_false]
    have := neg_abs_le ((x i + (k : ℤ) * (-1) : ℤ) : ℝ)
    linarith

/-- The bad parameter set of Claim `escape`. -/
theorem exists_version_bad :
    ∃ V : Set ((Fin d → ℤ) × PathSpace d), MeasurableSet V ∧ ∀ z γ, IsRegularPath γ →
      ((∃ s : ℝ≥0, ‖fun i => ((z i + γ s i : ℤ) : ℝ)‖ < 2) ↔ (z, γ) ∈ V) := by
  have h := isVersion_exists_Ici (E := Fin d → ℤ) (d := d) (α := fun _ => 0)
    (K := {p : (Fin d → ℤ) × (Fin d → ℤ) | ‖fun i => ((p.1 i + p.2 i : ℤ) : ℝ)‖ < 2})
    measurable_const MeasurableSet.of_discrete
  refine ⟨_, h.1, fun z γ hγ => ?_⟩
  rw [← h.2 z γ hγ]
  simp only [mem_ofPred_eq]
  exact ⟨fun ⟨s, hs⟩ => ⟨s, bot_le, hs⟩, fun ⟨s, _, hs⟩ => ⟨s, hs⟩⟩

/-- Transience: escape from the unit box: transience. -/
theorem escape_unit (hZ : IsSRW P Z) (hd : 3 ≤ d) {x : Fin d → ℤ} (hx : 2 ≤ ‖x‖) :
    Real.exp (-(2 * d)) / (2 * (escR d).factorial) ≤
      P.real {ω | ∀ s : ℝ≥0, 2 ≤ ‖fun i => ((x i + Z ω s i : ℤ) : ℝ)‖} := by
  classical
  have := hZ.isProbabilityMeasure
  obtain ⟨hR2, -⟩ := escR_spec hd
  set R := escR d with hRdef
  have hF := hZ.isAdmissible_natFil
  have hd0 : 0 < d := by omega
  -- a maximal coordinate
  obtain ⟨i, -, hi⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin d)) (fun j => ‖x j‖)
    ⟨⟨0, hd0⟩, Finset.mem_univ _⟩
  have hxi : ‖x‖ = ‖x i‖ := by
    apply le_antisymm
    · exact (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun j => hi j (Finset.mem_univ _)
    · exact norm_le_pi_norm x i
  have hxi2 : (2 : ℤ) ≤ |x i| := by
    have h1 : (2 : ℝ) ≤ ‖x i‖ := hxi ▸ hx
    rw [Int.norm_eq_abs] at h1
    have : ((2 : ℤ) : ℝ) ≤ ((|x i| : ℤ) : ℝ) := by rw [Int.cast_abs]; exact_mod_cast h1
    exact_mod_cast this
  set b : Bool := decide (0 ≤ x i) with hb
  have hbb : (b = true ∧ 0 ≤ x i) ∨ (b = false ∧ x i < 0) := by
    by_cases h : 0 ≤ x i
    · left; simp [hb, h]
    · right; simp [hb, h]; omega
  set v₀ : Dir d := (i, b) with hv₀
  obtain ⟨V1, hV1m, hV1⟩ := (isRegSet_evalForall (d := d)
    {w : Fin d → ℤ | w = (R : ℤ) • v₀.vec}
    {w : Fin d → ℤ | ∃ k : ℕ, k ≤ R ∧ w = (k : ℤ) • v₀.vec} 1 : IsRegSet (gamLine v₀ R))
  obtain ⟨V, hVm, hV⟩ := exists_version_bad (d := d)
  set A' : Set Ω := {ω | Z ω ∈ gamLine v₀ R} with hA'
  have hT : IsStoppingTime hF.filtration (fun _ : Ω => ((1 : ℝ≥0) : WithTop ℝ≥0)) :=
    isStoppingTime_const _ _
  have hTs : hT.measurableSpace = natFil Z 1 := IsStoppingTime.measurableSpace_const _ _
  have hA'm : MeasurableSet[hT.measurableSpace] A' := by
    rw [hTs]
    have hmeas : Measurable[natFil Z 1] (fun ω => stopPath 1 (Z ω)) :=
      (@measurable_pi_iff Ω ℝ≥0 (fun _ => Fin d → ℤ) (natFil Z 1) _ _).2
        (fun s => hF.adapted (min s 1) 1 (min_le_right _ _))
    have e : A' = (fun ω => stopPath 1 (Z ω)) ⁻¹' V1 := by
      ext ω
      simp only [hA', mem_ofPred_eq, mem_preimage]
      have hreg : IsRegularPath (stopPath 1 (Z ω)) := (hZ.2.1 ω).stop 1
      rw [← hV1 _ hreg]
      exact (evalForall_stop _ _ 1 (Z ω)).symm
    rw [e]; exact hmeas hV1m
  have hξ : Measurable[hT.measurableSpace] (fun ω => x + Z ω 1) := by
    rw [hTs]
    exact (measurable_of_countable (fun y : Fin d → ℤ => x + y)).comp
      (hF.adapted 1 1 le_rfl)
  set C : Set (Fin d → ℤ) := {z | (R : ℝ) ≤ ‖z‖} with hC
  have hp : ∀ z ∈ C, P.map Z (Prod.mk z ⁻¹' V) ≤ ENNReal.ofReal (1 / 2) := by
    intro z hz
    rw [Measure.map_apply hZ.1 (measurable_prodMk_left hVm)]
    have hbad : Z ⁻¹' (Prod.mk z ⁻¹' V) = {ω | ∃ s : ℝ≥0, ‖fun i => ((z i + Z ω s i : ℤ) : ℝ)‖ < 2} := by
      ext ω; exact (hV z (Z ω) (hZ.2.1 ω)).symm
    have hbm : MeasurableSet (Z ⁻¹' (Prod.mk z ⁻¹' V)) := hZ.1 (measurable_prodMk_left hVm)
    have hfar := far_start hZ hd (z := z) hz
    have hgood : {ω | ∀ s : ℝ≥0, 2 ≤ ‖fun i => ((z i + Z ω s i : ℤ) : ℝ)‖} =
        (Z ⁻¹' (Prod.mk z ⁻¹' V))ᶜ := by
      rw [hbad]; ext ω; simp
    rw [hgood, measureReal_def, prob_compl_eq_one_sub hbm] at hfar
    have : P (Z ⁻¹' (Prod.mk z ⁻¹' V)) ≤ ENNReal.ofReal (1 / 2) := by
      have h1 : (P (Z ⁻¹' (Prod.mk z ⁻¹' V))).toReal ≤ 1 / 2 := by
        have := ENNReal.toReal_mono ENNReal.one_ne_top (prob_le_one (μ := P) (s := Z ⁻¹' (Prod.mk z ⁻¹' V)))
        rw [ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top] at hfar
        simp at hfar
        linarith
      exact (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) (by norm_num)).2 h1
    exact this
  have hCm : MeasurableSet C := MeasurableSet.of_discrete
  have hfr := hZ.freeze_param_le hF hT hξ hA'm hVm hCm hp
  -- simplify the freeze inequality
  have hTlt : {ω : Ω | ((1 : ℝ≥0) : WithTop ℝ≥0) < ⊤} = Set.univ := by
    ext ω; simp
  have hA'C : A' ⊆ {ω | (fun ω => x + Z ω 1) ω ∈ C} := by
    intro ω hω
    obtain ⟨h1, -⟩ := hω
    have h1' : Z ω 1 = (R : ℤ) • v₀.vec := h1
    show (R : ℝ) ≤ ‖x + Z ω 1‖
    rw [← norm_cast_vec, h1']
    exact line_norm_ge_k hbb
  have hbad'm : MeasurableSet {ω | ((fun ω => x + Z ω 1) ω, thetaAt (fun _ : Ω => ((1 : ℝ≥0) : WithTop ℝ≥0)) Z ω) ∈ V} := by
    have hξm : Measurable (fun ω => x + Z ω 1) :=
      (measurable_of_countable (fun y : Fin d → ℤ => x + y)).comp
        ((measurable_pi_apply (1 : ℝ≥0)).comp hZ.1)
    have hth : Measurable (thetaAt (fun _ : Ω => ((1 : ℝ≥0) : WithTop ℝ≥0)) Z) :=
      measurable_thetaAt hT (fun s => (measurable_pi_apply s).comp hZ.1) hZ.2.1
    exact (hξm.prodMk hth) hVm
  have hA'meas : MeasurableSet A' := hT.measurableSpace_le A' hA'm
  rw [hTlt] at hfr
  simp only [Set.inter_univ] at hfr
  have e1 : A' ∩ {ω | (fun ω => x + Z ω 1) ω ∈ C} = A' := inter_eq_left.2 hA'C
  rw [e1] at hfr
  set bad' : Set Ω := {ω | ((fun ω => x + Z ω 1) ω,
    thetaAt (fun _ : Ω => ((1 : ℝ≥0) : WithTop ℝ≥0)) Z ω) ∈ V} with hbad'
  have hdec := measure_inter_add_sdiff (μ := P) A' hbad'm
  have hr : (P (A' ∩ bad')).toReal ≤ 1 / 2 * (P A').toReal := by
    have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)) hfr
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by norm_num)] at this
    exact this
  have hsum : (P (A' ∩ bad')).toReal + (P (A' \ bad')).toReal = (P A').toReal := by
    rw [← ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _), hdec]
  have hsubT : A' \ bad' ⊆ {ω | ∀ s : ℝ≥0, 2 ≤ ‖fun i => ((x i + Z ω s i : ℤ) : ℝ)‖} := by
    intro ω ⟨hA, hnb⟩ s
    obtain ⟨h1, h2⟩ := hA
    have hnb' : ¬ (∃ u : ℝ≥0, ‖fun l => ((x l + Z ω 1 l + theta 1 (Z ω) u l : ℤ) : ℝ)‖ < 2) := by
      intro hex
      apply hnb
      have hreg : IsRegularPath (thetaAt (fun _ : Ω => ((1 : ℝ≥0) : WithTop ℝ≥0)) Z ω) :=
        isRegularPath_thetaAt hZ.2.1 _ ω
      have hth : thetaAt (fun _ : Ω => ((1 : ℝ≥0) : WithTop ℝ≥0)) Z ω = theta 1 (Z ω) := by
        simp [thetaAt, stopReal]
      show (x + Z ω 1, thetaAt (fun _ : Ω => ((1 : ℝ≥0) : WithTop ℝ≥0)) Z ω) ∈ V
      rw [← hV _ _ hreg, hth]
      exact hex
    rcases le_or_gt s 1 with hs | hs
    · obtain ⟨k, -, hk⟩ := h2 s hs
      rw [hk]
      exact line_norm_ge hxi2 hbb
    · by_contra hcon
      apply hnb'
      refine ⟨s - 1, ?_⟩
      have e : ∀ l, x l + Z ω 1 l + theta 1 (Z ω) (s - 1) l = x l + Z ω s l := by
        intro l
        simp only [theta]
        rw [add_tsub_cancel_of_le hs.le]
        simp
      simp only [e]
      exact not_le.1 hcon
  have hA'low := hZ.prob_gamLine v₀ R
  have hsm : (P (A' \ bad')).toReal ≤
      P.real {ω | ∀ s : ℝ≥0, 2 ≤ ‖fun i => ((x i + Z ω s i : ℤ) : ℝ)‖} :=
    ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsubT)
  have hfac : (0 : ℝ) < (R.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos R
  have e2 : Real.exp (-(2 * d)) / (2 * R.factorial) =
      1 / 2 * (Real.exp (-(2 * d)) / R.factorial) := by
    field_simp
  rw [e2]
  have hPA : (P A').toReal = P.real A' := rfl
  linarith

end SRW
end ElboimSly
