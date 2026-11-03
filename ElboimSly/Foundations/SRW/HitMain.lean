/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.SRW.HitSum
public import ElboimSly.Foundations.SRW.Maximal
public import ElboimSly.Foundations.SRW.HittingTime
public import ElboimSly.Foundations.SRW.StrongMarkovMain
public import ElboimSly.Foundations.SRW.AdmissibleSRW
public import ElboimSly.Foundations.SRW.Modulus
public import ElboimSly.Foundations.SRW.WindowExit
public import ElboimSly.Foundations.SRW.EscapeSets
public import Mathlib

/-!
# Hitting a ball after a given time

Hitting a box after a given time.  This file: the stopping-time part (strong Markov and the maximal
inequality).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Real

namespace ElboimSly
namespace SRW

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {Z : Ω → PathSpace d}

/-- `κ_d = 8 ln (8 d)`. -/
noncomputable def kappa (d : ℕ) : ℝ := 8 * Real.log (8 * d)

/-- The hitting constant `C_hit(d) = 12 (5 κ_d)^d π^{-d/2}`. -/
noncomputable def Chit (d : ℕ) : ℝ := 12 * (5 * kappa d) ^ d * π ^ (-(d : ℝ) / 2)

theorem kappa_ge {d : ℕ} (hd : 1 ≤ d) : 8 ≤ kappa d := by
  unfold kappa
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have h1 : (1 : ℝ) ≤ Real.log (8 * d) := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    have := Real.exp_one_lt_d9
    nlinarith
  linarith

theorem four_d_exp_le {d : ℕ} (hd : 1 ≤ d) : 4 * (d : ℝ) * Real.exp (-(kappa d / 2)) ≤ 1 / 2 := by
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have e : Real.exp (-(kappa d / 2)) = ((8 * (d : ℝ)) ^ 4)⁻¹ := by
    unfold kappa
    have : -(8 * Real.log (8 * d) / 2) = -((4 : ℕ) * Real.log (8 * d)) := by push_cast; ring
    rw [this, Real.exp_neg, Real.exp_nat_mul, Real.exp_log (by positivity)]
  rw [e]
  rw [← div_eq_mul_inv]
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  have h4 : (d : ℝ) ≤ (d : ℝ) ^ 4 := le_self_pow₀ hd' (by norm_num)
  rw [mul_pow]
  nlinarith

omit [MeasurableSpace Ω] in
theorem isRegularPath_thetaAt (hreg : ∀ ω, IsRegularPath (Z ω)) (T : Ω → WithTop ℝ≥0) (ω : Ω) :
    IsRegularPath (thetaAt T Z ω) := by
  unfold thetaAt
  split_ifs
  · intro t; exact ⟨1, one_pos, fun s _ _ => rfl⟩
  · exact (hreg ω).theta _

theorem measurableSet_ballVisit (hZ : IsSRW P Z) (c : Fin d → ℤ) (R : ℝ) (K₀ k : ℕ) :
    MeasurableSet (ballVisit Z c R K₀ k) := by
  by_cases h : K₀ ≤ k
  · have : ballVisit Z c R K₀ k =
        (fun ω => Z ω (k : ℝ≥0)) ⁻¹' {z | ‖fun i => ((z i - c i : ℤ) : ℝ)‖ < R} := by
      ext ω; simp [ballVisit, h]
    rw [this]
    exact ((measurable_pi_apply (k : ℝ≥0)).comp hZ.1) (MeasurableSet.of_discrete)
  · have : ballVisit Z c R K₀ k = ∅ := by ext ω; simp [ballVisit, h]
    rw [this]; exact MeasurableSet.empty

/-- The set of paths staying within `ρ₁` of the origin up to time `h`. -/
def stayBall (ρ₁ : ℝ) (h : ℝ≥0) : Set (PathSpace d) :=
  evalForall Set.univ {z : Fin d → ℤ | ‖fun i => ((z i : ℤ) : ℝ)‖ < ρ₁} h

/-- The strong Markov step of hitting a box after a given time. -/
theorem hit_markov (hZ : IsSRW P Z) (ρ₁ : ℝ) (h : ℝ≥0) (a : ℝ≥0) (K : Set (Fin d → ℤ))
    (hmax : 1 / 2 ≤ P.real {ω | Z ω ∈ stayBall ρ₁ h}) :
    1 / 2 * P.real {ω | hitTime Z a K ω < ⊤} ≤
      P.real {ω | hitTime Z a K ω < ⊤ ∧ thetaAt (hitTime Z a K) Z ω ∈ stayBall ρ₁ h} := by
  have := hZ.isProbabilityMeasure
  have hF := hZ.isAdmissible_natFil
  have hτ : IsStoppingTime hF.filtration (hitTime Z a K) :=
    isStoppingTime_hitTime hF.adapted hZ.2.1 a K
  obtain ⟨V, hVm, hV⟩ := isRegSet_evalForall (d := d) Set.univ
    {z : Fin d → ℤ | ‖fun i => ((z i : ℤ) : ℝ)‖ < ρ₁} h
  have hsm := hZ.strong_markov hF hτ (A := Set.univ) (@MeasurableSet.univ _ hτ.measurableSpace) hVm
  have e1 : (Set.univ ∩ {ω | hitTime Z a K ω < ⊤} ∩ {ω | thetaAt (hitTime Z a K) Z ω ∈ V}) =
      {ω | hitTime Z a K ω < ⊤ ∧ thetaAt (hitTime Z a K) Z ω ∈ stayBall ρ₁ h} := by
    ext ω
    simp only [mem_inter_iff, mem_univ, true_and, mem_ofPred_eq]
    rw [and_congr_right_iff]
    intro _
    exact (hV _ (isRegularPath_thetaAt hZ.2.1 _ ω)).symm
  have e2 : (Set.univ ∩ {ω | hitTime Z a K ω < ⊤}) = {ω | hitTime Z a K ω < ⊤} := by
    ext ω; simp
  have e3 : P.map Z V = P {ω | Z ω ∈ stayBall ρ₁ h} := by
    rw [Measure.map_apply hZ.1 hVm]
    congr 1
    ext ω
    exact (hV _ (hZ.2.1 ω)).symm
  rw [e1, e2, e3] at hsm
  have : P.real {ω | hitTime Z a K ω < ⊤ ∧ thetaAt (hitTime Z a K) Z ω ∈ stayBall ρ₁ h} =
      P.real {ω | hitTime Z a K ω < ⊤} * P.real {ω | Z ω ∈ stayBall ρ₁ h} := by
    simp only [measureReal_def]
    rw [hsm, ENNReal.toReal_mul]
  rw [this]
  have hnn : 0 ≤ P.real {ω | hitTime Z a K ω < ⊤} := measureReal_nonneg
  nlinarith

omit [MeasurableSpace Ω] in
theorem hitTime_facts {γ : Ω → PathSpace d} (hreg : ∀ ω, IsRegularPath (γ ω)) {a : ℝ≥0}
    {K : Set (Fin d → ℤ)} {ω : Ω} (h : hitTime γ a K ω < ⊤) :
    ∃ t₀ : ℝ≥0, hitTime γ a K ω = (t₀ : WithTop ℝ≥0) ∧ a ≤ t₀ ∧ γ ω t₀ ∈ K := by
  unfold hitTime at h ⊢
  by_cases hex : ∃ s, a ≤ s ∧ γ ω s ∈ K
  · rw [ite_eq_left hex] at h ⊢
    obtain ⟨h1, h2⟩ := hitTime_attained (hreg ω) hex
    exact ⟨_, rfl, h1, h2⟩
  · rw [ite_eq_right hex] at h
    exact absurd h (lt_irrefl _)

omit [MeasurableSpace Ω] in
theorem mem_ballVisit_of_G {ω : Ω} (_hreg : IsRegularPath (Z ω)) {x y : Fin d → ℤ} {ρ₁ : ℝ}
    {h a t₀ : ℝ≥0} (hat : a ≤ t₀)
    (hK : ‖fun i => ((x i + Z ω t₀ i - y i : ℤ) : ℝ)‖ ≤ ρ₁)
    (hΓ : ∀ u : ℝ≥0, u ≤ h → ‖fun i => ((Z ω (t₀ + u) i : ℤ) - Z ω t₀ i : ℝ)‖ < ρ₁) {k : ℕ}
    (hk1 : t₀ ≤ k) (hk2 : (k : ℝ≥0) ≤ t₀ + h) :
    ω ∈ ballVisit Z (y - x) (2 * ρ₁) ⌈a⌉₊ k := by
  refine ⟨Nat.ceil_le.2 (hat.trans hk1), ?_⟩
  have hu : t₀ + ((k : ℝ≥0) - t₀) = k := add_tsub_cancel_of_le hk1
  have hu2 : (k : ℝ≥0) - t₀ ≤ h := by rw [tsub_le_iff_left]; exact hk2
  have h2 := hΓ _ hu2
  rw [hu] at h2
  have e : (fun i => ((Z ω (k : ℝ≥0) i - (y - x) i : ℤ) : ℝ)) =
      (fun i => ((x i + Z ω t₀ i - y i : ℤ) : ℝ)) +
        (fun i => ((Z ω (k : ℝ≥0) i : ℤ) - Z ω t₀ i : ℝ)) := by
    funext i; simp only [Pi.add_apply, Pi.sub_apply]; push_cast; ring
  rw [e]
  calc _ ≤ ‖fun i => ((x i + Z ω t₀ i - y i : ℤ) : ℝ)‖ +
        ‖fun i => ((Z ω (k : ℝ≥0) i : ℤ) - Z ω t₀ i : ℝ)‖ := norm_add_le _ _
    _ < 2 * ρ₁ := by linarith

theorem measurableSet_G (hZ : IsSRW P Z) (ρ₁ : ℝ) (h a : ℝ≥0) (K : Set (Fin d → ℤ)) :
    MeasurableSet {ω | hitTime Z a K ω < ⊤ ∧ thetaAt (hitTime Z a K) Z ω ∈ stayBall ρ₁ h} := by
  have hF := hZ.isAdmissible_natFil
  have hτ : IsStoppingTime hF.filtration (hitTime Z a K) :=
    isStoppingTime_hitTime hF.adapted hZ.2.1 a K
  obtain ⟨V, hVm, hV⟩ := isRegSet_evalForall (d := d) Set.univ
    {z : Fin d → ℤ | ‖fun i => ((z i : ℤ) : ℝ)‖ < ρ₁} h
  have hth : Measurable (thetaAt (hitTime Z a K) Z) :=
    measurable_thetaAt hτ (fun s => (measurable_pi_apply s).comp hZ.1) hZ.2.1
  have e : {ω | hitTime Z a K ω < ⊤ ∧ thetaAt (hitTime Z a K) Z ω ∈ stayBall ρ₁ h} =
      {ω | hitTime Z a K ω < ⊤} ∩ (thetaAt (hitTime Z a K) Z) ⁻¹' V := by
    ext ω
    simp only [mem_ofPred_eq, mem_inter_iff, mem_preimage]
    rw [and_congr_right_iff]
    intro _
    exact hV _ (isRegularPath_thetaAt hZ.2.1 _ ω)
  rw [e]
  refine MeasurableSet.inter ?_ (hth hVm)
  have : {ω | hitTime Z a K ω < ⊤} = {ω | hitTime Z a K ω = ⊤}ᶜ := by
    ext ω; simp [lt_top_iff_ne_top]
  rw [this]; exact hτ.measurableSet_top.compl

/-- Counting: `⌊h⌋ · P(G) ≤ ∑_k P(ballVisit k)`. -/
theorem hit_count (hZ : IsSRW P Z) (x y : Fin d → ℤ) {ρ₁ : ℝ} (h a : ℝ≥0) :
    (⌊h⌋₊ : ℝ≥0∞) *
      P {ω | hitTime Z a {z : Fin d → ℤ | ‖fun i => ((x i + z i - y i : ℤ) : ℝ)‖ ≤ ρ₁} ω < ⊤ ∧
        thetaAt (hitTime Z a {z : Fin d → ℤ | ‖fun i => ((x i + z i - y i : ℤ) : ℝ)‖ ≤ ρ₁}) Z ω ∈
          stayBall ρ₁ h} ≤
      ∑' k : ℕ, P (ballVisit Z (y - x) (2 * ρ₁) ⌈a⌉₊ k) := by
  set K : Set (Fin d → ℤ) := {z : Fin d → ℤ | ‖fun i => ((x i + z i - y i : ℤ) : ℝ)‖ ≤ ρ₁}
    with hK
  set G := {ω | hitTime Z a K ω < ⊤ ∧ thetaAt (hitTime Z a K) Z ω ∈ stayBall ρ₁ h} with hG
  have hGm : MeasurableSet G := measurableSet_G hZ ρ₁ h a K
  have hvm : ∀ k, MeasurableSet (ballVisit Z (y - x) (2 * ρ₁) ⌈a⌉₊ k) := fun k =>
    measurableSet_ballVisit hZ _ _ _ _
  calc (⌊h⌋₊ : ℝ≥0∞) * P G = ∫⁻ ω, G.indicator (fun _ => (⌊h⌋₊ : ℝ≥0∞)) ω ∂P := by
        rw [lintegral_indicator_const hGm, mul_comm]
    _ ≤ ∫⁻ ω, ∑' k : ℕ, (ballVisit Z (y - x) (2 * ρ₁) ⌈a⌉₊ k).indicator (fun _ => (1 : ℝ≥0∞)) ω ∂P := by
        refine lintegral_mono fun ω => ?_
        by_cases hω : ω ∈ G
        · rw [Set.indicator_of_mem hω]
          obtain ⟨hlt, hth⟩ := hω
          obtain ⟨t₀, ht₀, hat, hKt⟩ := hitTime_facts hZ.2.1 hlt
          have hsr : stopReal (hitTime Z a K) ω = t₀ := by
            unfold stopReal; rw [ht₀]; rfl
          have hth' : thetaAt (hitTime Z a K) Z ω = theta t₀ (Z ω) := by
            unfold thetaAt; rw [ite_eq_right (by rw [ht₀]; exact WithTop.coe_ne_top), hsr]
          rw [hth'] at hth
          obtain ⟨-, hth2⟩ := hth
          have hΓ : ∀ u : ℝ≥0, u ≤ h → ‖fun i => ((Z ω (t₀ + u) i : ℤ) - Z ω t₀ i : ℝ)‖ < ρ₁ := by
            intro u hu
            have := hth2 u hu
            simp only [mem_ofPred_eq, theta] at this
            simpa using this
          have hI : ∀ k ∈ Finset.Ico ⌈t₀⌉₊ (⌈t₀⌉₊ + ⌊h⌋₊),
              ω ∈ ballVisit Z (y - x) (2 * ρ₁) ⌈a⌉₊ k := by
            intro k hk
            rw [Finset.mem_Ico] at hk
            have hk1 : t₀ ≤ (k : ℝ≥0) := (Nat.le_ceil t₀).trans (by exact_mod_cast hk.1)
            have hk2 : (k : ℝ≥0) ≤ t₀ + h := by
              rw [← NNReal.coe_le_coe]
              push_cast
              have h1 : (⌈t₀⌉₊ : ℝ) < t₀ + 1 := Nat.ceil_lt_add_one t₀.2
              have h2 : (⌊h⌋₊ : ℝ) ≤ h := Nat.floor_le h.2
              have h3 : (k : ℝ) + 1 ≤ ⌈t₀⌉₊ + ⌊h⌋₊ := by exact_mod_cast hk.2
              linarith
            exact mem_ballVisit_of_G (hZ.2.1 ω) hat hKt hΓ hk1 hk2
          have hcard : (⌊h⌋₊ : ℝ≥0∞) = ∑ k ∈ Finset.Ico ⌈t₀⌉₊ (⌈t₀⌉₊ + ⌊h⌋₊),
              (ballVisit Z (y - x) (2 * ρ₁) ⌈a⌉₊ k).indicator (fun _ => (1 : ℝ≥0∞)) ω := by
            rw [Finset.sum_congr rfl (fun k hk => Set.indicator_of_mem (hI k hk) _)]
            simp
          rw [hcard]
          exact ENNReal.sum_le_tsum _
        · rw [Set.indicator_of_notMem hω]; exact bot_le
    _ = ∑' k : ℕ, P (ballVisit Z (y - x) (2 * ρ₁) ⌈a⌉₊ k) := by
        rw [lintegral_tsum fun k => (measurable_const.indicator (hvm k)).aemeasurable]
        refine tsum_congr fun k => ?_
        rw [lintegral_indicator_const (hvm k), one_mul]

end SRW
end ElboimSly
