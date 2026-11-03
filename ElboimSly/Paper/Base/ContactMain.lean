/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Base.ContactProbC
public import ElboimSly.Foundations.SRW.Freeze
public import Mathlib

/-!
# Contacts are few: geometric decay

Contacts are few (ii): `P(κ_m < ∞) ≤ (1 - c₁)^{m-1}` (`kap m` is `κ_{m+1}`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Paper

open ElboimSly.Cyclic ElboimSly.Paper.Base ElboimSly.SRW

variable {d : ℕ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {Ñ : Ω → Measure ((Dir d × Fin 2) × ℝ)}

theorem es8CEsc_pos (d : ℕ) : 0 < es8CEsc d := by
  unfold es8CEsc; positivity

theorem es8C1_pos (d : ℕ) : 0 < es8C1 d := by
  unfold es8C1; exact mul_pos (Real.exp_pos _) (es8CEsc_pos d)

theorem es8C1_lt_one (d : ℕ) : es8C1 d < 1 := by
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have h1 : Real.exp (-(4 * (d : ℝ))) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have h2 : Real.exp (-(2 * (d : ℝ))) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have hf : (1 : ℝ) ≤ ((escR d).factorial : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero _)
  have hc : es8CEsc d ≤ 1 / 2 := by
    unfold es8CEsc
    rw [div_le_iff₀ (by positivity)]
    nlinarith [Real.exp_pos (-(2 * (d : ℝ)))]
  have := mul_le_mul h1 hc (es8CEsc_pos d).le zero_le_one
  unfold es8C1
  linarith

section

variable [NeZero d] (h : IsPoissonPointProcess Ñ (clockIntensity (Dir d × Fin 2)) P)
include h

omit [NeZero d] in
theorem measurableSet_kap_lt_top (a b : Fin d → ℤ) (m : ℕ) :
    MeasurableSet {ω | kap Ñ a b m ω < ⊤} := by
  have hT := kap_isStoppingTime h a b m
  have : {ω | kap Ñ a b m ω < ⊤} = {ω | kap Ñ a b m ω = ⊤}ᶜ := by
    ext ω; simp [lt_top_iff_ne_top]
  rw [this]; exact hT.measurableSet_top.compl

/-- One step of the decay: `P(κ_{m+1} < ∞) ≤ (1 - c₁) P(κ_m < ∞)`. -/
theorem prob_kap_succ_le (hd : 3 ≤ d) (a b : Fin d → ℤ) (hab : a ≠ b) (m : ℕ) :
    P {ω | kap Ñ a b (m + 1) ω < ⊤} ≤
      ENNReal.ofReal (1 - es8C1 d) * P {ω | kap Ñ a b m ω < ⊤} := by
  have := (drivers_isSRW h 0).isProbabilityMeasure
  set ζ := kap Ñ a b m with hζ
  have hT := kap_isStoppingTime h a b m
  set s : Set Ω := {ω | ζ ω < ⊤} with hs
  set t : Set Ω := {ω | kap Ñ a b (m + 1) ω < ⊤} with ht
  have hsm : MeasurableSet s := measurableSet_kap_lt_top h a b m
  have htm : MeasurableSet t := measurableSet_kap_lt_top h a b (m + 1)
  have hts : t ⊆ s := fun ω hω =>
    lt_top_iff_ne_top.2 (kap_succ_ne_top a b m (lt_top_iff_ne_top.1 hω))
  -- the freezing
  set ξ : Ω → Fin d → ℤ := fun ω => if ζ ω = ⊤ then 0 else drvD Ñ a b ω (stopReal ζ ω) with hξ
  have hξm : Measurable[hT.measurableSpace] ξ := by
    refine @measurable_to_countable' _ _ _ _ hT.measurableSpace _ fun z => ?_
    have : ξ ⁻¹' {z} = ({ω | ζ ω = ⊤} ∩ {_ω | z = 0}) ∪
        {ω | ζ ω ≠ ⊤ ∧ drvD Ñ a b ω (stopReal ζ ω) = z} := by
      ext ω
      by_cases hω : ζ ω = ⊤
      · simp [hξ, hω, eq_comm]
      · simp [hξ, hω]
    rw [this]
    refine MeasurableSet.union (MeasurableSet.inter
      (hT.measurable (measurableSet_singleton (⊤ : WithTop ℝ≥0))) ?_)
      (drvD_stopped_measurable h a b m z)
    exact MeasurableSet.const _
  set Γ : Set ((Fin d → ℤ) × PathSpace (d + d)) := {p | p.2 ∈ contactGamma p.1} with hΓ
  have hΓm : MeasurableSet Γ := by
    have : Γ = ⋃ z : Fin d → ℤ, {z} ×ˢ contactGamma z := by
      ext p; simp [hΓ]
    rw [this]
    exact MeasurableSet.iUnion fun z => (measurableSet_singleton z).prod (measurableSet_escGamma z)
  have hZ := drivers_pair_isSRW h
  have hF := drivers_pair_admissible h
  have hfreeze := hZ.freeze_param hF hT hξm (A := univ) MeasurableSet.univ hΓm
  -- lower bound for the right side
  have hlow : ENNReal.ofReal (es8C1 d) * P s ≤
      ∫⁻ ω in univ ∩ {ω | ζ ω < ⊤}, P.map (drvPair Ñ) (Prod.mk (ξ ω) ⁻¹' Γ) ∂P := by
    rw [univ_inter, ← hs]
    calc ENNReal.ofReal (es8C1 d) * P s = ∫⁻ _ in s, ENNReal.ofReal (es8C1 d) ∂P := by
          rw [setLIntegral_const]
      _ ≤ _ := by
          refine lintegral_mono_ae ?_
          rw [ae_restrict_iff' hsm]
          filter_upwards [drivers_ae_good h] with ω hG hωs
          have hne : ζ ω ≠ ⊤ := lt_top_iff_ne_top.1 hωs
          have hξω : ξ ω = drvD Ñ a b ω (stopReal ζ ω) := by simp [hξ, hne]
          have hpos : 0 < ‖drvD Ñ a b ω (stopReal ζ ω)‖ := drvD_kap_pos a b hab m hG hne
          have hle : ‖drvD Ñ a b ω (stopReal ζ ω)‖ ≤ 1 := drvD_kap_mem a b m hne
          have hp := prob_contactGamma h hd (norm_pos_iff.1 hpos) hle
          rw [Measure.map_apply (measurable_drvPair h) ((hΓm.preimage measurable_prodMk_left))]
          have : (drvPair Ñ ⁻¹' (Prod.mk (ξ ω) ⁻¹' Γ)) =
              {ω' | drvPair Ñ ω' ∈ contactGamma (drvD Ñ a b ω (stopReal ζ ω))} := by
            ext ω'; simp [hΓ, hξω]
          rw [this]; exact hp
  -- upper bound for the left side
  have hup : P (univ ∩ {ω | ζ ω < ⊤} ∩ {ω | (ξ ω, thetaAt ζ (drvPair Ñ) ω) ∈ Γ}) ≤ P (s \ t) := by
    refine measure_mono_ae ?_
    filter_upwards [drivers_ae_good h] with ω hG hω
    obtain ⟨⟨-, hωs⟩, hωΓ⟩ := hω
    have hne : ζ ω ≠ ⊤ := lt_top_iff_ne_top.1 hωs
    refine ⟨hωs, fun hωt => ?_⟩
    have hξω : ξ ω = drvD Ñ a b ω (stopReal ζ ω) := by simp [hξ, hne]
    have hth : thetaAt ζ (drvPair Ñ) ω = theta (stopReal ζ ω) (drvPair Ñ ω) := by
      simp [thetaAt, hne]
    have hΓω : theta (stopReal ζ ω) (drvPair Ñ ω) ∈
        contactGamma (drvD Ñ a b ω (stopReal ζ ω)) := by
      have : (ξ ω, thetaAt ζ (drvPair Ñ) ω) ∈ Γ := hωΓ
      rw [hξω, hth] at this
      exact this
    have := kap_succ_eq_top_of_scenario a b hab m hG hne hΓω
    exact absurd hωt (by simp [ht, this])
  have hsplit : P (s \ t) + P t = P s := by
    have := measure_sdiff_add_inter s htm (μ := P)
    rwa [inter_eq_right.2 hts] at this
  have hc1 : ENNReal.ofReal (es8C1 d) * P s + P t ≤ P s := by
    calc ENNReal.ofReal (es8C1 d) * P s + P t ≤ P (s \ t) + P t := by
          gcongr
          exact hlow.trans (hfreeze ▸ hup)
      _ = P s := hsplit
  have hfin : ENNReal.ofReal (es8C1 d) * P s ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top P s)
  have h2 := ENNReal.le_sub_of_add_le_left hfin hc1
  calc P t ≤ P s - ENNReal.ofReal (es8C1 d) * P s := h2
    _ = (ENNReal.ofReal 1 - ENNReal.ofReal (es8C1 d)) * P s := by
        rw [ENNReal.sub_mul (fun _ _ => measure_ne_top P s)]; simp
    _ = ENNReal.ofReal (1 - es8C1 d) * P s := by
        rw [← ENNReal.ofReal_sub 1 (es8C1_pos d).le]

/-- Contacts are few (ii): `P(κ_{m+1} < ∞) ≤ (1 - c₁)^m`. -/
theorem prob_kap_le (hd : 3 ≤ d) (a b : Fin d → ℤ) (hab : a ≠ b) (m : ℕ) :
    P {ω | kap Ñ a b m ω < ⊤} ≤ ENNReal.ofReal ((1 - es8C1 d) ^ m) := by
  have := (drivers_isSRW h 0).isProbabilityMeasure
  induction m with
  | zero => simpa using prob_le_one
  | succ m ih =>
    refine (prob_kap_succ_le h hd a b hab m).trans ?_
    rw [pow_succ', ENNReal.ofReal_mul (sub_nonneg.2 (es8C1_lt_one d).le)]
    gcongr

end

end ElboimSly.Paper
