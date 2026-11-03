/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Brownian.EscapeBox
import Mathlib

/-!
# Escaping a box for ever: the probability bound

Escaping a box for ever (a).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace ElboimSly.Brownian

lemma lamBox_ge_four (d : ℕ) : 4 ≤ lamBox d := le_max_left _ _

lemma Chit_pos {d : ℕ} (_hd : 3 ≤ d) : 0 < Chit d := by
  refine lt_of_lt_of_le ?_ (le_max_left _ _)
  positivity

/-- The hitting bound used after time `T`: `C_hit (2/λ)^{d-2} ≤ 1/2`. -/
lemma lam_arith {d : ℕ} (hd : 3 ≤ d) : Chit d * (2 / lamBox d) ^ (d - 2) ≤ 1 / 2 := by
  obtain ⟨m, rfl⟩ : ∃ m, d = m + 2 := ⟨d - 2, by omega⟩
  have hm : (1 : ℝ) ≤ m := by exact_mod_cast (by omega : 1 ≤ m)
  have hC := Chit_pos hd
  have hlam4 := lamBox_ge_four (m + 2)
  have hlam0 : 0 < lamBox (m + 2) := by linarith
  have hc2 : ((m + 2 : ℕ) : ℝ) - 2 = m := by push_cast; ring
  have h1 : 2 * (2 * Chit (m + 2)) ^ (1 / (m : ℝ)) ≤ lamBox (m + 2) := by
    unfold lamBox; rw [hc2]; exact le_max_right _ _
  set a : ℝ := (2 * Chit (m + 2)) ^ (1 / (m : ℝ)) with ha
  have ha0 : 0 < a := by positivity
  have ham : a ^ m = 2 * Chit (m + 2) := by
    rw [ha, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    have : 1 / (m : ℝ) * m = 1 := by field_simp
    rw [this, Real.rpow_one]
  have h2 : 2 / lamBox (m + 2) ≤ 1 / a := by
    rw [div_le_div_iff₀ hlam0 ha0]; linarith
  rw [Nat.add_sub_cancel]
  calc Chit (m + 2) * (2 / lamBox (m + 2)) ^ m ≤ Chit (m + 2) * (1 / a) ^ m :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) h2 m) hC.le
    _ = Chit (m + 2) / (2 * Chit (m + 2)) := by rw [one_div, inv_pow, ← ham]; ring
    _ = 1 / 2 := by field_simp

/-- The set of pairs `(z, w)` with `‖z + σ w(v)‖ > M L` in the sense of infima, for all `M'`. -/
def afterSet (d : ℕ) (σ M L : ℝ) : Set ((Fin d → ℝ) × PathSpace d) :=
  {q | ∀ M' : ℕ, ((M * L : ℝ) : EReal) <
    ⨅ v ∈ denseSub (Set.Icc (0 : ℝ≥0) M'), ((‖q.1 + σ • q.2 v‖ : ℝ) : EReal)}

lemma measurableSet_afterSet (d : ℕ) (σ M L : ℝ) : MeasurableSet (afterSet d σ M L) := by
  have e : afterSet d σ M L = ⋂ M' : ℕ, {q : (Fin d → ℝ) × PathSpace d | ((M * L : ℝ) : EReal) <
      ⨅ v ∈ denseSub (Set.Icc (0 : ℝ≥0) M'), ((‖q.1 + σ • q.2 v‖ : ℝ) : EReal)} := by
    ext q; simp [afterSet]
  rw [e]
  refine MeasurableSet.iInter fun M' => ?_
  refine measurableSet_lt measurable_const (Measurable.biInf _ (denseSub_countable _) fun v _ => ?_)
  exact measurable_coe_real_ereal.comp
    (by fun_prop : Measurable fun q : (Fin d → ℝ) × PathSpace d => ‖q.1 + σ • q.2 v‖)

section B

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {d : ℕ}
  {B : ℝ≥0 → Ω → (Fin d → ℝ)}

/-- After time `T`: from a point `z` with `‖z‖ ≥ R/2`, the path stays outside the cube of radius
`M L` with probability at least `1/2`. -/
theorem after_prob [IsProbabilityMeasure P] (hB : IsStandardBrownianMotion d B P) (hd : 3 ≤ d)
    {σ M L : ℝ} (hσ1 : 1 ≤ σ) (_hσ2 : σ ≤ 2) (hM : 1 ≤ M) (hL : 0 < L) {z : Fin d → ℝ}
    (hz : lamBox d * M * L / 2 ≤ ‖z‖) :
    (1 / 2 : ℝ≥0∞) ≤ P {ω | (z, pathMap B ω) ∈ afterSet d σ M L} := by
  have hσ0 : 0 < σ := by linarith
  have hlam0 : 0 < lamBox d := by linarith [lamBox_ge_four d]
  have hML : 0 < M * L := by positivity
  have hzpos : 0 < ‖z‖ := lt_of_lt_of_le (by positivity) hz
  have hz0 : (0 : Fin d → ℝ) ≠ z := fun h => by rw [← h, norm_zero] at hzpos; exact lt_irrefl _ hzpos
  have hmeas : MeasurableSet {ω | (z, pathMap B ω) ∈ afterSet d σ M L} :=
    (measurable_const.prodMk hB.measurable_pathMap) (measurableSet_afterSet d σ M L)
  have hsub : {ω | (z, pathMap B ω) ∈ afterSet d σ M L}ᶜ ⊆
      {ω | ∃ t : ℝ≥0, ‖z + σ • B t ω - 0‖ ≤ M * L} := by
    intro ω hω
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, afterSet, not_forall, not_lt] at hω
    obtain ⟨M', hM'⟩ := hω
    have hcont : Continuous fun t : ℝ≥0 => z + σ • B t ω := by
      have := (hB.continuous_zero ω).1
      exact continuous_const.add (this.const_smul σ)
    obtain ⟨t, -, ht⟩ := (exists_mem_le_iff_iInf_le (J := Set.Icc (0 : ℝ≥0) M')
      Set.ordConnected_Icc isCompact_Icc ⟨0, le_rfl, zero_le⟩ hcont 0 (M * L)).2 (by
        simpa [sub_zero, pathMap] using hM')
    exact ⟨t, ht⟩
  have hhit := hit_ball_le hB hd hz0 hML hσ0
  have hb : Chit d * (M * L / ‖z - 0‖) ^ (d - 2) ≤ 1 / 2 := by
    rw [sub_zero]
    refine le_trans ?_ (lam_arith hd)
    refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) ?_ _) (Chit_pos hd).le
    rw [div_le_div_iff₀ hzpos hlam0]
    nlinarith
  have hP : P {ω | (z, pathMap B ω) ∈ afterSet d σ M L}ᶜ ≤ 1 / 2 := by
    refine (measure_mono hsub).trans (hhit.trans ?_)
    calc _ ≤ ENNReal.ofReal (1 / 2) := ENNReal.ofReal_le_ofReal hb
      _ = 1 / 2 := by rw [ENNReal.ofReal_div_of_pos (by norm_num)]; simp
  rw [prob_compl_eq_one_sub hmeas] at hP
  have h1 : 1 ≤ P {ω | (z, pathMap B ω) ∈ afterSet d σ M L} + 1 / 2 := tsub_le_iff_left.1 hP
  have h2 : (1 / 2 : ℝ≥0∞) + 1 / 2 ≤ 1 / 2 + P {ω | (z, pathMap B ω) ∈ afterSet d σ M L} := by
    rw [ENNReal.add_halves, add_comm]; exact h1
  exact (ENNReal.add_le_add_iff_left (by simp)).1 h2

end B

section Abstract

variable {Ω : Type*} {m : MeasurableSpace Ω} {d : ℕ}

lemma measurableSet_pathTube2 {B : ℝ≥0 → Ω → (Fin d → ℝ)} {T : ℝ≥0}
    (hB : ∀ s ≤ T, Measurable (B s)) (σ : ℝ) (x : Fin d → ℝ) (f : ℝ → Fin d → ℝ) (ρ : ℝ) :
    MeasurableSet {ω | (fun s => B s ω) ∈ tube2Set d σ x f ρ T} := by
  have hTT : (T / 2 : ℝ≥0) ≤ T := by
    rw [← NNReal.coe_le_coe]; push_cast; linarith [T.2]
  have e : {ω | (fun s => B s ω) ∈ tube2Set d σ x f ρ T} =
      (⋂ u ∈ denseSub (Set.Icc (0 : ℝ≥0) (T / 2)), {ω | ‖x + σ • B u ω - f u‖ ≤ ρ}) ∩
      (⋂ v ∈ denseSub (Set.Icc (0 : ℝ≥0) (T / 2)),
        {ω | ‖x + σ • B (T / 2 + v) ω - f ((T / 2 + v : ℝ≥0) : ℝ)‖ ≤ ρ / 5}) := by
    ext ω; simp [tube2Set]
  rw [e]
  refine (MeasurableSet.biInter (denseSub_countable _) fun u hu => ?_).inter
    (MeasurableSet.biInter (denseSub_countable _) fun v hv => ?_)
  · have := hB u ((denseSub_subset _ hu).2.trans hTT)
    exact measurableSet_le (((this.const_smul σ).const_add x).sub_const _).norm measurable_const
  · have hv' := (denseSub_subset _ hv).2
    have := hB (T / 2 + v) (by
      rw [← NNReal.coe_le_coe]; push_cast
      have := NNReal.coe_le_coe.2 hv'
      push_cast at this; linarith)
    exact measurableSet_le (((this.const_smul σ).const_add x).sub_const _).norm measurable_const

end Abstract

section Main

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {d : ℕ}
  {B : ℝ≥0 → Ω → (Fin d → ℝ)}

/-- Escaping a box for ever (a). -/
theorem escapeBox_prob [IsProbabilityMeasure P] (hB : IsStandardBrownianMotion d B P)
    (hd : 3 ≤ d) (i0 : Fin d) {σ : ℝ} (hσ1 : 1 ≤ σ) (hσ2 : σ ≤ 2) {M : ℝ} (hM : 1 ≤ M) {L : ℝ}
    (hL : 0 < L) :
    ENNReal.ofReal (qbox d M) ≤ P {ω | pathMap B ω ∈ escapeBoxSet d i0 σ M L} := by
  have hσ0 : 0 < σ := by linarith
  have hlam4 := lamBox_ge_four d
  set lam := lamBox d with hlam
  have hlam0 : 0 < lam := by linarith
  set R : ℝ := lam * M * L with hR
  set ρ : ℝ := L / 2 with hρ
  have hρ0 : 0 < ρ := by positivity
  set K : ℝ := 2 * lam * M with hK
  have hK1 : 1 ≤ K := by nlinarith
  set T : ℝ≥0 := escT d M L with hTdef
  have hTR : (T : ℝ) = K * ρ ^ 2 := by
    rw [hTdef, escT, Real.coe_toNNReal _ (by positivity)]
    rw [hK, hρ]; ring
  have hTpos : 0 < (T : ℝ) := by rw [hTR]; positivity
  set f : ℝ → Fin d → ℝ := fun u => (u / T * R) • e0 i0 with hf
  have hLip : ∀ u ∈ Set.Icc (0 : ℝ) T, ∀ v ∈ Set.Icc (0 : ℝ) T,
      ‖f u - f v‖ ≤ K / ρ * |u - v| := by
    intro u _ v _
    have e : f u - f v = ((u - v) / T * R) • e0 i0 := by
      simp only [hf]; rw [← sub_smul]; congr 1; ring
    rw [e, norm_smul, norm_e0, mul_one, Real.norm_eq_abs, abs_mul, abs_div, abs_of_pos hTpos,
      abs_of_pos (by positivity : 0 < R)]
    have h1 : R / T = 1 / ρ := by
      rw [hTR, hK, hR, hρ]; field_simp
    calc |u - v| / T * R = |u - v| * (R / T) := by ring
      _ = |u - v| * (1 / ρ) := by rw [h1]
      _ ≤ |u - v| * (K / ρ) := by
          gcongr
      _ = K / ρ * |u - v| := by ring
  have hf0 : f 0 = 0 := by simp [hf]
  have hT1ok : ρ ^ 2 / K ≤ T := by
    rw [hTR, div_le_iff₀ (by linarith)]
    have : 1 ≤ K * K := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right this (sq_nonneg ρ)]
  have hTube := tube_lemma (x := (0 : Fin d → ℝ)) hB hK1 hσ1 hσ2 hρ0 (T := T)
    hT1ok hTR.le hLip (by rw [hf0]; simp; positivity)
  set P1 : Set Ω := {ω | pathMap B ω ∈ tube2Set d σ 0 f ρ T} with hP1def
  -- Markov property at time `T`
  set Φ : (Fin d → ℝ) → PathSpace d → ℝ≥0∞ := fun z w =>
    (afterSet d σ M L).indicator 1 (z, w) with hΦdef
  have hΦ : Measurable (Function.uncurry Φ) := by
    have : Function.uncurry Φ = (afterSet d σ M L).indicator 1 := by
      funext ⟨z, w⟩; rfl
    rw [this]
    exact measurable_one.indicator (measurableSet_afterSet d σ M L)
  have hA : MeasurableSet[bmFiltration B T] P1 :=
    @measurableSet_pathTube2 Ω (bmFiltration B T) d B T (fun s hs => measurable_bmFiltration hs)
      σ 0 f ρ
  have hZ : Measurable[bmFiltration B T] (fun ω => σ • B T ω) :=
    (measurable_bmFiltration (B := B) le_rfl).const_smul σ
  have key := hB.lintegral_indicator_shift T hZ hA hΦ
  have hP1m : MeasurableSet P1 := bmFiltration_le hB.measurable T _ hA
  set Q2 : Set Ω := {ω | (σ • B T ω, shiftPath B T ω) ∈ afterSet d σ M L} with hQ2def
  have hQ2m : MeasurableSet Q2 :=
    (((hB.measurable T).const_smul σ).prodMk (measurable_shiftPath hB.measurable T))
      (measurableSet_afterSet d σ M L)
  have hlhs : ∫⁻ ω, P1.indicator (fun ω => Φ (σ • B T ω) (shiftPath B T ω)) ω ∂P =
      P (P1 ∩ Q2) := by
    rw [← lintegral_indicator_one (hP1m.inter hQ2m)]
    refine lintegral_congr fun ω => ?_
    by_cases h1 : ω ∈ P1
    · by_cases h2 : ω ∈ Q2
      · rw [Set.indicator_of_mem h1, Set.indicator_of_mem (show ω ∈ P1 ∩ Q2 from ⟨h1, h2⟩)]
        exact Set.indicator_of_mem (show (σ • B T ω, shiftPath B T ω) ∈ afterSet d σ M L from h2) _
      · rw [Set.indicator_of_mem h1,
          Set.indicator_of_notMem (show ω ∉ P1 ∩ Q2 from fun hh => h2 hh.2)]
        exact Set.indicator_of_notMem
          (show (σ • B T ω, shiftPath B T ω) ∉ afterSet d σ M L from h2) _
    · rw [Set.indicator_of_notMem h1, Set.indicator_of_notMem (fun hh => h1 hh.1)]
  have hfc := continuousOn_of_lip hLip
  have hrhs : (1 / 2 : ℝ≥0∞) * P P1 ≤ P (P1 ∩ Q2) := by
    rw [← hlhs, key, ← lintegral_indicator_const hP1m]
    refine lintegral_mono fun ω => ?_
    by_cases h1 : ω ∈ P1
    · rw [Set.indicator_of_mem h1, Set.indicator_of_mem h1]
      have hfib : MeasurableSet (Prod.mk (σ • B T ω) ⁻¹' afterSet d σ M L) :=
        measurable_prodMk_left (measurableSet_afterSet d σ M L)
      have e : Φ (σ • B T ω) = (Prod.mk (σ • B T ω) ⁻¹' afterSet d σ M L).indicator 1 := by
        funext w; rfl
      rw [e, lintegral_indicator_one hfib, ← hB.map_pathMap_eq_wiener,
        Measure.map_apply hB.measurable_pathMap hfib]
      refine after_prob hB hd hσ1 hσ2 hM hL ?_
      have hmem : pathMap B ω ∈ tube2Set d σ 0 f ρ T := h1
      have hev := (mem_tube2Set_iff (continuous_path hB ω) σ 0 hρ0.le hfc).1 hmem
      have hT2 : (T / 2 : ℝ≥0) ≤ T := by
        rw [← NNReal.coe_le_coe]; push_cast; linarith
      have hend := hev.2 T hT2 le_rfl
      have e2 : f T = R • e0 i0 := by
        simp only [hf]; rw [div_self hTpos.ne', one_mul]
      rw [e2] at hend
      have h3 : ‖R • e0 i0‖ = R := by
        rw [norm_smul, norm_e0, mul_one, Real.norm_eq_abs, abs_of_pos (by positivity)]
      have h4 : ‖R • e0 i0‖ ≤ ‖σ • B T ω‖ + ‖R • e0 i0 - σ • B T ω‖ := by
        have := norm_add_le (σ • B T ω) (R • e0 i0 - σ • B T ω)
        rwa [add_sub_cancel] at this
      have h5 : ‖(0 : Fin d → ℝ) + σ • B T ω - R • e0 i0‖ = ‖R • e0 i0 - σ • B T ω‖ := by
        rw [zero_add, norm_sub_rev]
      have hRρ : ρ / 5 ≤ R / 2 := by
        rw [hρ, hR]
        nlinarith [mul_pos hL hL, mul_pos (mul_pos hlam0 (by linarith : (0:ℝ) < M)) hL]
      have hend' : ‖R • e0 i0 - σ • B T ω‖ ≤ ρ / 5 := by rw [← h5]; exact hend
      show lamBox d * M * L / 2 ≤ ‖σ • B T ω‖
      rw [← hlam, ← hR]
      linarith
    · rw [Set.indicator_of_notMem h1, Set.indicator_of_notMem h1]
  have hsub : P1 ∩ Q2 ⊆ {ω | pathMap B ω ∈ escapeBoxSet d i0 σ M L} := by
    rintro ω ⟨h1, h2⟩
    have hmem : pathMap B ω ∈ tube2Set d σ 0 f ρ T := h1
    have hev := (mem_tube2Set_iff (continuous_path hB ω) σ 0 hρ0.le hfc).1 hmem
    refine ⟨fun u hu => ?_, fun M' => ?_⟩
    · have := hev.1 u (denseSub_subset _ hu).2
      simpa [hf] using this
    · have := h2 M'
      refine this.trans_eq (iInf_congr fun v => iInf_congr fun _ => ?_)
      have e : σ • B T ω + σ • shiftPath B T ω v = σ • B (T + v) ω := by
        simp only [shiftPath]; rw [← smul_add]; congr 1; abel
      rw [e]; rfl
  calc ENNReal.ofReal (qbox d M) = (1 / 2 : ℝ≥0∞) * ENNReal.ofReal (ctube d K) := by
        unfold qbox
        rw [ENNReal.ofReal_div_of_pos (by norm_num)]
        simp [hK, hlam]
        rw [div_eq_mul_inv, mul_comm]
    _ ≤ (1 / 2 : ℝ≥0∞) * P P1 := mul_le_mul_right hTube _
    _ ≤ P (P1 ∩ Q2) := hrhs
    _ ≤ _ := measure_mono hsub

end Main

end ElboimSly.Brownian
