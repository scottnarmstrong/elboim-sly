/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Brownian.EscapeLine
import Mathlib

/-!
# Escaping a box and a line of points: the probability bound

Escaping a box and a line of points (a).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace ElboimSly.Brownian

lemma ctube_pos (d : ℕ) (K : ℝ) : 0 < ctube d K := by
  unfold ctube tubeC0; positivity

lemma qbox_pos (d : ℕ) (M : ℝ) : 0 < qbox d M := by
  unfold qbox; have := ctube_pos d (2 * lamBox d * M); positivity

lemma qstar_pos (d : ℕ) : 0 < qstar d := qbox_pos d 60

/-- The pairs `(z, w)` with `‖(z + σ w(v))~‖ > 2a/3` in the sense of infima, for all `M'`
(`~` drops the coordinate `i1`). -/
def lineCond {n : ℕ} (i1 : Fin (n + 1)) (σ a : ℝ) : Set ((Fin (n + 1) → ℝ) × PathSpace (n + 1)) :=
  {q | ∀ M' : ℕ, ((2 * a / 3 : ℝ) : EReal) <
    ⨅ v ∈ denseSub (Set.Icc (0 : ℝ≥0) M'),
      ((‖fun k : Fin n => (q.1 + σ • q.2 v) (i1.succAbove k)‖ : ℝ) : EReal)}

lemma measurableSet_lineCond {n : ℕ} (i1 : Fin (n + 1)) (σ a : ℝ) :
    MeasurableSet (lineCond i1 σ a) := by
  unfold lineCond
  rw [Set.ofPred_forall]
  refine MeasurableSet.iInter fun M' => ?_
  refine measurableSet_lt measurable_const (Measurable.biInf _ (denseSub_countable _) fun v _ => ?_)
  exact measurable_coe_real_ereal.comp
    (by fun_prop : Measurable fun q : (Fin (n + 1) → ℝ) × PathSpace (n + 1) =>
      ‖fun k : Fin n => (q.1 + σ • q.2 v) (i1.succAbove k)‖)

/-- The pairs `(z, w)` for which the stage 2 conditions of escaping a box and a line of points hold: the path
`w` is in the box set, and the line condition holds. -/
def lineAfter {n : ℕ} (i0 i1 : Fin (n + 1)) (σ a A : ℝ) :
    Set ((Fin (n + 1) → ℝ) × PathSpace (n + 1)) :=
  {q | q.2 ∈ escapeBoxSet (n + 1) i0 σ 60 (A / 20)} ∩ lineCond i1 σ a

lemma measurableSet_lineAfter {n : ℕ} (i0 i1 : Fin (n + 1)) (σ a A : ℝ) :
    MeasurableSet (lineAfter i0 i1 σ a A) :=
  (measurable_snd (measurableSet_escapeBoxSet _ _ _ _ _)).inter (measurableSet_lineCond _ _ _)

/-- The numerical bound of stage 2: `C_hit (2a/3 / ‖z̃‖)^{n-2} ≤ q_*/2` when `‖z̃‖ ≥ M₁ a/2`. -/
lemma line_numeric {n : ℕ} (hn : 3 ≤ n) {a : ℝ} (ha : 0 < a) {t : ℝ}
    (ht : lineM1 (n + 1) * a / 2 ≤ t) :
    Chit n * (2 * a / 3 / t) ^ (n - 2) ≤ qstar (n + 1) / 2 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have hm : (1 : ℝ) ≤ m := by exact_mod_cast (by omega : 1 ≤ m)
  have hC := Chit_pos (d := m + 2) (by omega)
  have hq := qstar_pos (m + 2 + 1)
  have hM1 := lineM1_ge_two (m + 2 + 1)
  set M1 := lineM1 (m + 2 + 1) with hM1def
  have hc3 : ((m + 2 + 1 : ℕ) : ℝ) - 3 = m := by push_cast; ring
  set b : ℝ := (2 * Chit (m + 2) / qstar (m + 2 + 1)) ^ (1 / (m : ℝ)) with hb
  have hb0 : 0 < b := by positivity
  have hbm : b ^ m = 2 * Chit (m + 2) / qstar (m + 2 + 1) := by
    rw [hb, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    have : 1 / (m : ℝ) * m = 1 := by field_simp
    rw [this, Real.rpow_one]
  have hMb : 4 / 3 * b ≤ M1 := by
    have : 4 / 3 * (2 * Chit (m + 2 + 1 - 1) / qstar (m + 2 + 1)) ^ (1 / (((m + 2 + 1 : ℕ) : ℝ) - 3))
        ≤ M1 := le_max_right _ _
    rwa [hc3, Nat.add_sub_cancel] at this
  have ht0 : 0 < t := lt_of_lt_of_le (by positivity) ht
  have h1 : 2 * a / 3 / t ≤ 1 / b := by
    rw [div_le_div_iff₀ ht0 hb0]
    nlinarith
  rw [Nat.add_sub_cancel]
  calc Chit (m + 2) * (2 * a / 3 / t) ^ m ≤ Chit (m + 2) * (1 / b) ^ m :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) h1 m) hC.le
    _ = qstar (m + 2 + 1) / 2 := by
        rw [one_div, inv_pow, ← one_div, hbm]; field_simp

section B

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {n : ℕ}
  {B : ℝ≥0 → Ω → (Fin (n + 1) → ℝ)}

/-- One trial of stage 2: from a point `z` whose `i0`-coordinate is at least `M₁ a/2`, the box
and line conditions hold with probability at least `q_*/2`. -/
theorem lineAfter_prob [IsProbabilityMeasure P] (hB : IsStandardBrownianMotion (n + 1) B P)
    (hn : 3 ≤ n) {i0 i1 : Fin (n + 1)} (hne : i0 ≠ i1) {σ a A : ℝ} (hσ1 : 1 ≤ σ) (hσ2 : σ ≤ 2)
    (ha : 0 < a) (hA : 0 < A) {z : Fin (n + 1) → ℝ} (hz : lineM1 (n + 1) * a / 2 ≤ z i0) :
    ENNReal.ofReal (qstar (n + 1) / 2) ≤ P {ω | (z, pathMap B ω) ∈ lineAfter i0 i1 σ a A} := by
  have hσ0 : 0 < σ := by linarith
  set M1 := lineM1 (n + 1) with hM1def
  have hM1 : 2 ≤ M1 := lineM1_ge_two (n + 1)
  have hq0 := qstar_pos (n + 1)
  set Esc : Set Ω := {ω | pathMap B ω ∈ escapeBoxSet (n + 1) i0 σ 60 (A / 20)} with hEsc
  set Lz : Set Ω := {ω | (z, pathMap B ω) ∈ lineCond i1 σ a} with hLz
  have hEscm : MeasurableSet Esc := hB.measurable_pathMap (measurableSet_escapeBoxSet _ _ _ _ _)
  have hLzm : MeasurableSet Lz :=
    (measurable_const.prodMk hB.measurable_pathMap) (measurableSet_lineCond _ _ _)
  have hset : {ω | (z, pathMap B ω) ∈ lineAfter i0 i1 σ a A} = Esc ∩ Lz := rfl
  have hEscP : ENNReal.ofReal (qstar (n + 1)) ≤ P Esc := by
    have := escapeBox_prob hB (by omega) i0 hσ1 hσ2 (M := 60) (by norm_num) (L := A / 20)
      (by positivity)
    exact this
  -- the line bound
  obtain ⟨k0, hk0⟩ := Fin.exists_succAbove_eq hne
  set Bt : ℝ≥0 → Ω → (Fin n → ℝ) := fun t ω k => B t ω (i1.succAbove k) with hBt
  have hBtstd : IsStandardBrownianMotion n Bt P :=
    hB.subvector (ι := i1.succAbove) (Fin.succAbove_right_injective)
  set zt : Fin n → ℝ := fun k => z (i1.succAbove k) with hzt
  have hztnorm : M1 * a / 2 ≤ ‖zt‖ := by
    have h1 := norm_le_pi_norm zt k0
    have h2 : zt k0 = z i0 := by simp [hzt, hk0]
    rw [h2, Real.norm_eq_abs] at h1
    exact hz.trans ((le_abs_self _).trans h1)
  have hM1a : 0 < M1 * a := mul_pos (by linarith) ha
  have hztpos : 0 < ‖zt‖ := lt_of_lt_of_le (half_pos hM1a) hztnorm
  have hzt0 : (0 : Fin n → ℝ) ≠ zt := fun h => by rw [← h, norm_zero] at hztpos; exact lt_irrefl _ hztpos
  have hsub : Lzᶜ ⊆ {ω | ∃ t : ℝ≥0, ‖zt + σ • Bt t ω - 0‖ ≤ 2 * a / 3} := by
    intro ω hω
    by_contra hcon
    apply hω
    show (z, pathMap B ω) ∈ lineCond i1 σ a
    intro M'
    by_contra hM'
    rw [not_lt] at hM'
    have hcont : Continuous fun t : ℝ≥0 => zt + σ • Bt t ω := by
      refine continuous_const.add (Continuous.const_smul ?_ σ)
      exact continuous_pi fun k => (continuous_apply (i1.succAbove k)).comp (hB.continuous_zero ω).1
    obtain ⟨t, -, ht⟩ := (exists_mem_le_iff_iInf_le (J := Set.Icc (0 : ℝ≥0) M')
      Set.ordConnected_Icc isCompact_Icc ⟨0, le_rfl, zero_le⟩ hcont 0 (2 * a / 3)).2 (by
        simp only [sub_zero]; exact hM')
    exact hcon ⟨t, ht⟩
  have hhit := hit_ball_le hBtstd hn hzt0 (r := 2 * a / 3) (by positivity) hσ0
  have hnum : Chit n * (2 * a / 3 / ‖zt - 0‖) ^ (n - 2) ≤ qstar (n + 1) / 2 :=
    by rw [sub_zero]; exact line_numeric hn ha hztnorm
  have hLzc : P Lzᶜ ≤ ENNReal.ofReal (qstar (n + 1) / 2) :=
    (measure_mono hsub).trans (hhit.trans (ENNReal.ofReal_le_ofReal hnum))
  rw [hset]
  have h1 : ENNReal.ofReal (qstar (n + 1)) ≤ P (Esc ∩ Lz) + ENNReal.ofReal (qstar (n + 1) / 2) := by
    refine hEscP.trans ?_
    refine (measure_mono (fun ω hω => ?_)).trans ((measure_union_le _ _).trans
      (add_le_add le_rfl hLzc))
    by_cases h : ω ∈ Lz
    · exact Or.inl ⟨hω, h⟩
    · exact Or.inr h
  have h2 : ENNReal.ofReal (qstar (n + 1)) - ENNReal.ofReal (qstar (n + 1) / 2) =
      ENNReal.ofReal (qstar (n + 1) / 2) := by
    rw [← ENNReal.ofReal_sub _ (by positivity)]
    congr 1; ring
  rw [← h2]
  exact tsub_le_iff_right.2 h1

end B

section Main

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {n : ℕ}
  {B : ℝ≥0 → Ω → (Fin (n + 1) → ℝ)}

/-- Escaping a box and a line of points (a). -/
theorem lineSet_prob [IsProbabilityMeasure P] (hB : IsStandardBrownianMotion (n + 1) B P)
    (hn : 3 ≤ n) {i0 i1 : Fin (n + 1)} (hne : i0 ≠ i1) {σ a A : ℝ} (hσ1 : 1 ≤ σ) (hσ2 : σ ≤ 2)
    (ha : 0 < a) (hA : Cline (n + 1) * a ≤ A) :
    ENNReal.ofReal (cline (n + 1)) ≤ P {ω | pathMap B ω ∈ lineSet i0 i1 σ a A} := by
  have hσ0 : 0 < σ := by linarith
  obtain ⟨hC1, hC2⟩ := Cline_ge (n + 1)
  set M1 := lineM1 (n + 1) with hM1def
  have hM1 : 2 ≤ M1 := lineM1_ge_two (n + 1)
  have hA400 : 400 * a ≤ A := by nlinarith
  have hApos : 0 < A := by nlinarith
  set T1 : ℝ≥0 := lineT (n + 1) a with hT1
  have hT1R : (T1 : ℝ) = M1 * a * (a / 3) := lineT_coe ha
  have hT1pos : 0 < (T1 : ℝ) := by rw [hT1R]; positivity
  set ρ : ℝ := a / 3 with hρ
  have hρ0 : 0 < ρ := by positivity
  set K : ℝ := 3 * M1 with hK
  have hK1 : 1 ≤ K := by linarith
  have hTK : (T1 : ℝ) = K * ρ ^ 2 := by rw [hT1R, hK, hρ]; ring
  have hLip : ∀ u ∈ Set.Icc (0 : ℝ) T1, ∀ v ∈ Set.Icc (0 : ℝ) T1,
      ‖lineF i0 a u - lineF i0 a v‖ ≤ K / ρ * |u - v| := by
    intro u _ v _
    have e : lineF i0 a u - lineF i0 a v = ((u - v) / T1 * (M1 * a)) • e0 i0 := by
      simp only [lineF]; rw [← sub_smul]; congr 1; ring
    rw [e, norm_smul, norm_e0, mul_one, Real.norm_eq_abs, abs_mul, abs_div, abs_of_pos hT1pos,
      abs_of_pos (by positivity : 0 < M1 * a)]
    have h1 : M1 * a / T1 = 1 / ρ := by
      rw [hT1R, hρ]; field_simp
    calc |u - v| / T1 * (M1 * a) = |u - v| * (M1 * a / T1) := by ring
      _ = |u - v| * (1 / ρ) := by rw [h1]
      _ ≤ |u - v| * (K / ρ) := by gcongr
      _ = K / ρ * |u - v| := by ring
  have hf0 : lineF i0 a 0 = 0 := by simp [lineF]
  have hT1ok : ρ ^ 2 / K ≤ T1 := by
    rw [hTK, div_le_iff₀ (by linarith)]
    have : 1 ≤ K * K := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right this (sq_nonneg ρ)]
  have hTube := tube_lemma (x := (0 : Fin (n + 1) → ℝ)) hB hK1 hσ1 hσ2 hρ0 (T := T1) hT1ok
    hTK.le hLip (by rw [hf0]; simp; positivity)
  set P1 : Set Ω := {ω | pathMap B ω ∈ tube2Set (n + 1) σ 0 (lineF i0 a) ρ T1} with hP1def
  -- Markov property at time `T₁`
  set Φ : (Fin (n + 1) → ℝ) → PathSpace (n + 1) → ℝ≥0∞ := fun z w =>
    (lineAfter i0 i1 σ a A).indicator 1 (z, w) with hΦdef
  have hΦ : Measurable (Function.uncurry Φ) := by
    have : Function.uncurry Φ = (lineAfter i0 i1 σ a A).indicator 1 := by
      funext ⟨z, w⟩; rfl
    rw [this]
    exact measurable_one.indicator (measurableSet_lineAfter _ _ _ _ _)
  have hA' : MeasurableSet[bmFiltration B T1] P1 :=
    @measurableSet_pathTube2 Ω (bmFiltration B T1) (n + 1) B T1
      (fun s hs => measurable_bmFiltration hs) σ 0 (lineF i0 a) ρ
  have hZ : Measurable[bmFiltration B T1] (fun ω => σ • B T1 ω) :=
    (measurable_bmFiltration (B := B) le_rfl).const_smul σ
  have key := hB.lintegral_indicator_shift T1 hZ hA' hΦ
  have hP1m : MeasurableSet P1 := bmFiltration_le hB.measurable T1 _ hA'
  set Q2 : Set Ω := {ω | (σ • B T1 ω, shiftPath B T1 ω) ∈ lineAfter i0 i1 σ a A} with hQ2def
  have hQ2m : MeasurableSet Q2 :=
    (((hB.measurable T1).const_smul σ).prodMk (measurable_shiftPath hB.measurable T1))
      (measurableSet_lineAfter _ _ _ _ _)
  have hlhs : ∫⁻ ω, P1.indicator (fun ω => Φ (σ • B T1 ω) (shiftPath B T1 ω)) ω ∂P =
      P (P1 ∩ Q2) := by
    rw [← lintegral_indicator_one (hP1m.inter hQ2m)]
    refine lintegral_congr fun ω => ?_
    by_cases h1 : ω ∈ P1
    · by_cases h2 : ω ∈ Q2
      · rw [Set.indicator_of_mem h1, Set.indicator_of_mem (show ω ∈ P1 ∩ Q2 from ⟨h1, h2⟩)]
        exact Set.indicator_of_mem
          (show (σ • B T1 ω, shiftPath B T1 ω) ∈ lineAfter i0 i1 σ a A from h2) _
      · rw [Set.indicator_of_mem h1,
          Set.indicator_of_notMem (show ω ∉ P1 ∩ Q2 from fun hh => h2 hh.2)]
        exact Set.indicator_of_notMem
          (show (σ • B T1 ω, shiftPath B T1 ω) ∉ lineAfter i0 i1 σ a A from h2) _
    · rw [Set.indicator_of_notMem h1, Set.indicator_of_notMem (fun hh => h1 hh.1)]
  have hfc := continuousOn_of_lip hLip
  have hrhs : ENNReal.ofReal (qstar (n + 1) / 2) * P P1 ≤ P (P1 ∩ Q2) := by
    rw [← hlhs, key, ← lintegral_indicator_const hP1m]
    refine lintegral_mono fun ω => ?_
    by_cases h1 : ω ∈ P1
    · rw [Set.indicator_of_mem h1, Set.indicator_of_mem h1]
      have hfib : MeasurableSet (Prod.mk (σ • B T1 ω) ⁻¹' lineAfter i0 i1 σ a A) :=
        measurable_prodMk_left (measurableSet_lineAfter _ _ _ _ _)
      have e : Φ (σ • B T1 ω) = (Prod.mk (σ • B T1 ω) ⁻¹' lineAfter i0 i1 σ a A).indicator 1 := by
        funext w; rfl
      rw [e, lintegral_indicator_one hfib, ← hB.map_pathMap_eq_wiener,
        Measure.map_apply hB.measurable_pathMap hfib]
      refine lineAfter_prob hB hn hne hσ1 hσ2 ha hApos ?_
      have hmem : pathMap B ω ∈ tube2Set (n + 1) σ 0 (lineF i0 a) ρ T1 := h1
      have hev := (mem_tube2Set_iff (continuous_path hB ω) σ 0 hρ0.le hfc).1 hmem
      have hT12 : (T1 / 2 : ℝ≥0) ≤ T1 := by
        rw [← NNReal.coe_le_coe]; push_cast; linarith
      have hend := hev.2 T1 hT12 le_rfl
      have e2 : lineF i0 a T1 = (M1 * a) • e0 i0 := by
        simp only [lineF]; rw [div_self hT1pos.ne', one_mul]
      rw [e2] at hend
      have h1' := norm_le_pi_norm (0 + σ • pathMap B ω T1 - (M1 * a) • e0 i0) i0
      have hc : (0 + σ • pathMap B ω T1 - (M1 * a) • e0 i0) i0 =
          σ * B T1 ω i0 - M1 * a := by
        simp [pathMap, e0_apply_self]
      rw [hc, Real.norm_eq_abs] at h1'
      have h2 := (abs_le.1 (h1'.trans hend)).1
      show M1 * a / 2 ≤ (σ • B T1 ω) i0
      simp only [Pi.smul_apply, smul_eq_mul]
      nlinarith
    · rw [Set.indicator_of_notMem h1, Set.indicator_of_notMem h1]
  have hsub : P1 ∩ Q2 ⊆ {ω | pathMap B ω ∈ lineSet i0 i1 σ a A} := by
    rintro ω ⟨h1, h2⟩
    refine ⟨h1, h2.1, fun M' => ?_⟩
    have := h2.2 M'
    refine this.trans_eq (iInf_congr fun v => iInf_congr fun _ => ?_)
    have e : (fun k : Fin n => (σ • B T1 ω + σ • shiftPath B T1 ω v) (i1.succAbove k)) =
        fun k : Fin n => σ • pathMap B ω (T1 + v) (i1.succAbove k) := by
      funext k
      simp only [Pi.add_apply, Pi.smul_apply, shiftPath, Pi.sub_apply, pathMap, smul_eq_mul]
      ring
    rw [e]
  calc ENNReal.ofReal (cline (n + 1)) =
      ENNReal.ofReal (qstar (n + 1) / 2) * ENNReal.ofReal (ctube (n + 1) K) := by
        unfold cline
        rw [← ENNReal.ofReal_mul (by have := qstar_pos (n + 1); positivity)]
        congr 1; rw [hK, hM1def]; ring
    _ ≤ ENNReal.ofReal (qstar (n + 1) / 2) * P P1 := mul_le_mul_right hTube _
    _ ≤ P (P1 ∩ Q2) := hrhs
    _ ≤ _ := measure_mono hsub

end Main

end ElboimSly.Brownian
