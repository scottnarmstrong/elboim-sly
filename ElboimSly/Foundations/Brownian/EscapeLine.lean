/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Brownian.EscapeBoxProb
import Mathlib

/-!
# Escaping a box and a line of points

Escaping a box and a line of points.

The dimension is `n + 1` with `n ≥ 3`, and the sub-vector that drops the coordinate `i1`
(the written proof's "second coordinate") is indexed by `i1.succAbove : Fin n → Fin (n+1)`.
The coordinate `i0` is the written proof's first coordinate.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace ElboimSly.Brownian

/-- Escaping a box and a line of points. `q_* = q_box(d, 60)`. -/
noncomputable def qstar (d : ℕ) : ℝ := qbox d 60

/-- Escaping a box and a line of points.
`M₁ = max {2, (4/3) (2 C_hit(d-1)/q_*)^{1/(d-3)}}`. -/
noncomputable def lineM1 (d : ℕ) : ℝ :=
  max 2 (4 / 3 * (2 * Chit (d - 1) / qstar d) ^ (1 / ((d : ℝ) - 3)))

/-- Escaping a box and a line of points. `C_line = max {400, M₁ + 1}`. -/
noncomputable def Cline (d : ℕ) : ℝ := max 400 (lineM1 d + 1)

/-- Escaping a box and a line of points. `c_line(d) = c_tube(d, 3 M₁) q_*/2`. -/
noncomputable def cline (d : ℕ) : ℝ := ctube d (3 * lineM1 d) * qstar d / 2

/-- The time `T₁ = κ ρ` of stage 1, with `κ = M₁ a` and `ρ = a/3`. -/
noncomputable def lineT (d : ℕ) (a : ℝ) : ℝ≥0 := (lineM1 d * a * (a / 3)).toNNReal

/-- The target path of stage 1: `f(u) = (u/T₁) κ e_{i0}`. -/
noncomputable def lineF {n : ℕ} (i0 : Fin (n + 1)) (a : ℝ) (u : ℝ) : Fin (n + 1) → ℝ :=
  (u / lineT (n + 1) a * (lineM1 (n + 1) * a)) • e0 i0

/-- Escaping a box and a line of points. The path set `𝔏`. -/
def lineSet {n : ℕ} (i0 i1 : Fin (n + 1)) (σ a A : ℝ) : Set (PathSpace (n + 1)) :=
  {w | w ∈ tube2Set (n + 1) σ 0 (lineF i0 a) (a / 3) (lineT (n + 1) a) ∧
    (fun v => w (lineT (n + 1) a + v) - w (lineT (n + 1) a)) ∈ escapeBoxSet (n + 1) i0 σ 60 (A / 20) ∧
    ∀ M' : ℕ, ((2 * a / 3 : ℝ) : EReal) <
      ⨅ v ∈ denseSub (Set.Icc (0 : ℝ≥0) M'),
        ((‖fun k : Fin n => σ • w (lineT (n + 1) a + v) (i1.succAbove k)‖ : ℝ) : EReal)}

lemma lineM1_ge_two (d : ℕ) : 2 ≤ lineM1 d := le_max_left _ _

lemma Cline_ge (d : ℕ) : 400 ≤ Cline d ∧ lineM1 d + 1 ≤ Cline d :=
  ⟨le_max_left _ _, le_max_right _ _⟩

lemma lineT_coe {n : ℕ} {a : ℝ} (ha : 0 < a) :
    (lineT (n + 1) a : ℝ) = lineM1 (n + 1) * a * (a / 3) := by
  have := lineM1_ge_two (n + 1)
  rw [lineT, Real.coe_toNNReal _ (by positivity)]

lemma continuous_lineF {n : ℕ} (i0 : Fin (n + 1)) (a : ℝ) : Continuous (lineF i0 a) := by
  unfold lineF
  fun_prop

/-- Escaping a box and a line of points (b). -/
theorem lineSet_avoids {n : ℕ} (_hn : 3 ≤ n) {i0 i1 : Fin (n + 1)} (hne : i0 ≠ i1)
    {σ a A : ℝ} (hσ0 : 0 < σ) (ha : 0 < a) (hA : Cline (n + 1) * a ≤ A)
    {w : PathSpace (n + 1)} (hw : Continuous w) (hmem : w ∈ lineSet i0 i1 σ a A)
    {Q : Set (Fin (n + 1) → ℝ)}
    (hQ : Q ⊆ {y | y i0 ≤ -(A / 20)} ∩ Metric.closedBall 0 (2 * A)) (s : ℝ≥0) :
    σ • w s ∉ Q ∧ ((∃ i, i ≠ i1 ∧ 2 * a / 3 ≤ |σ * w s i|) ∨ |σ * w s i1| ≤ a / 3) := by
  obtain ⟨H1, H2, H3⟩ := hmem
  set T1 : ℝ≥0 := lineT (n + 1) a with hT1
  have hM1 := lineM1_ge_two (n + 1)
  obtain ⟨hC1, hC2⟩ := Cline_ge (n + 1)
  set M1 := lineM1 (n + 1) with hM1def
  have hT1R : (T1 : ℝ) = M1 * a * (a / 3) := lineT_coe ha
  have hT1pos : 0 < (T1 : ℝ) := by rw [hT1R]; positivity
  have hA400 : 400 * a ≤ A := by nlinarith
  have hAM : (M1 + 1) * a ≤ A := by nlinarith
  have hApos : 0 < A := by nlinarith
  have hfc : ContinuousOn (lineF i0 a) (Set.Icc (0 : ℝ) T1) := (continuous_lineF i0 a).continuousOn
  have hev := (mem_tube2Set_iff hw σ 0 (by positivity : 0 ≤ a / 3) hfc).1 H1
  have hT12 : (T1 / 2 : ℝ≥0) ≤ T1 := by
    rw [← NNReal.coe_le_coe]; push_cast; linarith
  have hend := hev.2 T1 hT12 le_rfl
  have hfT : lineF i0 a T1 = (M1 * a) • e0 i0 := by
    simp only [lineF]; rw [div_self hT1pos.ne', one_mul]
  rw [hfT] at hend
  have hM1a : 0 < M1 * a := mul_pos (by linarith) ha
  have hz0 : 0 ≤ (σ • w T1) i0 := by
    have h1 := norm_le_pi_norm (0 + σ • w T1 - (M1 * a) • e0 i0) i0
    have hc : (0 + σ • w T1 - (M1 * a) • e0 i0) i0 = σ * w T1 i0 - M1 * a := by
      simp [e0_apply_self]
    rw [hc, Real.norm_eq_abs] at h1
    have h2 := (abs_le.1 (h1.trans hend)).1
    simp only [Pi.smul_apply, smul_eq_mul]
    nlinarith
  by_cases hs : s ≤ T1
  · have h1 := hev.1 s hs
    have h2 := norm_le_pi_norm (0 + σ • w s - lineF i0 a s) i0
    have h3 := norm_le_pi_norm (0 + σ • w s - lineF i0 a s) i1
    have hd0 : (0 + σ • w s - lineF i0 a s) i0 =
        σ * w s i0 - (s : ℝ) / T1 * (M1 * a) := by
      simp [lineF, e0_apply_self]; rfl
    have hd1 : (0 + σ • w s - lineF i0 a s) i1 = σ * w s i1 := by
      simp [lineF, e0, hne.symm]
    refine ⟨fun hq => ?_, Or.inr ?_⟩
    · have hqy := (hQ hq).1
      simp only [Set.mem_ofPred_eq, Pi.smul_apply, smul_eq_mul] at hqy
      rw [hd0, Real.norm_eq_abs] at h2
      have h4 := (abs_le.1 (h2.trans h1)).1
      have : 0 ≤ (s : ℝ) / T1 * (M1 * a) := by positivity
      linarith
    · rw [hd1, Real.norm_eq_abs] at h3
      exact h3.trans h1
  · have hs' := not_le.1 hs
    -- after time `T₁`
    set w' : PathSpace (n + 1) := fun v => w (T1 + v) - w T1 with hw'
    have hw'c : Continuous w' := (hw.comp (continuous_const.add continuous_id)).sub continuous_const
    have hz : ‖σ • w T1‖ ≤ M1 * a + a / 15 := by
      calc ‖σ • w T1‖ = ‖(M1 * a) • e0 i0 + (0 + σ • w T1 - (M1 * a) • e0 i0)‖ := by
            congr 1; abel
        _ ≤ ‖(M1 * a) • e0 i0‖ + ‖0 + σ • w T1 - (M1 * a) • e0 i0‖ := norm_add_le _ _
        _ ≤ M1 * a + a / 3 / 5 := by
            rw [norm_smul, norm_e0, mul_one, Real.norm_eq_abs, abs_of_pos hM1a]
            exact add_le_add le_rfl hend
        _ = _ := by ring
    have hQ' : Q ⊆ {y | y i0 ≤ (σ • w T1) i0 - A / 20} ∩ Metric.closedBall (σ • w T1) (60 * (A / 20)) := by
      intro y hy
      obtain ⟨h1, h2⟩ := hQ hy
      refine ⟨?_, ?_⟩
      · simp only [Set.mem_ofPred_eq] at h1 ⊢; linarith
      · rw [Metric.mem_closedBall, dist_eq_norm] at h2 ⊢
        rw [sub_zero] at h2
        calc ‖y - σ • w T1‖ ≤ ‖y‖ + ‖σ • w T1‖ := norm_sub_le _ _
          _ ≤ 60 * (A / 20) := by nlinarith
    have hav := escapeBox_avoids hw'c (i0 := i0) hσ0 (by norm_num : (1 : ℝ) ≤ 60)
      (by positivity : 0 < A / 20) (lamBox_ge_four (n + 1)) H2 (σ • w T1) hQ' (s - T1)
    have e : σ • w T1 + σ • w' (s - T1) = σ • w s := by
      simp only [hw']; rw [add_tsub_cancel_of_le hs'.le, ← smul_add]; congr 1; abel
    rw [e] at hav
    refine ⟨hav, Or.inl ?_⟩
    -- the line condition
    have hc : Continuous fun v : ℝ≥0 => w (T1 + v) := hw.comp (continuous_const.add continuous_id)
    have hcont : Continuous fun v : ℝ≥0 => ‖fun k : Fin n => σ • w (T1 + v) (i1.succAbove k)‖ :=
      (continuous_pi fun k => ((continuous_apply (i1.succAbove k)).comp hc).const_smul σ).norm
    have hv : s - T1 ∈ Set.Icc (0 : ℝ≥0) ⌈((s - T1 : ℝ≥0) : ℝ)⌉₊ := by
      refine ⟨zero_le, ?_⟩
      rw [← NNReal.coe_le_coe]
      simpa using Nat.le_ceil (((s - T1 : ℝ≥0)) : ℝ)
    have key := H3 ⌈((s - T1 : ℝ≥0) : ℝ)⌉₊
    rw [← iInf_eq_denseSub (J := Set.Icc (0 : ℝ≥0) _) Set.ordConnected_Icc hcont] at key
    have h1 := key.trans_le (biInf_le _ hv)
    rw [add_tsub_cancel_of_le hs'.le] at h1
    have h2 := EReal.coe_lt_coe_iff.1 h1
    by_contra hcon
    push Not at hcon
    have hle : ‖fun k : Fin n => σ • w s (i1.succAbove k)‖ ≤ 2 * a / 3 := by
      rw [pi_norm_le_iff_of_nonneg (by positivity)]
      intro k
      rw [Real.norm_eq_abs]
      exact (hcon _ (Fin.succAbove_ne i1 k)).le
    linarith

end ElboimSly.Brownian
