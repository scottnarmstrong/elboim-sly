/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.StrongApprox.StrongMarkov1d
public import ElboimSly.Foundations.Brownian.Density
public import ElboimSly.Foundations.Brownian.Sup
public import Mathlib

/-!
# Tail of the exit time of Brownian motion from a symmetric interval

Exit times of Brownian motion from symmetric intervals (a) (Part II).

For a standard real Brownian motion `β` and `r > 0` let `τ = bmExit r β` be the exit time from
`(-r, r)`. We show `τ` is a stopping time of the natural filtration, and
`P(τ > 16 r² k) ≤ (2/5)^k`. (The written proof has the constant `e^{-0.9} ≈ 0.4066`; `2/5` is a slightly
cleaner and stronger constant, since `(2π)^{-1/2} < 0.399`.)
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace ElboimSly.StrongApprox

open ElboimSly.Brownian

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {β : ℝ≥0 → Ω → ℝ}

/-- The exit time of the path of `β` from `(-r, r)`. -/
noncomputable def bmExit (r : ℝ) (β : ℝ≥0 → Ω → ℝ) (ω : Ω) : ℝ≥0∞ :=
  exitTime r (fun t => β t ω)

lemma bmExit_stopping [IsProbabilityMeasure P] (hβ : IsStandardRealBM β P) (r : ℝ) (t : ℝ≥0) :
    MeasurableSet[realFiltration β t] {ω | bmExit r β ω ≤ t} := by
  have hproc : IsProcess β := isProcess_of_realBM hβ
  have : {ω | bmExit r β ω ≤ t} = {ω | ∃ s ≤ t, r ≤ |β s ω|} := by
    ext ω; exact exitTime_le_iff (hproc.1 ω).1 t
  rw [this]
  exact measurableSet_exists_le_abs (m := realFiltration β t) (fun ω => (hproc.1 ω).1)
    (fun s hs => measurable_realFiltration hs) (measurable_const (a := r))

lemma measurable_bmExit [IsProbabilityMeasure P] (hβ : IsStandardRealBM β P) (r : ℝ) :
    Measurable (bmExit r β) :=
  measurable_procExit (isProcess_of_realBM hβ) measurable_const

lemma real_ball_bound {r : ℝ} (hr : 0 < r) {h : ℝ} (hh : h = 16 * r ^ 2) :
    (2 * (2 * r)) ^ 1 * (2 * Real.pi * (1 ^ 2 * h)) ^ (-((1 : ℕ) : ℝ) / 2) ≤ 2 / 5 := by
  have hpi : (3.14 : ℝ) < Real.pi := Real.pi_gt_d2
  have hx : 0 < 2 * Real.pi * (1 ^ 2 * h) := by rw [hh]; positivity
  have e1 : (2 * Real.pi * (1 ^ 2 * h)) ^ (-((1 : ℕ) : ℝ) / 2) =
      (Real.sqrt (2 * Real.pi * (1 ^ 2 * h)))⁻¹ := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hx.le]
    congr 1; push_cast; ring
  have e2 : Real.sqrt (2 * Real.pi * (1 ^ 2 * h)) = 4 * r * Real.sqrt (2 * Real.pi) := by
    rw [hh, show 2 * Real.pi * (1 ^ 2 * (16 * r ^ 2)) = (4 * r) ^ 2 * (2 * Real.pi) by ring,
      Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  have e3 : (5 / 2 : ℝ) ≤ Real.sqrt (2 * Real.pi) := by
    apply Real.le_sqrt_of_sq_le; nlinarith
  rw [e1, e2, pow_one]
  have hs : 0 < Real.sqrt (2 * Real.pi) := by positivity
  rw [show 2 * (2 * r) * (4 * r * Real.sqrt (2 * Real.pi))⁻¹ = (Real.sqrt (2 * Real.pi))⁻¹ by
    field_simp; norm_num]
  rw [inv_le_comm₀ hs (by norm_num)]
  linarith

/-- `P(|β(t+h) - β(t)| ≤ 2r) ≤ 2/5` for `h = 16 r²`. -/
lemma gaussian_small_increment [IsProbabilityMeasure P] (hβ : IsStandardRealBM β P)
    {r : ℝ} (hr : 0 < r) (t : ℝ≥0) :
    P {ω | |β (t + (16 * r ^ 2).toNNReal) ω - β t ω| ≤ 2 * r} ≤ 2 / 5 := by
  set h : ℝ≥0 := (16 * r ^ 2).toNNReal with hh
  have hhR : (h : ℝ) = 16 * r ^ 2 := Real.coe_toNNReal _ (by positivity)
  have hh0 : h ≠ 0 := by
    intro h0
    have : (h : ℝ) = 0 := by rw [h0]; rfl
    rw [hhR] at this; nlinarith
  have hs := hβ.shift t
  have key := IsStandardBrownianMotion.measure_closedBall_le hs hh0 0 0 (σ := 1) one_pos
    (r := 2 * r) (by positivity)
  have e : {ω | |β (t + h) ω - β t ω| ≤ 2 * r} =
      {ω | ‖(0 : Fin 1 → ℝ) + (1 : ℝ) • toVec1 (fun u ω => β (t + u) ω - β t ω) h ω - 0‖
        ≤ 2 * r} := by
    ext ω
    simp only [Set.mem_ofPred_eq, one_smul, zero_add, sub_zero]
    rw [norm_toVec1]
  rw [e]
  refine key.trans ?_
  have hreal := real_ball_bound hr hhR
  calc _ ≤ ENNReal.ofReal (2 / 5) := ENNReal.ofReal_le_ofReal hreal
    _ = 2 / 5 := by
      rw [ENNReal.ofReal_div_of_pos (by norm_num)]; simp

lemma tail_step [IsProbabilityMeasure P] (hβ : IsStandardRealBM β P) {r : ℝ} (hr : 0 < r)
    (t : ℝ≥0) :
    P {ω | ((t + (16 * r ^ 2).toNNReal : ℝ≥0) : ℝ≥0∞) < bmExit r β ω} ≤
      (2 / 5) * P {ω | (t : ℝ≥0∞) < bmExit r β ω} := by
  set h : ℝ≥0 := (16 * r ^ 2).toNNReal with hh
  have hproc : IsProcess β := isProcess_of_realBM hβ
  have hth : t ≤ t + h := le_self_add
  set E1 : Set Ω := {ω | (t : ℝ≥0∞) < bmExit r β ω} with hE1
  set E2 : Set Ω := {ω | |β (t + h) ω - β t ω| ≤ 2 * r} with hE2
  have hsub : {ω | ((t + h : ℝ≥0) : ℝ≥0∞) < bmExit r β ω} ⊆ E1 ∩ E2 := by
    intro ω hω
    have h1 : (t : ℝ≥0∞) < bmExit r β ω := lt_of_le_of_lt (by exact_mod_cast hth) hω
    refine ⟨h1, ?_⟩
    have a1 := lt_of_lt_exitTime (ρ := r) (w := fun s => β s ω) hω
    have a2 := lt_of_lt_exitTime (ρ := r) (w := fun s => β s ω) h1
    show |β (t + h) ω - β t ω| ≤ 2 * r
    calc |β (t + h) ω - β t ω| ≤ |β (t + h) ω| + |β t ω| := abs_sub _ _
      _ ≤ 2 * r := by linarith
  have hind := hβ.indep_increment hth
  have hE1m : MeasurableSet[realFiltration β t] E1 := by
    have : E1 = {ω | bmExit r β ω ≤ t}ᶜ := by
      ext ω; simp [hE1, not_le]
    rw [this]; exact (bmExit_stopping hβ r t).compl
  have hE2m : MeasurableSet[MeasurableSpace.comap (fun ω => β (t + h) ω - β t ω) inferInstance]
      E2 := by
    refine ⟨{x : ℝ | |x| ≤ 2 * r}, ?_, rfl⟩
    exact measurableSet_le measurable_id.abs measurable_const
  have hmul := (Indep_iff _ _ _).1 hind E2 E1 hE2m hE1m
  calc P {ω | ((t + h : ℝ≥0) : ℝ≥0∞) < bmExit r β ω} ≤ P (E2 ∩ E1) :=
        measure_mono (fun ω hω => ⟨(hsub hω).2, (hsub hω).1⟩)
    _ = P E2 * P E1 := hmul
    _ ≤ (2 / 5) * P E1 := by
        gcongr
        exact gaussian_small_increment hβ hr t

lemma tail_pow [IsProbabilityMeasure P] (hβ : IsStandardRealBM β P) {r : ℝ} (hr : 0 < r)
    (k : ℕ) :
    P {ω | (((k : ℝ≥0) * (16 * r ^ 2).toNNReal : ℝ≥0) : ℝ≥0∞) < bmExit r β ω} ≤ (2 / 5) ^ k := by
  induction k with
  | zero => simpa using prob_le_one
  | succ k ih =>
    have := tail_step hβ hr ((k : ℝ≥0) * (16 * r ^ 2).toNNReal)
    have e : ((k + 1 : ℕ) : ℝ≥0) * (16 * r ^ 2).toNNReal =
        (k : ℝ≥0) * (16 * r ^ 2).toNNReal + (16 * r ^ 2).toNNReal := by
      push_cast; ring
    rw [e]
    calc _ ≤ (2 / 5) * P {ω | (((k : ℝ≥0) * (16 * r ^ 2).toNNReal : ℝ≥0) : ℝ≥0∞) <
          bmExit r β ω} := this
      _ ≤ (2 / 5) * (2 / 5) ^ k := by gcongr
      _ = (2 / 5) ^ (k + 1) := by ring

lemma bmExit_lt_top_ae [IsProbabilityMeasure P] (hβ : IsStandardRealBM β P) {r : ℝ}
    (hr : 0 < r) : ∀ᵐ ω ∂P, bmExit r β ω < ⊤ := by
  rw [ae_iff]
  have hz : P {ω | ¬ bmExit r β ω < ⊤} = 0 := by
    have hle : ∀ k : ℕ, P {ω | ¬ bmExit r β ω < ⊤} ≤ (2 / 5) ^ k := fun k =>
      (measure_mono (fun ω hω => by
        have : bmExit r β ω = ⊤ := by simpa using hω
        show (((k : ℝ≥0) * (16 * r ^ 2).toNNReal : ℝ≥0) : ℝ≥0∞) < bmExit r β ω
        rw [this]; exact ENNReal.coe_lt_top)).trans (tail_pow hβ hr k)
    refine le_antisymm ?_ bot_le
    refine ge_of_tendsto' (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (by
      rw [show (2 / 5 : ℝ≥0∞) = ENNReal.ofReal (2 / 5) by
        rw [ENNReal.ofReal_div_of_pos (by norm_num)]; simp]
      exact ENNReal.ofReal_lt_one.2 (by norm_num))) fun k => hle k
  exact hz

end ElboimSly.StrongApprox
