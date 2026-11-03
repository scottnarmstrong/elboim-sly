/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Escape.C56Adapted
public import ElboimSly.Paper.Escape.C56Shift
public import ElboimSly.Paper.Escape.RelaxedStopping
public import ElboimSly.Paper.Escape.SepFinal
public import Mathlib

/-!
# The times `ζ_i` of ES22 Claim 5.6 are stopping times

Phases, radii and events of Claim 5.6; First relaxed times are relaxed and are stopping times (c).  `escZt` is `ζ_i` as an `ℝ≥0`-valued
random time of the regenerated walk; it is a stopping time of `avoidFilt`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Escape

open ElboimSly.Cyclic ElboimSly.Paper ElboimSly.Brownian

variable {k : ℕ}

/-- The real extension of the walk `W`: `r ↦ W(r⁺)`. -/
noncomputable def escY {β : ℝ} [Fact (0 < β)] {Ω : Type} [MeasurableSpace Ω]
    (N : Ω → MeasureTheory.Measure (CycS ℕ (k + 2) β)) (ω : Ω) : ℝ → Fin (k + 2) → ℤ :=
  fun r => escW N ω r.toNNReal

theorem escY_eq_cpathReal {β : ℝ} [Fact (0 < β)] {Ω : Type} [MeasurableSpace Ω]
    (N : Ω → MeasureTheory.Measure (CycS ℕ (k + 2) β)) (ω : Ω) :
    escY N ω = cpathReal (escCPath N ω) := rfl

/-- `b_i ≤ a_{i+1}`. -/
theorem es56B_le_escPhaseA_succ {t : ℝ} (ht : 0 ≤ t) (m i : ℕ) :
    es56B t m i ≤ escPhaseA t m (i + 1) := by
  unfold es56B escPhaseA
  by_cases h1 : i + 1 ≤ m
  · rw [ite_eq_left (by omega), ite_eq_left h1]
    obtain ⟨k, hk⟩ : ∃ k, m - i = k + 1 := ⟨m - i - 1, by omega⟩
    have hk' : m - (i + 1) = k := by omega
    rw [hk, hk', pow_succ]
    have : (0 : ℝ) < 4 ^ k := by positivity
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_nonneg ht this.le]
  · by_cases h2 : i ≤ m
    · have him : i = m := by omega
      subst him
      rw [ite_eq_left le_rfl, ite_eq_right h1]
      simp only [Nat.sub_self, pow_zero, div_one]
      rw [show i + 1 - i = 1 by omega]; simp only [pow_one]
      linarith [mul_nonneg ht (show (0:ℝ) ≤ 1 by norm_num)]
    · rw [ite_eq_right h2, ite_eq_right h1]
      obtain ⟨k, hk⟩ : ∃ k, i - m = k := ⟨_, rfl⟩
      have hk' : i + 1 - m = k + 1 := by omega
      rw [hk, hk', pow_succ]
      have : (0 : ℝ) < 4 ^ k := by positivity
      have e1 : 3 / 10 * t / 4 ^ k = 3 / 10 * t / 4 ^ k := rfl
      have h3 : t / (2 * (4 ^ k * 4)) ≤ 3 / 10 * t / 4 ^ k := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [mul_nonneg ht this.le]
      linarith

/-- `ζ_i` as an `ℝ≥0`-valued random time. -/
noncomputable def escZt {β : ℝ} [Fact (0 < β)] {Ω : Type} [MeasurableSpace Ω]
    (N : Ω → MeasureTheory.Measure (CycS ℕ (k + 2) β)) (t : ℝ) (m i : ℕ) (ω : Ω) : ℝ≥0 :=
  (escZetaAux β (escY N ω) (escPhaseA t m) (es56B t m) i).toNNReal

theorem escPhaseA_nonneg {t : ℝ} (ht : 0 ≤ t) (m i : ℕ) : 0 ≤ escPhaseA t m i := by
  unfold escPhaseA
  split_ifs
  · positivity
  · have : t / (2 * 4 ^ (i - m)) ≤ t := by
      rw [div_le_iff₀ (by positivity)]
      have : (1 : ℝ) ≤ 4 ^ (i - m) := one_le_pow₀ (by norm_num)
      nlinarith
    linarith

theorem escY_zeta_nonneg (β : ℝ) (y : ℝ → Fin (k + 2) → ℤ) {t : ℝ} (ht : 0 ≤ t) (m i : ℕ) :
    0 ≤ escZeta β y t m i :=
  (escPhaseA_nonneg ht m i).trans (escZeta_mem β y ht m i).1

theorem coe_escZt {β : ℝ} [Fact (0 < β)] {Ω : Type} [MeasurableSpace Ω]
    (N : Ω → Measure (CycS ℕ (k + 2) β)) {t : ℝ} (ht : 0 ≤ t) (m i : ℕ) (ω : Ω) :
    ((escZt N t m i ω : ℝ≥0) : ℝ) = escZeta β (escY N ω) t m i := by
  unfold escZt
  exact Real.coe_toNNReal _ (escY_zeta_nonneg β _ ht m i)

variable {β : ℝ} [Fact (0 < β)] {n₀ n : ℕ} {t₀ : ℝ}
  {Ω : Type} {𝒢₀ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {Pr : Measure Ω}
  {N N' : Ω → Measure (CycS ℕ (k + 2) β)}

/-- First relaxed times are relaxed and are stopping times (c) for `ζ_i`: the times `ζ_i` are `avoidFilt`-stopping
times. -/
theorem isStoppingTime_escZt (S : Es4Setting (k + 2) β n₀ n t₀ 𝒢₀ Pr N N') {t : ℝ} (ht : 0 ≤ t)
    (m : ℕ) : ∀ i : ℕ, IsStoppingTime (avoidFilt 𝒢₀ S.space)
      (fun ω => ((escZt N t m i ω : ℝ≥0) : WithTop ℝ≥0)) := by
  have hβ : 0 < β := Fact.out
  intro i
  induction i with
  | zero =>
    have := isStoppingTime_escZetaStep hβ (avoidFilt 𝒢₀ S.space) (escCPath N)
      (fun s => escW_adapted S s) (fun _ => 0) (isStoppingTime_const _ 0)
      (lo := escPhaseA t m 0) (hi := es56B t m 0) (escPhaseA_nonneg ht m 0)
      (escA_le_B t ht m 0) (fun ω => by simpa using escPhaseA_nonneg ht m 0)
    convert this using 2 with ω
    simp only [escZt, escZetaAux, escY_eq_cpathReal]
    rfl
  | succ i ih =>
    have := isStoppingTime_escZetaStep hβ (avoidFilt 𝒢₀ S.space) (escCPath N)
      (fun s => escW_adapted S s) (fun ω => escZt N t m i ω) ih
      (lo := escPhaseA t m (i + 1)) (hi := es56B t m (i + 1)) (escPhaseA_nonneg ht m _)
      (escA_le_B t ht m (i + 1)) (fun ω => by
        rw [coe_escZt N ht]
        exact (escZeta_mem β (escY N ω) ht m i).2.trans (es56B_le_escPhaseA_succ ht m i))
    convert this using 2 with ω
    simp only [escZt, escZetaAux, escY_eq_cpathReal]
    have h : 0 ≤ escZetaAux β (cpathReal (escCPath N ω)) (escPhaseA t m) (es56B t m) i :=
      escY_zeta_nonneg β (cpathReal (escCPath N ω)) ht m i
    rw [Real.coe_toNNReal _ h]

end ElboimSly.Paper.Escape

end
