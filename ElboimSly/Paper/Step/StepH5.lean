/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Step.H5Cov
public import ElboimSly.Paper.Step.StepH234
public import ElboimSly.Paper.Step.Lemma78Stmt
public import ElboimSly.Frozen.Defs.IndH5
public import Mathlib

/-!
# (H5) at level `n` from Lemma 7.8

(H5) at level n (ES22 §7), from ES22 Lemma 7.8 (`StepPp`), covariance of trajectories,
Invariance in law and the periodicity restriction, restart, periodicity (c).

The event of (H5) for `(u₁, u₂, q₁, q₂)` is carried, for good `ν`, to the event for
`(0, u₂ - u₁, 0, q)` of the shifted environment `stepShiftEnv u₁ r ν`, where
`r = -q₁ + β·1{q₂ < q₁}` and `q = q₂ - q₁ + β·1{q₂ < q₁} ∈ [0, β]`. `step_H5_of_pp` is a
conditional helper (hypothesis `StepPp`, owned by Lemma 7.8).
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Step

open ElboimSly ElboimSly.Interchange ElboimSly.Paper

variable {d : ℕ} {β : ℝ} [Fact (0 < β)]

/-- The event of (H5) for one environment. -/
def stepH5Ev (n : ℕ) (t : ℝ) (ν : Measure (RingSpace d β)) (u₁ u₂ : Fin d → ℤ) (q₁ q₂ : ℝ) :
    Prop :=
  cycOmega ν u₁ u₂ q₁ q₂ t ∧
    ENNReal.ofReal ((39 / 10 : ℝ) ^ n) ≤
      volume {s₂ : ℝ | s₂ ∈ Set.Icc 0 t ∧ ∃ s₁ ∈ Set.Icc 0 t,
        ‖cycWalk ν u₁ q₁ s₁ - cycWalk ν u₂ q₂ s₂‖ ≤ (19 / 10 : ℝ) ^ n}

theorem stepH5Ev_shift {ν : Measure (RingSpace d β)} (hν : Good ν) (n : ℕ) (t : ℝ)
    (u₁ u₂ : Fin d → ℤ) (q₁ q₂ r : ℝ) :
    stepH5Ev n t ν u₁ u₂ q₁ q₂ ↔
      stepH5Ev n t (stepShiftEnv u₁ r ν) (u₁ - u₁) (u₂ - u₁) (q₁ + r) (q₂ + r) := by
  have hw : ∀ (u : Fin d → ℤ) (q s : ℝ), 0 ≤ s →
      cycWalk (stepShiftEnv u₁ r ν) (u - u₁) (q + r) s = cycWalk ν u q s - u₁ :=
    fun u q s hs => cycWalk_stepShiftEnv hν u₁ u r q hs
  have hβ0 : 0 < β := Fact.out
  have hmerge : cycMerges ν u₁ u₂ q₁ q₂ t ↔
      cycMerges (stepShiftEnv u₁ r ν) (u₁ - u₁) (u₂ - u₁) (q₁ + r) (q₂ + r) t := by
    unfold cycMerges
    constructor
    · rintro ⟨s₁, s₂, h1, h2, ⟨k, hk⟩, hw'⟩
      refine ⟨s₁, s₂, h1, h2, ⟨k, by linarith⟩, ?_⟩
      rw [hw _ _ _ h1.1, hw _ _ _ h2.1, hw']
    · rintro ⟨s₁, s₂, h1, h2, ⟨k, hk⟩, hw'⟩
      refine ⟨s₁, s₂, h1, h2, ⟨k, by linarith⟩, ?_⟩
      rw [hw _ _ _ h1.1, hw _ _ _ h2.1] at hw'
      exact sub_left_inj.1 hw'
  have hclose : ∀ (u : Fin d → ℤ) (q : ℝ), cycClosesBy ν u q t ↔
      cycClosesBy (stepShiftEnv u₁ r ν) (u - u₁) (q + r) t := by
    intro u q
    unfold cycClosesBy
    refine exists_congr fun k => and_congr Iff.rfl (and_congr Iff.rfl ?_)
    rw [hw _ _ _ (by positivity)]
    exact ⟨fun h => by rw [h], fun h => sub_left_inj.1 h⟩
  have hset : {s₂ : ℝ | s₂ ∈ Set.Icc 0 t ∧ ∃ s₁ ∈ Set.Icc 0 t,
        ‖cycWalk ν u₁ q₁ s₁ - cycWalk ν u₂ q₂ s₂‖ ≤ (19 / 10 : ℝ) ^ n} =
      {s₂ : ℝ | s₂ ∈ Set.Icc 0 t ∧ ∃ s₁ ∈ Set.Icc 0 t,
        ‖cycWalk (stepShiftEnv u₁ r ν) (u₁ - u₁) (q₁ + r) s₁ -
          cycWalk (stepShiftEnv u₁ r ν) (u₂ - u₁) (q₂ + r) s₂‖ ≤ (19 / 10 : ℝ) ^ n} := by
    ext s₂
    simp only [Set.mem_ofPred_eq]
    constructor
    · rintro ⟨h2, s₁, h1, hn⟩
      refine ⟨h2, s₁, h1, ?_⟩
      rw [hw _ _ _ h1.1, hw _ _ _ h2.1, sub_sub_sub_cancel_right]
      exact hn
    · rintro ⟨h2, s₁, h1, hn⟩
      refine ⟨h2, s₁, h1, ?_⟩
      rw [hw _ _ _ h1.1, hw _ _ _ h2.1, sub_sub_sub_cancel_right] at hn
      exact hn
  unfold stepH5Ev cycOmega
  rw [hmerge, hclose u₁ q₁, hclose u₂ q₂, hset]

/-- Periodicity of the cyclic start time (restriction, restart, periodicity (c)). -/
theorem stepH5Ev_period {ν : Measure (RingSpace d β)} (hν : Good ν) (n : ℕ) (t : ℝ)
    (u₁ u₂ : Fin d → ℤ) (q₁ q₂ : ℝ) :
    stepH5Ev n t ν u₁ u₂ (q₁ + β) q₂ ↔ stepH5Ev n t ν u₁ u₂ q₁ q₂ := by
  have hβ0 : 0 < β := Fact.out
  have hmerge : cycMerges ν u₁ u₂ (q₁ + β) q₂ t ↔ cycMerges ν u₁ u₂ q₁ q₂ t := by
    unfold cycMerges
    constructor
    · rintro ⟨s₁, s₂, h1, h2, ⟨k, hk⟩, hw'⟩
      refine ⟨s₁, s₂, h1, h2, ⟨k - 1, by push_cast; linarith⟩, ?_⟩
      rwa [cycWalk_period hν _ _ h1.1] at hw'
    · rintro ⟨s₁, s₂, h1, h2, ⟨k, hk⟩, hw'⟩
      refine ⟨s₁, s₂, h1, h2, ⟨k + 1, by push_cast; linarith⟩, ?_⟩
      rwa [cycWalk_period hν _ _ h1.1]
  have hclose : cycClosesBy ν u₁ (q₁ + β) t ↔ cycClosesBy ν u₁ q₁ t := by
    unfold cycClosesBy
    refine exists_congr fun k => and_congr Iff.rfl (and_congr Iff.rfl ?_)
    rw [cycWalk_period hν _ _ (by positivity)]
  have hset : {s₂ : ℝ | s₂ ∈ Set.Icc 0 t ∧ ∃ s₁ ∈ Set.Icc 0 t,
        ‖cycWalk ν u₁ (q₁ + β) s₁ - cycWalk ν u₂ q₂ s₂‖ ≤ (19 / 10 : ℝ) ^ n} =
      {s₂ : ℝ | s₂ ∈ Set.Icc 0 t ∧ ∃ s₁ ∈ Set.Icc 0 t,
        ‖cycWalk ν u₁ q₁ s₁ - cycWalk ν u₂ q₂ s₂‖ ≤ (19 / 10 : ℝ) ^ n} := by
    ext s₂
    simp only [Set.mem_ofPred_eq]
    constructor
    · rintro ⟨h2, s₁, h1, hn⟩
      exact ⟨h2, s₁, h1, by rwa [cycWalk_period hν _ _ h1.1] at hn⟩
    · rintro ⟨h2, s₁, h1, hn⟩
      exact ⟨h2, s₁, h1, by rwa [cycWalk_period hν _ _ h1.1]⟩
  unfold stepH5Ev cycOmega
  rw [hmerge, hclose, hset]

omit [Fact (0 < β)] in
/-- The `q`-parameter after the shift: `q₂ + r ∈ [0, β]` and `q₁ + r ∈ {0, β}`. -/
theorem stepH5_shift_params {q₁ q₂ : ℝ} (hq₁ : q₁ ∈ Set.Icc 0 β) (hq₂ : q₂ ∈ Set.Icc 0 β) :
    q₂ + (-q₁ + if q₂ < q₁ then β else 0) ∈ Set.Icc 0 β ∧
      (q₁ + (-q₁ + if q₂ < q₁ then β else 0) = 0 ∨
        q₁ + (-q₁ + if q₂ < q₁ then β else 0) = 0 + β) := by
  by_cases h : q₂ < q₁
  · simp only [h, ite_true]
    refine ⟨⟨by linarith [hq₁.2, hq₂.1], by linarith [hq₁.1]⟩, Or.inr (by ring)⟩
  · simp only [h, ite_false]
    refine ⟨⟨by linarith [not_lt.1 h], by linarith [hq₁.1, hq₂.2]⟩, Or.inl (by ring)⟩

/-- Corollary 7.8 ((H5) at level n): (H5) at level `n`, from Lemma 7.8 (`StepPp`). -/
theorem step_H5_of_pp {cPp : ℝ} {βPp : ℕ → ℝ} (hPp : StepPp d cPp βPp) {n₁ n : ℕ} {t₀ : ℝ}
    (hn₁ : 8 * d ≤ n₁) (hβ : βPp n₁ ≤ β) (h : StepRegime d n₁ β n t₀) (hn : 1 / cPp ≤ n)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (N : Ω → Measure (RingSpace d β))
    (hN : IsPoissonPointProcess N (ringIntensity d β) P) : IndH5 P N n t₀ := by
  intro u₁ u₂ q₁ q₂ hq₁ hq₂
  set r : ℝ := -q₁ + if q₂ < q₁ then β else 0 with hr
  obtain ⟨hqmem, hq1⟩ := stepH5_shift_params hq₁ hq₂
  have hN' := isPoissonPointProcess_stepShiftEnv hN u₁ r
  have key := hPp.2 n₁ hn₁ β n t₀ hβ h hn Ω P (fun ω => stepShiftEnv u₁ r (N ω)) hN' (u₂ - u₁)
    (q₂ + r) hqmem
  have hae : {ω | cycOmega (N ω) u₁ u₂ q₁ q₂ (indScaleReduced t₀ n) ∧
        ENNReal.ofReal ((39 / 10 : ℝ) ^ n) ≤
          volume {s₂ : ℝ | s₂ ∈ Set.Icc 0 (indScaleReduced t₀ n) ∧
            ∃ s₁ ∈ Set.Icc 0 (indScaleReduced t₀ n),
              ‖cycWalk (N ω) u₁ q₁ s₁ - cycWalk (N ω) u₂ q₂ s₂‖ ≤ (19 / 10 : ℝ) ^ n}} =ᵐ[P]
      {ω | cycOmega (stepShiftEnv u₁ r (N ω)) 0 (u₂ - u₁) 0 (q₂ + r) (indScaleReduced t₀ n) ∧
        ENNReal.ofReal ((39 / 10 : ℝ) ^ n) ≤
          volume {s₂ : ℝ | s₂ ∈ Set.Icc 0 (indScaleReduced t₀ n) ∧
            ∃ s₁ ∈ Set.Icc 0 (indScaleReduced t₀ n),
              ‖cycWalk (stepShiftEnv u₁ r (N ω)) 0 0 s₁ -
                cycWalk (stepShiftEnv u₁ r (N ω)) (u₂ - u₁) (q₂ + r) s₂‖ ≤ (19 / 10 : ℝ) ^ n}} := by
    filter_upwards [ae_good hN] with ω hω
    have e1 := stepH5Ev_shift hω n (indScaleReduced t₀ n) u₁ u₂ q₁ q₂ r
    have hg := good_stepShiftEnv hω u₁ r
    have e2 : stepH5Ev n (indScaleReduced t₀ n) (stepShiftEnv u₁ r (N ω)) 0 (u₂ - u₁) (q₁ + r)
        (q₂ + r) ↔ stepH5Ev n (indScaleReduced t₀ n) (stepShiftEnv u₁ r (N ω)) 0 (u₂ - u₁) 0
        (q₂ + r) := by
      rcases hq1 with h0 | h0
      · rw [h0]
      · rw [h0]; exact stepH5Ev_period hg n _ 0 _ 0 _
    rw [sub_self] at e1
    exact propext (e1.trans e2)
  rw [measure_congr hae]
  refine key.trans (ENNReal.ofReal_le_ofReal ?_)
  rw [step_pn_eq h]
  exact exp_neg_mul_cube_le hPp.1 hn

end ElboimSly.Paper.Step

end
