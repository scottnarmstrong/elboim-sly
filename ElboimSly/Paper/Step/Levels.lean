/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Frozen.Defs.AdmitsBMCoupling
public import ElboimSly.Frozen.Defs.IndFailBound
public import ElboimSly.Frozen.Defs.IndThetaH
public import ElboimSly.Paper.Step.Regime
public import Mathlib

/-!
# Levels of the step regime

Levels.

Under `StepRegime d n₁ β n t₀`:

* (a) `log₄ β - 1 < n`; and `n₁ ≤ n - 1` once `β ≥ 4^(n₁+2)` (`stepRegime_log_lt`,
  `stepRegime_level_le`);
* (b) every real `s` with `4^n₁ < s ≤ 4^n` has level `n(s) ∈ [n₁, n-1]`, `t₀(s) ∈ (1,4]`,
  `s = t_{n(s)}(t₀(s))`, `n(s) ≥ log₄ s - 1`, `H(β, n(s), t₀(s))`, and the consequences (H2)-(H4) at
  scale `s` (`stepRegime_level`);
* (c) (H2) on `[1, 4^n]` when `β ≥ 4^(n₁+2)` (`stepRegime_H2_pow`);
* (d) `1 ≤ σ ≤ 2` and `σ² ≤ 3` for every admissible `σ` when `β ≥ 12^16` (`step_sigma_bounds`);
* (e) the interval `[t_n^κ/2, 4^n]` satisfies the hypothesis of (b) when `β ≥ 4^((n₁+2)/κ)`
  (`stepRegime_interval`).
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal ENNReal

namespace ElboimSly.Paper

variable {d : ℕ} {β : ℝ} [Fact (0 < β)]

/-- (H2) at scale `s`: `ℙ(W(r) = x) ≤ r^{-d/2+0.1}` for all real `r ∈ [1, s]` and `x ∈ ℤ^d`,
for the regenerated walk of every Poisson environment sequence. -/
def StepH2 (d : ℕ) (β : ℝ) [Fact (0 < β)] (s : ℝ) : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (N : Ω → Measure (ℕ × RingSpace d β)),
    IsPoissonPointProcess N ((Measure.count : Measure ℕ).prod (ringIntensity d β)) P →
      ∀ r ∈ Icc (1 : ℝ) s, ∀ x : Fin d → ℤ,
        P {ω | regenWalk (fun k => copyEnv (N ω) k) r = x} ≤
          ENNReal.ofReal (r ^ (-(d : ℝ) / 2 + 1 / 10))

/-- (H3) at scale `s` with level `m`: `ℙ(sup_{r ≤ s} ‖W(r)‖ ≥ m² √s) ≤ e^{-m²}`. -/
def StepH3 (d : ℕ) (β : ℝ) [Fact (0 < β)] (s : ℝ) (m : ℕ) : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (N : Ω → Measure (ℕ × RingSpace d β)),
    IsPoissonPointProcess N ((Measure.count : Measure ℕ).prod (ringIntensity d β)) P →
      P {ω | ENNReal.ofReal ((m : ℝ) ^ 2 * Real.sqrt s) ≤
        ⨆ r : Set.Icc (0 : ℝ) s,
          ENNReal.ofReal ‖regenWalk (fun k => copyEnv (N ω) k) (r : ℝ)‖} ≤
        ENNReal.ofReal (Real.exp (-((m : ℝ) ^ 2)))

/-- (H4) at scale `s` with level `m`: a `(σ_s, s^{θ_H})`-coupling up to time `s` with failure
probability `e^{-m²}`, for some `σ_s` with `|σ_s - √2| ≤ max {3β^{-1/16} - s^{-1/16}, 0}`. -/
def StepH4 (d : ℕ) (β : ℝ) [Fact (0 < β)] (s : ℝ) (m : ℕ) : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (N : Ω → Measure (ℕ × RingSpace d β)),
    IsPoissonPointProcess N ((Measure.count : Measure ℕ).prod (ringIntensity d β)) P →
      ∃ σ : ℝ, |σ - Real.sqrt 2| ≤ max (3 * β ^ (-(1 : ℝ) / 16) - s ^ (-(1 : ℝ) / 16)) 0 ∧
        AdmitsBMCoupling d s.toNNReal
          (P.map (fun ω (t : Set.Icc (0 : ℝ≥0) s.toNNReal) =>
            regenWalk (fun k => copyEnv (N ω) k) ((t : ℝ≥0) : ℝ)))
          σ (s ^ indThetaH) (Real.exp (-((m : ℝ) ^ 2)))

/-! ### The level of a real number -/

theorem stepLevel_spec {s : ℝ} (hs : 1 < s) :
    (4 : ℝ) ^ stepLevel s < s ∧ s ≤ 4 ^ (stepLevel s + 1) := by
  have hl : 0 < Real.logb 4 s := Real.logb_pos (by norm_num) hs
  set c := ⌈Real.logb 4 s⌉₊ with hc
  have hc1 : 1 ≤ c := Nat.one_le_iff_ne_zero.2 (by
    intro h; rw [hc, Nat.ceil_eq_zero] at h; linarith)
  have hle : Real.logb 4 s ≤ c := Nat.le_ceil _
  have hlt : (c : ℝ) < Real.logb 4 s + 1 := Nat.ceil_lt_add_one hl.le
  have hm : stepLevel s + 1 = c := by unfold stepLevel; omega
  have hmr : ((stepLevel s : ℕ) : ℝ) + 1 = c := by exact_mod_cast hm
  constructor
  · have h : ((stepLevel s : ℕ) : ℝ) < Real.logb 4 s := by linarith
    have := (Real.lt_logb_iff_rpow_lt (by norm_num : (1 : ℝ) < 4) (by linarith)).1 h
    simpa [Real.rpow_natCast] using this
  · rw [hm]
    have := (Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ) < 4) (by linarith)).1 hle
    simpa [Real.rpow_natCast] using this

theorem stepScale0_mem {s : ℝ} (hs : 1 < s) : stepScale0 s ∈ Ioc (1 : ℝ) 4 := by
  obtain ⟨h1, h2⟩ := stepLevel_spec hs
  have hp : (0 : ℝ) < 4 ^ stepLevel s := by positivity
  unfold stepScale0
  refine ⟨(one_lt_div hp).2 h1, ?_⟩
  rw [div_le_iff₀ hp]
  calc s ≤ 4 ^ (stepLevel s + 1) := h2
    _ = 4 * 4 ^ stepLevel s := by ring

theorem indScale_stepScale0 {s : ℝ} : indScale (stepScale0 s) (stepLevel s) = s := by
  unfold indScale stepScale0
  have hp : (0 : ℝ) < 4 ^ stepLevel s := by positivity
  field_simp

theorem stepLevel_ge_logb {s : ℝ} (hs : 1 < s) : Real.logb 4 s - 1 ≤ stepLevel s := by
  have h2 := (stepLevel_spec hs).2
  have : Real.logb 4 s ≤ (stepLevel s + 1 : ℕ) := by
    rw [Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ) < 4) (by linarith),
      Real.rpow_natCast]
    exact h2
  push_cast at this
  linarith

/-! ### Part (a) -/

theorem stepRegime_log_lt {d n₁ : ℕ} {n : ℕ} {t₀ : ℝ} (h : StepRegime d n₁ β n t₀) :
    Real.logb 4 β - 1 < n := by
  obtain ⟨-, hβ1, -, ⟨-, h4⟩, hlt, -⟩ := h
  have hsc : indScale t₀ n ≤ 4 ^ (n + 1) := by
    unfold indScale; calc (4 : ℝ) ^ n * t₀ ≤ 4 ^ n * 4 := by gcongr
      _ = 4 ^ (n + 1) := by ring
  have : Real.logb 4 β < (n + 1 : ℕ) := by
    rw [Real.logb_lt_iff_lt_rpow (by norm_num : (1 : ℝ) < 4) (by linarith), Real.rpow_natCast]
    exact lt_of_lt_of_le hlt hsc
  push_cast at this
  linarith

theorem stepRegime_level_le {d n₁ : ℕ} {n : ℕ} {t₀ : ℝ} (h : StepRegime d n₁ β n t₀)
    (hβ : (4 : ℝ) ^ (n₁ + 2) ≤ β) : n₁ + 1 ≤ n := by
  obtain ⟨-, hβ1, -, ⟨-, h4⟩, hlt, -⟩ := h
  have hsc : indScale t₀ n ≤ 4 ^ (n + 1) := by
    unfold indScale; calc (4 : ℝ) ^ n * t₀ ≤ 4 ^ n * 4 := by gcongr
      _ = 4 ^ (n + 1) := by ring
  have : (4 : ℝ) ^ (n₁ + 2) < 4 ^ (n + 1) := lt_of_le_of_lt hβ (lt_of_lt_of_le hlt hsc)
  have := (pow_lt_pow_iff_right₀ (by norm_num : (1 : ℝ) < 4)).1 this
  omega

/-! ### Part (b) -/

theorem stepRegime_level {d n₁ : ℕ} {n : ℕ} {t₀ : ℝ} (h : StepRegime d n₁ β n t₀) {s : ℝ}
    (hs1 : (4 : ℝ) ^ n₁ < s) (hs2 : s ≤ 4 ^ n) :
    n₁ ≤ stepLevel s ∧ stepLevel s ≤ n - 1 ∧ stepScale0 s ∈ Ioc (1 : ℝ) 4 ∧
      s = indScale (stepScale0 s) (stepLevel s) ∧ Real.logb 4 s - 1 ≤ stepLevel s ∧
      IndHyp d β (stepLevel s) (stepScale0 s) ∧
      StepH2 d β s ∧ StepH3 d β s (stepLevel s) ∧ StepH4 d β s (stepLevel s) := by
  have hs : 1 < s := lt_of_le_of_lt (one_le_pow₀ (by norm_num)) hs1
  obtain ⟨h1, h2⟩ := stepLevel_spec hs
  have hn1 : n₁ < stepLevel s + 1 := by
    have : (4 : ℝ) ^ n₁ < 4 ^ (stepLevel s + 1) := lt_of_lt_of_le hs1 h2
    exact (pow_lt_pow_iff_right₀ (by norm_num : (1 : ℝ) < 4)).1 this
  have hn2 : stepLevel s < n := by
    have : (4 : ℝ) ^ stepLevel s < 4 ^ n := lt_of_lt_of_le h1 hs2
    exact (pow_lt_pow_iff_right₀ (by norm_num : (1 : ℝ) < 4)).1 this
  have hI : IndHyp d β (stepLevel s) (stepScale0 s) :=
    h.2.2.2.2.2 _ (by omega) hn2 _ (stepScale0_mem hs)
  have hsc := indScale_stepScale0 (s := s)
  refine ⟨by omega, by omega, stepScale0_mem hs, hsc.symm, stepLevel_ge_logb hs, hI, ?_, ?_, ?_⟩
  · intro Ω _ P N hN r hr x
    have := (hI.1 Ω P N hN).2.1 r (by rwa [hsc]) x
    exact this
  · intro Ω _ P N hN
    have := (hI.1 Ω P N hN).2.2.1
    unfold IndH3 at this
    rw [hsc] at this
    refine this.trans (ENNReal.ofReal_le_ofReal ?_)
    unfold indFailBound
    split_ifs
    · apply Real.exp_le_exp.2
      have : ((stepLevel s : ℕ) : ℝ) ^ 2 ≤ ((stepLevel s : ℕ) : ℝ) ^ 3 := by
        rcases Nat.eq_zero_or_pos (stepLevel s) with h0 | h0
        · simp [h0]
        · have : (1 : ℝ) ≤ stepLevel s := by exact_mod_cast h0
          nlinarith [sq_nonneg (stepLevel s : ℝ)]
      linarith
    · exact le_rfl
  · intro Ω _ P N hN
    obtain ⟨σ, hσ, hC⟩ := (hI.1 Ω P N hN).2.2.2
    refine ⟨σ, ?_, ?_⟩
    · rw [hsc] at hσ; exact hσ
    · rw [hsc] at hC
      obtain ⟨Q, hQ1, hQ2, hQ3, hQ4⟩ := hC
      refine ⟨Q, hQ1, hQ2, hQ3, hQ4.trans (ENNReal.ofReal_le_ofReal ?_)⟩
      unfold indFailBound
      split_ifs
      · apply Real.exp_le_exp.2
        have : ((stepLevel s : ℕ) : ℝ) ^ 2 ≤ ((stepLevel s : ℕ) : ℝ) ^ 3 := by
          rcases Nat.eq_zero_or_pos (stepLevel s) with h0 | h0
          · simp [h0]
          · have : (1 : ℝ) ≤ stepLevel s := by exact_mod_cast h0
            nlinarith [sq_nonneg (stepLevel s : ℝ)]
        linarith
      · exact le_rfl

/-! ### Part (c) -/

theorem stepRegime_H2_pow {d n₁ : ℕ} {n : ℕ} {t₀ : ℝ} (h : StepRegime d n₁ β n t₀)
    (hβ : (4 : ℝ) ^ (n₁ + 2) ≤ β) : StepH2 d β (4 ^ n) := by
  have hn := stepRegime_level_le h hβ
  have hlt : (4 : ℝ) ^ n₁ < 4 ^ n :=
    pow_lt_pow_right₀ (by norm_num) (by omega)
  exact (stepRegime_level h hlt le_rfl).2.2.2.2.2.2.1

/-! ### Part (d) -/

omit [Fact (0 < β)] in
theorem step_sigma_bounds (hβ : (12 : ℝ) ^ 16 ≤ β) {s σ : ℝ} (hs : 0 < s)
    (hσ : |σ - Real.sqrt 2| ≤ max (3 * β ^ (-(1 : ℝ) / 16) - s ^ (-(1 : ℝ) / 16)) 0) :
    1 ≤ σ ∧ σ ≤ 2 ∧ σ ^ 2 ≤ 3 := by
  have hβ0 : 0 < β := lt_of_lt_of_le (by positivity) hβ
  have h12 : (12 : ℝ) ≤ β ^ ((1 : ℝ) / 16) := by
    have : (12 : ℝ) = ((12 : ℝ) ^ (16 : ℝ)) ^ ((1 : ℝ) / 16) := by
      rw [← Real.rpow_mul (by norm_num)]; norm_num
    rw [this]
    apply Real.rpow_le_rpow (by positivity) _ (by norm_num)
    simpa using hβ
  have hneg : β ^ (-(1 : ℝ) / 16) = (β ^ ((1 : ℝ) / 16))⁻¹ := by
    rw [← Real.rpow_neg hβ0.le]; congr 1; ring
  have hb : β ^ (-(1 : ℝ) / 16) ≤ 1 / 12 := by
    rw [hneg, one_div]
    have := inv_anti₀ (by norm_num : (0 : ℝ) < 12) h12
    simpa using this
  have hsp : 0 < s ^ (-(1 : ℝ) / 16) := Real.rpow_pos_of_pos hs _
  have hmax : max (3 * β ^ (-(1 : ℝ) / 16) - s ^ (-(1 : ℝ) / 16)) 0 ≤ 1 / 4 := by
    apply max_le <;> linarith
  have habs := (hσ.trans hmax)
  have h2a : (1.41 : ℝ) < Real.sqrt 2 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  have h2b : Real.sqrt 2 < 1.42 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  rw [abs_le] at habs
  refine ⟨by linarith, by linarith, ?_⟩
  nlinarith

/-! ### Part (e) -/

theorem stepRegime_interval {d n₁ : ℕ} {n : ℕ} {t₀ : ℝ} (h : StepRegime d n₁ β n t₀) {κ : ℝ}
    (hκ : 0 < κ) (hβ : (4 : ℝ) ^ (((n₁ : ℝ) + 2) / κ) ≤ β) {s : ℝ}
    (hs : indScale t₀ n ^ κ / 2 ≤ s) : (4 : ℝ) ^ n₁ < s := by
  obtain ⟨-, hβ1, -, ⟨-, h4⟩, hlt, -⟩ := h
  have hβ0 : 0 < β := by linarith
  have h1 : (4 : ℝ) ^ ((n₁ : ℝ) + 2) ≤ β ^ κ := by
    calc (4 : ℝ) ^ ((n₁ : ℝ) + 2) = ((4 : ℝ) ^ (((n₁ : ℝ) + 2) / κ)) ^ κ := by
          rw [← Real.rpow_mul (by norm_num)]; congr 1; field_simp
      _ ≤ β ^ κ := Real.rpow_le_rpow (by positivity) hβ hκ.le
  have h2 : β ^ κ < indScale t₀ n ^ κ := Real.rpow_lt_rpow hβ0.le hlt hκ
  have h3 : (4 : ℝ) ^ ((n₁ : ℝ) + 2) = 16 * 4 ^ n₁ := by
    rw [Real.rpow_add (by norm_num), Real.rpow_natCast]; norm_num; ring
  have : (0 : ℝ) < 4 ^ n₁ := by positivity
  linarith

end ElboimSly.Paper
