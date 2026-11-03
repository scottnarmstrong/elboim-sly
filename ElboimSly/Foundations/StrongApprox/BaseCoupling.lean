/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.StrongApprox.BaseCore
public import ElboimSly.Foundations.StrongApprox.BaseAsymp
public import ElboimSly.Foundations.SRW.SrwLaw
public import ElboimSly.Frozen.Theorems.PoissonKmtCoupling
public import Mathlib

/-!
# ES22 (8.3): the base coupling with precision `n^10`

ES22 (8.3): base coupling with precision n^10.

For `d ≥ 1` there is `n₁(d)` such that for every integer `n ≥ n₁` and every real `T ∈ [0, 4^{n+1}]`
there is a probability space carrying a Poisson point process `N'` with intensity `μ_d` and a
standard `d`-dimensional Brownian motion `B` with
`P'(sup_{t ≤ T} ‖X̃(t) - √2 B(t)‖ ≥ n^10) ≤ e^{-n^4}`, where `X̃` is the canonical walk of `N'`;
and `X̃` is an SRW (`IsSRW`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal

namespace ElboimSly
namespace StrongApprox

open SRW

theorem mul_exp_le (c : ℝ) (hc : 0 < c) (u v : ℝ) (h : Real.log c + u ≤ v) :
    c * Real.exp u ≤ Real.exp v := by
  calc c * Real.exp u = Real.exp (Real.log c) * Real.exp u := by rw [Real.exp_log hc]
    _ = Real.exp (Real.log c + u) := (Real.exp_add _ _).symm
    _ ≤ Real.exp v := Real.exp_le_exp.2 h

theorem four_pow_le_exp (m : ℕ) : (4 : ℝ) ^ m ≤ Real.exp (2 * m) := by
  have h4 : (4 : ℝ) ≤ Real.exp 2 := by
    have := Real.exp_one_gt_d9
    have h : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    nlinarith
  calc (4 : ℝ) ^ m ≤ (Real.exp 2) ^ m := pow_le_pow_left₀ (by norm_num) h4 m
    _ = Real.exp (2 * m) := by rw [← Real.exp_nat_mul]; ring_nf

theorem isRegularPath_canonical {Ω : Type*} {d : ℕ} (N : Ω → Measure (Dir d × ℝ)) (ω : Ω) :
    IsRegularPath (canonical d N ω) := by
  intro t
  obtain ⟨δ, hδ, h⟩ := exists_const_right (ν := N ω) (t : ℝ) t.2
  refine ⟨δ.toNNReal, Real.toNNReal_pos.2 hδ, fun s hts hst => ?_⟩
  have h1 : (t : ℝ) ≤ s := hts
  have h2 : (s : ℝ) < t + δ := by
    have : (s : ℝ) < (t + δ.toNNReal : ℝ≥0) := hst
    rwa [NNReal.coe_add, Real.coe_toNNReal _ hδ.le] at this
  exact h s ⟨h1, h2⟩

/-- The real inequalities (N1)-(N4), eventually in `n`. -/
theorem eventually_thresholds (d : ℕ) (_hd : 1 ≤ d) {C K lam : ℝ} (_hK : 0 < K) (hlam : 0 < lam) :
    ∀ᶠ n : ℕ in atTop, 1 ≤ n ∧
      C * ((n + 1) * Real.log 4) ≤ ((n : ℝ) ^ 10 / 5) / 2 ∧
      Real.log (6 * d * K) + (n : ℝ) ^ 4 ≤ lam * (((n : ℝ) ^ 10 / 5) / 2) ∧
      Real.log 6 + 2 * ((n : ℝ) + 1) + 4 * d * (Real.exp 1 - 1) + (n : ℝ) ^ 4 ≤
        (n : ℝ) ^ 10 / 5 ∧
      Real.log (12 * d) + 2 * ((n : ℝ) + 1) + (n : ℝ) ^ 4 ≤ ((n : ℝ) ^ 10 / 5) ^ 2 / 32 := by
  have h1 := eventually_poly_le (α := 1 / 10) (by norm_num) (C * Real.log 4) (C * Real.log 4)
  have h2 := eventually_poly_le (α := lam / 10) (by positivity) 0 (Real.log (6 * d * K))
  have h3 := eventually_poly_le (α := 1 / 5) (by norm_num) 2
    (Real.log 6 + 2 + 4 * d * (Real.exp 1 - 1))
  have h4 := eventually_poly_le (α := 1 / 800) (by norm_num) 2 (Real.log (12 * d) + 2)
  filter_upwards [h1, h2, h3, h4, eventually_ge_atTop 1] with n e1 e2 e3 e4 hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hp4 : (0 : ℝ) ≤ (n : ℝ) ^ 4 := by positivity
  have hp10 : (n : ℝ) ^ 10 ≤ ((n : ℝ) ^ 10) ^ 2 := by
    nlinarith [one_le_pow₀ (n := 10) hn1]
  refine ⟨hn, ?_, ?_, ?_, ?_⟩
  · nlinarith
  · nlinarith
  · nlinarith
  · nlinarith

/-- ES22 (8.3): base coupling with precision n^10 (ES22 (8.3)): the base coupling with precision `n^10`.
`X̃` is the canonical walk of `N'` (`SRW.canonical`), written out as `fun i => (walk d (N' ω) t i : ℝ)`.
The event `sup_{t ≤ T} ‖X̃(t) - √2 B(t)‖ ≥ n^10` is written with the supremum in `[0,∞]`. -/
theorem sa_base_coupling (d : ℕ) (hd : 1 ≤ d) :
    ∃ n₁ : ℕ, ∀ n : ℕ, n₁ ≤ n → ∀ T : ℝ, 0 ≤ T → T ≤ 4 ^ (n + 1) →
      ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (P' : Measure Ω') (N' : Ω' → Measure (Dir d × ℝ))
        (B : ℝ≥0 → Ω' → Fin d → ℝ),
        IsProbabilityMeasure P' ∧ IsPoissonPointProcess N' (clockIntensity (Dir d)) P' ∧
        IsStandardBrownianMotion d B P' ∧ IsSRW P' (canonical d N') ∧
        P' {ω | ENNReal.ofReal ((n : ℝ) ^ 10) ≤ ⨆ t : {t : ℝ≥0 // (t : ℝ) ≤ T},
            ENNReal.ofReal ‖(fun i => ((walk d (N' ω) (t : ℝ≥0) i : ℤ) : ℝ)) -
              √2 • B (t : ℝ≥0) ω‖} ≤ ENNReal.ofReal (Real.exp (-(n : ℝ) ^ 4)) := by
  obtain ⟨C, K, lam, hC, hK, hlam, hKMT⟩ := poisson_kmt_coupling
  obtain ⟨n₁, hn₁⟩ := eventually_atTop.1 (eventually_thresholds d hd (C := C) hK hlam)
  refine ⟨n₁, fun n hn T hT0 hT => ?_⟩
  obtain ⟨hn1, e1, e2, e3, e4⟩ := hn₁ n hn
  set a : ℝ := (n : ℝ) ^ 10 / 5 with ha_def
  have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have ha : 0 < a := by positivity
  -- the horizon
  set N : ℕ := max 1 ⌈T⌉₊ with hNdef
  have hN1 : 1 ≤ N := le_max_left _ _
  have hNle : N ≤ 4 ^ (n + 1) := by
    refine max_le (Nat.one_le_pow _ _ (by norm_num)) (Nat.ceil_le.2 ?_)
    exact_mod_cast hT
  have hNle' : (N : ℝ) ≤ 4 ^ (n + 1) := by exact_mod_cast hNle
  have hTN : T ≤ N := le_trans (Nat.le_ceil T) (by exact_mod_cast le_max_right _ _)
  obtain ⟨Q, hQprob, hQ1, hQ2, hQtail⟩ := hKMT N
  have := hQprob
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  have hlogN : Real.log N ≤ (n + 1) * Real.log 4 := by
    calc Real.log N ≤ Real.log ((4 : ℝ) ^ (n + 1)) := Real.log_le_log hNpos hNle'
      _ = (n + 1) * Real.log 4 := by rw [Real.log_pow]; push_cast; ring
  have hCa : C * Real.log N + a / 2 ≤ a := by
    have : C * Real.log N ≤ C * ((n + 1) * Real.log 4) := mul_le_mul_of_nonneg_left hlogN hC.le
    linarith
  obtain ⟨B, hB, hbound⟩ := base_core (d := d) (N := N) (μN := Q) hd hN1 hQ1 hQ2
    (C := C) (K := K) (lam := lam) hQtail ha hCa hT0 hTN
  refine ⟨OmBase d N, inferInstance, PBase d N Q, fun ω => Nproc d N ω.1, B, inferInstance,
    base_ppp hd hQ1, hB, ?_, ?_⟩
  · have hN := base_ppp hd hQ1
    refine ⟨measurable_canonical hN.measurable, fun ω => isRegularPath_canonical _ ω, ?_⟩
    exact ⟨OmBase d N, inferInstance, PBase d N Q, _, hN, rfl⟩
  · refine le_trans (measure_mono ?_) (hbound.trans ?_)
    · intro ω hω
      have h45 : ENNReal.ofReal (4 * a) < ENNReal.ofReal ((n : ℝ) ^ 10) := by
        rw [ENNReal.ofReal_lt_ofReal_iff (by positivity)]
        rw [ha_def]; nlinarith [pow_pos (by linarith : (0 : ℝ) < n) 10]
      obtain ⟨t, ht⟩ := lt_iSup_iff.1 (lt_of_lt_of_le h45 hω)
      refine ⟨t.1, t.2, ?_⟩
      have := (ENNReal.ofReal_lt_ofReal_iff'.1 ht).1
      exact this.le
    · -- the arithmetic
      have hcard : (Fintype.card (Dir d) : ℝ≥0∞) = ENNReal.ofReal (2 * d) := by
        rw [show (2 * d : ℝ) = ((2 * d : ℕ) : ℝ) by push_cast; ring, ENNReal.ofReal_natCast]
        simp [Fintype.card_prod]; ring
      have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
      have r2 : 2 * d * (K * Real.exp (-lam * (a / 2))) ≤ Real.exp (-(n : ℝ) ^ 4) / 3 := by
        have := mul_exp_le (6 * d * K) (by positivity) (-lam * (a / 2)) (-(n : ℝ) ^ 4)
          (by nlinarith)
        linarith
      have r3 : ((N : ℝ) / 1 + 1) * Real.exp (4 * d * 1 * (Real.exp 1 - 1) - a) ≤
          Real.exp (-(n : ℝ) ^ 4) / 3 := by
        have h4 := four_pow_le_exp (n + 1)
        have hN2 : (N : ℝ) / 1 + 1 ≤ 2 * Real.exp (2 * ((n + 1 : ℕ) : ℝ)) := by
          have : (1 : ℝ) ≤ 4 ^ (n + 1) := one_le_pow₀ (by norm_num)
          linarith
        have := mul_exp_le 6 (by norm_num)
          (2 * ((n : ℝ) + 1) + (4 * d * 1 * (Real.exp 1 - 1) - a)) (-(n : ℝ) ^ 4) (by nlinarith)
        calc ((N : ℝ) / 1 + 1) * Real.exp (4 * d * 1 * (Real.exp 1 - 1) - a)
            ≤ (2 * Real.exp (2 * ((n + 1 : ℕ) : ℝ))) *
              Real.exp (4 * d * 1 * (Real.exp 1 - 1) - a) :=
              mul_le_mul_of_nonneg_right hN2 (Real.exp_pos _).le
          _ = 2 * Real.exp (2 * ((n : ℝ) + 1) + (4 * d * 1 * (Real.exp 1 - 1) - a)) := by
              rw [mul_assoc, ← Real.exp_add]; push_cast; ring_nf
          _ ≤ Real.exp (-(n : ℝ) ^ 4) / 3 := by linarith
      have r4 : 4 * d * N * Real.exp (-a ^ 2 / (16 * √2 ^ 2 * 1)) ≤ Real.exp (-(n : ℝ) ^ 4) / 3 := by
        have h4 := four_pow_le_exp (n + 1)
        have hs : (√2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
        rw [hs]
        have := mul_exp_le (12 * d) (by positivity) (2 * ((n : ℝ) + 1) - a ^ 2 / 32) (-(n : ℝ) ^ 4)
          (by nlinarith)
        calc 4 * d * N * Real.exp (-a ^ 2 / (16 * 2 * 1))
            ≤ 4 * d * Real.exp (2 * ((n + 1 : ℕ) : ℝ)) * Real.exp (-a ^ 2 / (16 * 2 * 1)) := by
              gcongr; exact hNle'.trans h4
          _ = d * 4 * Real.exp (2 * ((n : ℝ) + 1) - a ^ 2 / 32) := by
              rw [mul_assoc, ← Real.exp_add]; push_cast; ring_nf
          _ ≤ Real.exp (-(n : ℝ) ^ 4) / 3 := by linarith
      have hexp : 0 < Real.exp (-(n : ℝ) ^ 4) := Real.exp_pos _
      calc _ = ENNReal.ofReal (2 * d * (K * Real.exp (-lam * (a / 2)))) +
            ENNReal.ofReal (((N : ℝ) / 1 + 1) * Real.exp (4 * d * 1 * (Real.exp 1 - 1) - a)) +
            ENNReal.ofReal (4 * d * N * Real.exp (-a ^ 2 / (16 * √2 ^ 2 * 1))) := by
            rw [hcard, ← ENNReal.ofReal_mul (by positivity)]
            congr 1
            rw [show (4 * d * N : ℝ≥0∞) = ENNReal.ofReal (4 * d * N) by
              rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]
              simp [ENNReal.ofReal_natCast], ← ENNReal.ofReal_mul (by positivity)]
        _ ≤ ENNReal.ofReal (Real.exp (-(n : ℝ) ^ 4) / 3) +
            ENNReal.ofReal (Real.exp (-(n : ℝ) ^ 4) / 3) +
            ENNReal.ofReal (Real.exp (-(n : ℝ) ^ 4) / 3) := by
            gcongr
        _ = ENNReal.ofReal (Real.exp (-(n : ℝ) ^ 4)) := by
            rw [← ENNReal.ofReal_add (by positivity) (by positivity),
              ← ENNReal.ofReal_add (by positivity) (by positivity)]
            congr 1; ring

end StrongApprox
end ElboimSly
