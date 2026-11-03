/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Step.TransChain
public import ElboimSly.Paper.Step.TransNum
public import ElboimSly.Paper.Step.TransCoupling
public import ElboimSly.Paper.Step.Lemma76Stmt
public import ElboimSly.Paper.Step.Levels
public import Mathlib

/-!
# Lemma 7.7 (transition probabilities), conditional on Corollary 7.2 and Lemma 7.6

ES22 Lemma 7.7 (§7).

`StepTp d βTp` is the conclusion of Lemma 7.7: for `β ≥ βTp n₁`, `SR(n₁; β, n, t₀)`,
real `t ∈ [t_n/4, t_n]` and `u ∈ ℤ^d`: `ℙ(W(t) = u) ≤ t^{-d/2+0.1}`.

`step_lemma77_of_cor72_bm` proves it **assuming `StepCor72`** (the conclusion of Corollary 7.2) and
**`StepBm`** (the conclusion of Lemma 7.6); a conditional helper under a distinct name. The proof is
the written proof's: the natural coupling with lengths `(s₁, r) = (t - t^{2θ_H}, t^{2θ_H})`,
(H3) and (H2) at level `n(r)` for the second walk, and the Brownian coupling of Lemma 7.6 and
Density bounds for the first.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology ElboimSly.Cyclic ElboimSly.SRW
open scoped NNReal ENNReal

namespace ElboimSly.Paper.Step

open ElboimSly.Paper

/-- The conclusion of Lemma 7.7 (ES22 Lemma 7.7), with threshold `β_tp(n₁) = βTp n₁`. -/
def StepTp (d : ℕ) (βTp : ℕ → ℝ) : Prop :=
  ∀ n₁ : ℕ, 8 * d ≤ n₁ → ∀ (β : ℝ) [Fact (0 < β)] (n : ℕ) (t₀ : ℝ), βTp n₁ ≤ β →
    StepRegime d n₁ β n t₀ →
    ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (N : Ω → Measure (ℕ × RingSpace d β)),
      IsPoissonPointProcess N ((Measure.count : Measure ℕ).prod (ringIntensity d β)) P →
      ∀ t : ℝ, indScale t₀ n / 4 ≤ t → t ≤ indScale t₀ n → ∀ u : Fin d → ℤ,
        P {ω | regenWalk (fun k => copyEnv (N ω) k) t = u} ≤
          ENNReal.ofReal (t ^ (-(d : ℝ) / 2 + 1 / 10))

variable {d : ℕ}

/-- Facts about the length `r = t^{2θ_H}` of the second walk. -/
theorem trans_r_facts {n : ℕ} {t tn : ℝ} (hn : 100 ≤ n) (h1 : (4 : ℝ) ^ n < tn)
    (h2 : tn ≤ 4 ^ (n + 1)) (h3 : tn / 4 ≤ t) (h4 : t ≤ tn) :
    Real.sqrt tn / 2 ≤ t ^ ((41 : ℝ) / 50) ∧ 1 ≤ t ^ ((41 : ℝ) / 50) ∧
      t ^ ((41 : ℝ) / 50) ≤ 4 ^ n ∧
      tn ^ indThetaH ≤ (n : ℝ) ^ 2 * Real.sqrt (t ^ ((41 : ℝ) / 50)) ∧
      4 / 5 * (n : ℝ) + 1 ≤ Real.logb 4 (t ^ ((41 : ℝ) / 50)) := by
  have hn' : (100 : ℝ) ≤ n := by exact_mod_cast hn
  have h4n : (4 : ℝ) ^ 100 ≤ 4 ^ n := pow_le_pow_right₀ (by norm_num) hn
  have ht1 : 1 ≤ t := by linarith
  have ht0 : 0 < t := by linarith
  have htn0 : 0 < tn := by linarith
  set r := t ^ ((41 : ℝ) / 50) with hr
  have hr1 : 1 ≤ r := Real.one_le_rpow ht1 (by norm_num)
  have hr0 : 0 < r := by linarith
  refine ⟨?_, hr1, ?_, ?_, ?_⟩
  · have hr2 : r ^ 2 = t ^ ((41 : ℝ) / 25) := by
      rw [hr, ← Real.rpow_natCast, ← Real.rpow_mul ht0.le]; norm_num
    have : tn ≤ (2 * r) ^ 2 := by
      calc tn ≤ 4 * t := by linarith
        _ = 4 * t ^ (1 : ℝ) := by rw [Real.rpow_one]
        _ ≤ 4 * t ^ ((41 : ℝ) / 25) := by
            have := Real.rpow_le_rpow_of_exponent_le ht1 (show (1 : ℝ) ≤ 41 / 25 by norm_num)
            linarith
        _ = (2 * r) ^ 2 := by rw [mul_pow, hr2]; ring
    have h5 : Real.sqrt tn ≤ 2 * r := Real.sqrt_le_iff.2 ⟨by positivity, this⟩
    linarith
  · have h50 : r ^ 50 = t ^ 41 := by
      rw [hr, ← Real.rpow_natCast, ← Real.rpow_mul ht0.le]; norm_num
    have : r ^ 50 ≤ (4 ^ n) ^ 50 := by
      rw [h50, ← pow_mul]
      calc t ^ 41 ≤ (4 ^ (n + 1)) ^ 41 := pow_le_pow_left₀ ht0.le (h4.trans h2) 41
        _ = 4 ^ ((n + 1) * 41) := by rw [← pow_mul]
        _ ≤ 4 ^ (n * 50) := pow_le_pow_right₀ (by norm_num) (by omega)
    exact (pow_le_pow_iff_left₀ hr0.le (by positivity) (by norm_num)).1 this
  · have hsq : Real.sqrt r = t ^ ((41 : ℝ) / 100) := by
      rw [Real.sqrt_eq_rpow, hr, ← Real.rpow_mul ht0.le]; norm_num
    rw [hsq]
    have hθ : indThetaH = (41 : ℝ) / 100 := by unfold indThetaH; norm_num
    rw [hθ]
    calc tn ^ ((41 : ℝ) / 100) ≤ (4 * t) ^ ((41 : ℝ) / 100) :=
          Real.rpow_le_rpow htn0.le (by linarith) (by norm_num)
      _ = 4 ^ ((41 : ℝ) / 100) * t ^ ((41 : ℝ) / 100) := Real.mul_rpow (by norm_num) ht0.le
      _ ≤ (n : ℝ) ^ 2 * t ^ ((41 : ℝ) / 100) := by
          gcongr
          calc (4 : ℝ) ^ ((41 : ℝ) / 100) ≤ 4 ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
            _ = 4 := Real.rpow_one 4
            _ ≤ (n : ℝ) ^ 2 := by nlinarith
  · rw [hr, Real.logb_rpow_eq_mul_logb_of_pos ht0]
    have hlt : (n : ℝ) - 1 ≤ Real.logb 4 t := by
      rw [Real.le_logb_iff_rpow_le (by norm_num) ht0, Real.rpow_sub (by norm_num),
        Real.rpow_natCast, Real.rpow_one]
      linarith
    nlinarith

/-- **Lemma 7.7**, conditional on `StepCor72` (the conclusion of Corollary 7.2) and `StepBm` (the
conclusion of Lemma 7.6). ES22 Lemma 7.7. -/
theorem step_lemma77_of_cor72_bm (hd : 1 ≤ d) {cCat : ℝ} (hc : 0 < cCat) {βCat : ℕ → ℝ}
    (hCor : StepCor72 d cCat βCat) {cBm : ℝ} (hcBm : 0 < cBm) {βBm : ℕ → ℝ}
    (hBm : StepBm d cBm βBm) : ∃ βTp : ℕ → ℝ, StepTp d βTp := by
  obtain ⟨N0, hN0⟩ := trans_numeric hd hc hcBm
  refine ⟨fun n₁ => max (βCat n₁) (max (βBm n₁) (max ((12 : ℝ) ^ 16)
    (max ((4 : ℝ) ^ (2 * (n₁ + 2))) ((4 : ℝ) ^ (max N0 100 + 1))))), ?_⟩
  intro n₁ hn₁ β _ n t₀ hβ hR Ω _ P N hN t ht1 ht2 u
  have hβ' : max (βCat n₁) (max (βBm n₁) (max ((12 : ℝ) ^ 16)
    (max ((4 : ℝ) ^ (2 * (n₁ + 2))) ((4 : ℝ) ^ (max N0 100 + 1))))) ≤ β := hβ
  simp only [max_le_iff] at hβ'
  obtain ⟨hβc, hβBm, hβ12, hβ4, hβN⟩ := hβ'
  obtain ⟨-, hβ1, hn1, ht0, htn_lt, -⟩ := id hR
  obtain ⟨htn_gt, htn_le⟩ := indScale_bounds (n := n) ht0
  have hnN : max N0 100 ≤ n := by
    have h1 : (4 : ℝ) ^ (max N0 100 + 1) < 4 ^ (n + 1) :=
      lt_of_le_of_lt hβN (lt_of_lt_of_le htn_lt htn_le)
    have := (pow_lt_pow_iff_right₀ (by norm_num : (1 : ℝ) < 4)).1 h1
    omega
  have hn0 : N0 ≤ n := le_trans (le_max_left _ _) hnN
  have hn100 : 100 ≤ n := le_trans (le_max_right _ _) hnN
  obtain ⟨hrsq, hr1, hr4n, hθρ, hlog⟩ := trans_r_facts hn100 htn_gt htn_le ht1 ht2
  have htn0 : 0 < indScale t₀ n := lt_trans (by positivity) htn_gt
  have ht_pos : 0 < t := by
    have : (0 : ℝ) < indScale t₀ n / 4 := by positivity
    linarith
  obtain ⟨r, hr⟩ : ∃ r, r = t ^ ((41 : ℝ) / 50) := ⟨_, rfl⟩
  rw [← hr] at hrsq hr1 hr4n hθρ hlog
  have hr0 : 0 < r := by linarith
  have h4r : (4 : ℝ) ^ n₁ < r := by
    refine stepRegime_interval hR (κ := 1 / 2) (by norm_num) ?_ (s := r) ?_
    · have : ((n₁ : ℝ) + 2) / (1 / 2) = ((2 * (n₁ + 2) : ℕ) : ℝ) := by push_cast; ring
      rw [this, Real.rpow_natCast]; exact hβ4
    · rw [← Real.sqrt_eq_rpow]; exact hrsq
  obtain ⟨-, hm2, -, -, hm5, -, -, hH3, -⟩ := stepRegime_level hR h4r hr4n
  have hH2 : StepH2 d β (4 ^ n) := by
    refine stepRegime_H2_pow hR ?_
    refine le_trans ?_ hβ4
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  have hq : ∀ x : Fin d → ℤ, P {ω | regenWalk (fun k => copyEnv (N ω) k) r = x} ≤
      ENNReal.ofReal (r ^ (-(d : ℝ) / 2 + 1 / 10)) := fun x =>
    hH2 Ω P N hN r ⟨hr1, hr4n⟩ x
  set ρ : ℝ := (n : ℝ) ^ 2 * Real.sqrt r with hρ
  set m : ℕ := stepLevel r with hm
  have hA2 : P {ω | ρ < ‖regenWalk (fun k => copyEnv (N ω) k) r‖} ≤
      ENNReal.ofReal (Real.exp (-((m : ℝ) ^ 2))) := by
    refine le_trans (measure_mono ?_) (hH3 Ω P N hN)
    intro ω hω
    have hmn : (m : ℝ) ^ 2 * Real.sqrt r ≤ ρ := by
      have : (m : ℝ) ≤ n := by exact_mod_cast (by omega : m ≤ n)
      have h0 : (0 : ℝ) ≤ m := by positivity
      have : (m : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 := pow_le_pow_left₀ h0 this 2
      rw [hρ]; gcongr
    have hlt : (m : ℝ) ^ 2 * Real.sqrt r ≤ ‖regenWalk (fun k => copyEnv (N ω) k) r‖ :=
      (hmn.trans (le_of_lt hω))
    refine le_trans (ENNReal.ofReal_le_ofReal hlt) ?_
    exact le_iSup (fun r' : Set.Icc (0 : ℝ) r =>
      ENNReal.ofReal ‖regenWalk (fun k => copyEnv (N ω) k) (r' : ℝ)‖) ⟨r, hr0.le, le_rfl⟩
  -- the coupling
  obtain ⟨σ, hσ, hC⟩ := hBm n₁ hn₁ β n t₀ hβBm hR Ω P N hN
  obtain ⟨hσ1, hσ2, -⟩ := step_sigma_bounds hβ12 htn0 hσ
  set s₁ : ℝ := t - r with hs₁
  have hrle : r ≤ t / 2 := by
    rw [hr]; exact rpow_le_half (by
      have h4n : (4 : ℝ) ^ 100 ≤ 4 ^ n := pow_le_pow_right₀ (by norm_num) hn100
      have : (4 : ℝ) ^ 100 / 4 ≤ indScale t₀ n / 4 := by linarith
      have : (64 : ℝ) ≤ 4 ^ 100 / 4 := by norm_num
      linarith)
  have hs1 : 0 < s₁ := by rw [hs₁]; linarith
  have hs₁t : s₁ ≤ indScale t₀ n := by rw [hs₁]; linarith
  have hε : 0 ≤ indScale t₀ n ^ indThetaH := Real.rpow_nonneg htn0.le _
  have hρ0 : 0 ≤ ρ := by rw [hρ]; positivity
  have hα : ∀ v : Fin d → ℤ, P {ω | ‖regenWalk (fun k => copyEnv (N ω) k) s₁ - v‖ ≤ ρ} ≤
      ENNReal.ofReal (Real.exp (-(cBm * (n : ℝ) ^ 3))) + ENNReal.ofReal ((2 * (ρ + indScale t₀ n ^ indThetaH)) ^ d *
        (2 * Real.pi * (σ ^ 2 * s₁)) ^ (-(d : ℝ) / 2)) := by
    intro v
    have h := coupling_ball_bound hN (by linarith) hε hC (s := s₁.toNNReal)
      (by
        refine (Real.toNNReal_le_toNNReal hs₁t) |> fun h => h)
      (by simpa using hs1) v hρ0
    have e : ((s₁.toNNReal : ℝ≥0) : ℝ) = s₁ := Real.coe_toNNReal _ hs1.le
    rw [e] at h
    exact h
  have hchain := trans_chain hCor hR hβc hN (s₁ := s₁) (r := r) (t := t) hs1 hr0
    (by rw [hs₁]; ring) ht2 hq ρ hA2 hα u
  have hm45 : 4 / 5 * (n : ℝ) ≤ (m : ℝ) := by linarith
  have hX := hN0 n hn0 (t := t) (tn := indScale t₀ n) (m := (m : ℝ)) (σ := σ) (r := r)
    (s₁ := s₁) (ρ := ρ) htn_gt htn_le ht1 ht2 hσ1 hm45 hr hs₁ hρ hθρ
  -- nonnegativity of the pieces
  have hK0 : 0 ≤ (2 * (2 * indScale t₀ n ^ (2 * heavyEps d)) + 1) ^ d := by
    have := Real.rpow_nonneg htn0.le (2 * heavyEps d)
    positivity
  have hD0 : 0 ≤ (2 * (ρ + indScale t₀ n ^ indThetaH)) ^ d *
      (2 * Real.pi * (σ ^ 2 * s₁)) ^ (-(d : ℝ) / 2) := by
    have := Real.rpow_nonneg htn0.le indThetaH
    have h2 : 0 ≤ 2 * Real.pi * (σ ^ 2 * s₁) := by positivity
    have := Real.rpow_nonneg h2 (-(d : ℝ) / 2)
    positivity
  have hr0' : 0 ≤ r ^ (-(d : ℝ) / 2 + 1 / 10) := Real.rpow_nonneg hr0.le _
  have e : ENNReal.ofReal (Real.exp (-(cCat * (n : ℝ) ^ 3)) +
      (2 * (2 * indScale t₀ n ^ (2 * heavyEps d)) + 1) ^ d *
      (Real.exp (-((m : ℝ) ^ 2)) + r ^ (-(d : ℝ) / 2 + 1 / 10) *
        (Real.exp (-(cBm * (n : ℝ) ^ 3)) + (2 * (ρ + indScale t₀ n ^ indThetaH)) ^ d *
          (2 * Real.pi * (σ ^ 2 * s₁)) ^ (-(d : ℝ) / 2)))) =
      ENNReal.ofReal (Real.exp (-(cCat * (n : ℝ) ^ 3))) +
        ENNReal.ofReal ((2 * (2 * indScale t₀ n ^ (2 * heavyEps d)) + 1) ^ d) *
          (ENNReal.ofReal (Real.exp (-((m : ℝ) ^ 2))) + ENNReal.ofReal (r ^ (-(d : ℝ) / 2 + 1 / 10)) *
            (ENNReal.ofReal (Real.exp (-(cBm * (n : ℝ) ^ 3))) +
              ENNReal.ofReal ((2 * (ρ + indScale t₀ n ^ indThetaH)) ^ d *
                (2 * Real.pi * (σ ^ 2 * s₁)) ^ (-(d : ℝ) / 2)))) := by
    have p1 := Real.exp_pos (-((m : ℝ) ^ 2))
    have p2 := Real.exp_pos (-(cBm * (n : ℝ) ^ 3))
    have p3 := Real.exp_pos (-(cCat * (n : ℝ) ^ 3))
    rw [ENNReal.ofReal_add p3.le (by positivity), ENNReal.ofReal_mul hK0,
      ENNReal.ofReal_add p1.le (by positivity), ENNReal.ofReal_mul hr0',
      ENNReal.ofReal_add p2.le hD0]
  refine hchain.trans ?_
  rw [← e]
  exact ENNReal.ofReal_le_ofReal hX

end ElboimSly.Paper.Step
