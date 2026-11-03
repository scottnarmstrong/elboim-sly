/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Step.TravelEngine
public import ElboimSly.Paper.Step.TravelBlocks
public import ElboimSly.Paper.Step.TravelEv
public import ElboimSly.Foundations.Cyclic.CycFar
public import Mathlib

/-!
# Lemma 7.3 (travelling far, conditional on Corollary 7.2)

ES22 Lemma 7.3 (§7).

`StepTf d cTf βTf` is the conclusion of Lemma 7.3: for `β ≥ βTf n₁`, `SR(n₁; β, n, t₀)` and all
real `t ∈ [√t_n, t_n]`, `ℙ(sup_{s ≤ t^{2/3}} ‖W(s)‖ ≥ t^{2/5}) ≤ e^{-cTf n³}`.

`step_lemma73_of_cor72` proves it **assuming `StepCor72`** (the conclusion of Corollary 7.2); it is
a conditional helper under a distinct name, not the source lemma. The proof is the written proof's:
the engine `step_travel_engine` with `k = ⌈t^{1/3}⌉` blocks of length `h = t^{2/3}/k`, truncation
level `K = n³h` (tail from ES22 Lemma 2.2), Freedman level `x = t^{2/5}/4`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology ElboimSly.Cyclic ElboimSly.SRW
open scoped NNReal ENNReal

namespace ElboimSly.Paper.Step

open ElboimSly.Paper

/-- The conclusion of Lemma 7.3 (ES22 Lemma 7.3), with constant `c_tf = cTf` and threshold
`β_tf(n₁) = βTf n₁`. -/
def StepTf (d : ℕ) (cTf : ℝ) (βTf : ℕ → ℝ) : Prop :=
  ∀ n₁ : ℕ, 8 * d ≤ n₁ → ∀ (β : ℝ) [Fact (0 < β)] (n : ℕ) (t₀ : ℝ), βTf n₁ ≤ β →
    StepRegime d n₁ β n t₀ →
    ∀ (Ωe : Type) [MeasurableSpace Ωe] (Pe : Measure Ωe) (N : Ωe → Measure (ℕ × RingSpace d β)),
      IsPoissonPointProcess N ((Measure.count : Measure ℕ).prod (ringIntensity d β)) Pe →
      ∀ t : ℝ, Real.sqrt (indScale t₀ n) ≤ t → t ≤ indScale t₀ n →
        Pe.real {ω | ∃ s : ℝ≥0, (s : ℝ) ≤ t ^ ((2 : ℝ) / 3) ∧ t ^ ((2 : ℝ) / 5) ≤
          ‖regenWalk (fun j => copyEnv (N ω) j) (s : ℝ)‖} ≤ Real.exp (-(cTf * (n : ℝ) ^ 3))

variable {d : ℕ}

/-- Powers of `u = t^{1/15}`. -/
theorem rpow_fifteenth {t : ℝ} (ht : 0 < t) :
    (t ^ ((1 : ℝ) / 15)) ^ 15 = t := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le]; norm_num

theorem rpow_two_thirds {t : ℝ} (ht : 0 < t) :
    t ^ ((2 : ℝ) / 3) = (t ^ ((1 : ℝ) / 15)) ^ 10 := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le]; norm_num

theorem rpow_two_fifths {t : ℝ} (ht : 0 < t) :
    t ^ ((2 : ℝ) / 5) = (t ^ ((1 : ℝ) / 15)) ^ 6 := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le]; norm_num

/-- `4^{n+1} ≤ (4ⁿ)³` for `n ≥ 1`. -/
theorem four_pow_succ_le (n : ℕ) (hn : 1 ≤ n) : (4 : ℝ) ^ (n + 1) ≤ ((4 : ℝ) ^ n) ^ 3 := by
  rw [← pow_mul]
  exact pow_le_pow_right₀ (by norm_num) (by omega)

/-- `4^{n+1} ≤ exp(3n)`. -/
theorem four_pow_succ_le_exp (n : ℕ) (hn : 1 ≤ n) : (4 : ℝ) ^ (n + 1) ≤ Real.exp (3 * n) := by
  rw [four_pow_eq_exp]
  apply Real.exp_le_exp.2
  have h2 := Real.log_two_lt_d9
  have h4 : Real.log 4 = 2 * Real.log 2 := Real.log_four_eq
  have : (1 : ℝ) ≤ n := by exact_mod_cast hn
  push_cast
  nlinarith

/-- Second-moment arithmetic of Lemma 7.3: `6dh + 2h^{2θ} + K² e^{-n(h)²} ≤ 7dh` for
`K = n³ h`. -/
theorem travel73_hv {n d : ℕ} {u h : ℝ} (hd1 : (1 : ℝ) ≤ d) (hn100 : (100 : ℝ) ≤ n)
    (hlo : u ^ 5 / 2 ≤ h) (hu64 : 64 ≤ u) (h30 : (4 : ℝ) ^ n ≤ u ^ 30)
    (hexp : h ≤ Real.exp n)
    (hB : (n : ℝ) ^ 6 * Real.exp n * Real.exp (-((n : ℝ) / 6 - 3 / 2) ^ 2) ≤ 1 / 2) :
    6 * (d : ℝ) * h + 2 * h ^ (2 * indThetaH) +
      ((n : ℝ) ^ 3 * h) ^ 2 * Real.exp (-((stepLevel h : ℝ) ^ 2)) ≤ 7 * d * h := by
  have hu5 : (64 : ℝ) ^ 5 ≤ u ^ 5 := pow_le_pow_left₀ (by norm_num) hu64 5
  have hh4096 : 4096 ≤ h := by norm_num at hu5; linarith
  have hh0 : 0 < h := by linarith
  have hh1 : 1 < h := by linarith
  have hm0 : (0 : ℝ) ≤ (n : ℝ) / 6 - 3 / 2 := by linarith
  have hlog : (n : ℝ) / 6 - 3 / 2 + 1 ≤ Real.logb 4 h := by
    rw [Real.le_logb_iff_rpow_le (by norm_num) hh0]
    set a : ℝ := (4 : ℝ) ^ ((n : ℝ) / 6 - 3 / 2 + 1) with ha
    have ha0 : 0 < a := Real.rpow_pos_of_pos (by norm_num) _
    have ha6 : a ^ 6 = 4 ^ n / 64 := by
      rw [ha, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
      have : ((n : ℝ) / 6 - 3 / 2 + 1) * ((6 : ℕ) : ℝ) = (n : ℝ) - 3 := by push_cast; ring
      rw [this, Real.rpow_sub (by norm_num), Real.rpow_natCast]; norm_num
    have hh6 : (4 : ℝ) ^ n / 64 ≤ h ^ 6 := by
      calc (4 : ℝ) ^ n / 64 ≤ u ^ 30 / 64 := by gcongr
        _ = (u ^ 5 / 2) ^ 6 := by ring
        _ ≤ h ^ 6 := by gcongr
    exact (pow_le_pow_iff_left₀ ha0.le hh0.le (by norm_num : (6 : ℕ) ≠ 0)).1
      (by rw [ha6]; exact hh6)
  have S1 := two_mul_rpow_theta_le hh4096
  have S2 : ((n : ℝ) ^ 3 * h) ^ 2 * Real.exp (-((stepLevel h : ℝ) ^ 2)) ≤ h / 2 := by
    have e1 := exp_neg_level_sq_le hh1 hm0 hlog
    calc ((n : ℝ) ^ 3 * h) ^ 2 * Real.exp (-((stepLevel h : ℝ) ^ 2))
        ≤ ((n : ℝ) ^ 3 * h) ^ 2 * Real.exp (-((n : ℝ) / 6 - 3 / 2) ^ 2) := by gcongr
      _ = h * ((n : ℝ) ^ 6 * h * Real.exp (-((n : ℝ) / 6 - 3 / 2) ^ 2)) := by ring
      _ ≤ h * ((n : ℝ) ^ 6 * Real.exp n * Real.exp (-((n : ℝ) / 6 - 3 / 2) ^ 2)) := by gcongr
      _ ≤ h * (1 / 2) := by gcongr
      _ = h / 2 := by ring
  nlinarith [mul_le_mul_of_nonneg_right hd1 hh0.le]

/-- The tail arithmetic: `h ≥ 10 d`. -/
theorem travel73_h10d {n d : ℕ} {u h : ℝ} (hdn : (d : ℝ) ≤ n) (hn1 : (1 : ℝ) ≤ n)
    (hlo : u ^ 5 / 2 ≤ h) (hu : 64 * (n : ℝ) ^ 6 ≤ u) : 10 * (d : ℝ) ≤ h := by
  have hu64 : 64 ≤ u := by
    have : (1 : ℝ) ≤ (n : ℝ) ^ 6 := one_le_pow₀ hn1
    linarith
  have h5 : u ≤ u ^ 5 := by
    calc u = u ^ 1 := (pow_one u).symm
      _ ≤ u ^ 5 := pow_le_pow_right₀ (by linarith) (by norm_num)
  have h6 : (n : ℝ) ≤ (n : ℝ) ^ 6 := by
    calc (n : ℝ) = (n : ℝ) ^ 1 := (pow_one _).symm
      _ ≤ (n : ℝ) ^ 6 := pow_le_pow_right₀ hn1 (by norm_num)
  linarith

/-- Truncation tail from `cyc_far`: `ℙ(sup_{s ≤ h} ‖W(s)‖ ≥ n³h) ≤ e^{-n³}` for `h ≥ 10 d`. -/
theorem travel73_tail {β : ℝ} [Fact (0 < β)] (hd : 1 ≤ d) {Ωe : Type} [MeasurableSpace Ωe]
    {Pe : Measure Ωe} {Np : Ωe → Measure (ℕ × RingSpace d β)}
    (hNp : IsPoissonPointProcess Np ((Measure.count : Measure ℕ).prod (ringIntensity d β)) Pe)
    {n : ℕ} {h : ℝ} (hh10 : 10 * (d : ℝ) ≤ h) (hn : 10 * (d : ℝ) ≤ (n : ℝ) ^ 3) :
    Pe.real {ω | ∃ s : ℝ≥0, s ≤ h.toNNReal ∧
      (n : ℝ) ^ 3 * h ≤ ‖regenWalk (fun j => copyEnv (Np ω) j) (s : ℝ)‖} ≤
      Real.exp (-((n : ℝ) ^ 3)) := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hh0 : 0 < h := by linarith
  have hL1 : 1 ≤ (n : ℝ) ^ 3 / (10 * d) := by
    rw [le_div_iff₀ (by positivity)]; linarith
  have hcf := Cyclic.cyc_far hd hNp hL1 hh0.le
  refine le_trans (le_of_eq ?_) (hcf.trans ?_)
  · congr 1
    ext ω
    have hK : (n : ℝ) ^ 3 * h = 10 * d * ((n : ℝ) ^ 3 / (10 * d)) * h := by
      field_simp
    constructor
    · rintro ⟨s, hs, hKs⟩
      refine ⟨s, (Real.le_toNNReal_iff_coe_le hh0.le).1 hs, ?_⟩
      simp only [← copyEnv_eq_cycSlice]
      rw [← hK]; exact hKs
    · rintro ⟨s, hs, hKs⟩
      refine ⟨s, (Real.le_toNNReal_iff_coe_le hh0.le).2 hs, ?_⟩
      simp only [← copyEnv_eq_cycSlice] at hKs
      rw [hK]; exact hKs
  · apply Real.exp_le_exp.2
    have : (n : ℝ) ^ 3 ≤ (n : ℝ) ^ 3 / (10 * d) * h := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      have : 0 ≤ (n : ℝ) ^ 3 := by positivity
      nlinarith
    linarith

/-- `t_n^{2ε} ≤ u/4` when `t_n ≤ u^{30}` and `u ≥ 64`. -/
theorem travel_tn_rpow_le {d : ℕ} (hd : 1 ≤ d) {u tn : ℝ} (hu : 64 ≤ u) (htn1 : 1 ≤ tn)
    (htn : tn ≤ u ^ 30) : tn ^ (2 * heavyEps d) ≤ u / 4 := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hε : 2 * heavyEps d ≤ 1 / 150 := by
    unfold heavyEps
    rw [show 2 * (1 / (300 * (d : ℝ))) = 1 / (150 * d) by field_simp; ring]
    exact one_div_le_one_div_of_le (by norm_num) (by nlinarith)
  have h1 : tn ^ (2 * heavyEps d) ≤ tn ^ ((1 : ℝ) / 150) :=
    Real.rpow_le_rpow_of_exponent_le htn1 hε
  refine h1.trans ?_
  have hu0 : 0 < u := by linarith
  have htn0 : 0 < tn := by linarith
  refine (pow_le_pow_iff_left₀ (Real.rpow_pos_of_pos htn0 _).le (by positivity)
    (by norm_num : (150 : ℕ) ≠ 0)).1 ?_
  rw [← Real.rpow_natCast, ← Real.rpow_mul htn0.le]
  norm_num
  rw [div_pow]
  rw [le_div_iff₀ (by positivity)]
  have h120 : (64 : ℝ) ^ 120 ≤ u ^ 120 := pow_le_pow_left₀ (by norm_num) hu 120
  have : u ^ 150 = u ^ 30 * u ^ 120 := by ring
  have h4 : (4 : ℝ) ^ 150 ≤ 64 ^ 120 := by norm_num
  calc tn * 4 ^ 150 ≤ u ^ 30 * u ^ 120 := by
        apply mul_le_mul htn (h4.trans h120) (by positivity) (by positivity)
    _ = u ^ 150 := this.symm

/-- The radius arithmetic of Lemma 7.3: `k t_n^{2ε} + n³h + u⁶/4 ≤ u⁶`. -/
theorem travel73_radius {n d : ℕ} {u h tn : ℝ} (k : ℕ) (hd : 1 ≤ d) (hn1 : (1 : ℝ) ≤ n)
    (hu : 64 * (n : ℝ) ^ 6 ≤ u) (hk : (k : ℝ) ≤ 2 * u ^ 5) (hhi : h ≤ u ^ 5) (hh0 : 0 ≤ h)
    (htn1 : 1 ≤ tn) (htn : tn ≤ u ^ 30) :
    (k : ℝ) * tn ^ (2 * heavyEps d) + (n : ℝ) ^ 3 * h + u ^ 6 / 4 ≤ u ^ 6 := by
  have hn6 : (1 : ℝ) ≤ (n : ℝ) ^ 6 := one_le_pow₀ hn1
  have hu64 : 64 ≤ u := by linarith
  have hu0 : 0 < u := by linarith
  have hA := travel_tn_rpow_le hd hu64 htn1 htn
  have hA0 : 0 ≤ tn ^ (2 * heavyEps d) := Real.rpow_nonneg (by linarith) _
  have e1 : (k : ℝ) * tn ^ (2 * heavyEps d) ≤ u ^ 6 / 2 := by
    calc (k : ℝ) * tn ^ (2 * heavyEps d) ≤ 2 * u ^ 5 * (u / 4) := by
          apply mul_le_mul hk hA hA0 (by positivity)
      _ = u ^ 6 / 2 := by ring
  have e2 : (n : ℝ) ^ 3 * h ≤ u ^ 6 / 64 := by
    have h3 : (n : ℝ) ^ 3 ≤ (n : ℝ) ^ 6 := pow_le_pow_right₀ hn1 (by norm_num)
    have h4 : (n : ℝ) ^ 3 ≤ u / 64 := by linarith
    calc (n : ℝ) ^ 3 * h ≤ (u / 64) * u ^ 5 := by
          apply mul_le_mul h4 hhi hh0 (by positivity)
      _ = u ^ 6 / 64 := by ring
  have : (0 : ℝ) < u ^ 6 := by positivity
  linarith

/-- The final summation of Lemmas 7.3 and 7.4: `(k-1) e^{-c n³} + k p + X ≤ e^{-c' n³/2}`. -/
theorem travel_sum_le {k n d : ℕ} {c' cCat p X : ℝ} (hcc : c' ≤ cCat)
    (hp : p ≤ Real.exp (-(c' * (n : ℝ) ^ 3))) (hk : (k : ℝ) ≤ 2 * 4 ^ n) (hd : (d : ℝ) ≤ 4 ^ n)
    (hC : 20 * (4 : ℝ) ^ n ≤ Real.exp (c' / 2 * (n : ℝ) ^ 3))
    (hX : X ≤ 2 * d * Real.exp (-(c' * (n : ℝ) ^ 3))) (hk1 : 1 ≤ k) :
    ((k : ℝ) - 1) * Real.exp (-(cCat * (n : ℝ) ^ 3)) + k * p + X ≤
      Real.exp (-(c' / 2 * (n : ℝ) ^ 3)) := by
  set E := Real.exp (-(c' * (n : ℝ) ^ 3)) with hE
  have hn3 : 0 ≤ (n : ℝ) ^ 3 := by positivity
  have hA : Real.exp (-(cCat * (n : ℝ) ^ 3)) ≤ E := by
    apply Real.exp_le_exp.2; nlinarith
  have hE0 : 0 < E := Real.exp_pos _
  have hk0 : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  have h1 : ((k : ℝ) - 1) * Real.exp (-(cCat * (n : ℝ) ^ 3)) ≤ ((k : ℝ) - 1) * E := by
    apply mul_le_mul_of_nonneg_left hA; linarith
  have h2 : (k : ℝ) * p ≤ k * E := mul_le_mul_of_nonneg_left hp (by linarith)
  have h4 : (2 * (k : ℝ) + 2 * d) ≤ 20 * 4 ^ n := by linarith
  have h5 : (2 * (k : ℝ) + 2 * d) * E ≤ Real.exp (c' / 2 * (n : ℝ) ^ 3) * E :=
    mul_le_mul_of_nonneg_right (h4.trans hC) hE0.le
  have h6 : Real.exp (c' / 2 * (n : ℝ) ^ 3) * E = Real.exp (-(c' / 2 * (n : ℝ) ^ 3)) := by
    rw [hE, ← Real.exp_add]; congr 1; ring
  nlinarith

section Data

variable {β : ℝ} [Fact (0 < β)]

/-- The time `t` in the regime: `2ⁿ ≤ t ≤ 4^{n+1}` and `t_n ≤ t²`. -/
theorem travel_time_bounds {n : ℕ} {t₀ t : ℝ} (ht0 : t₀ ∈ Ioc (1 : ℝ) 4)
    (ht1 : Real.sqrt (indScale t₀ n) ≤ t) (ht2 : t ≤ indScale t₀ n) :
    (2 : ℝ) ^ n ≤ t ∧ indScale t₀ n ≤ t ^ 2 ∧ t ≤ 4 ^ (n + 1) ∧ 1 ≤ indScale t₀ n := by
  obtain ⟨htn_gt, htn_le⟩ := indScale_bounds (n := n) ht0
  have h4 : (0 : ℝ) < 4 ^ n := by positivity
  refine ⟨?_, ?_, ht2.trans htn_le, ?_⟩
  · refine le_trans ?_ ht1
    rw [Real.le_sqrt (by positivity) (h4.trans htn_gt).le]
    calc ((2 : ℝ) ^ n) ^ 2 = 4 ^ n := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
      _ ≤ _ := htn_gt.le
  · calc indScale t₀ n = (Real.sqrt (indScale t₀ n)) ^ 2 :=
          (Real.sq_sqrt (h4.trans htn_gt).le).symm
      _ ≤ t ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) ht1 2
  · have : (1 : ℝ) ≤ 4 ^ n := one_le_pow₀ (by norm_num)
    linarith

/-- The block data of Lemma 7.3: `u = t^{1/15}`, `k = ⌈u⁵⌉`, `h = u^{10}/k`. -/
theorem travel73_data {n₁ n : ℕ} {d : ℕ} {t₀ t : ℝ} (hR : StepRegime d n₁ β n t₀)
    (hβ4 : (4 : ℝ) ^ (6 * (n₁ + 2)) ≤ β) (hn : 1 ≤ n) (hA : (64 * (n : ℝ) ^ 6) ^ 15 ≤ 2 ^ n)
    (ht1 : Real.sqrt (indScale t₀ n) ≤ t) (ht2 : t ≤ indScale t₀ n) :
    ∃ (u : ℝ) (k : ℕ) (h : ℝ), 64 * (n : ℝ) ^ 6 ≤ u ∧ u ^ 15 = t ∧ 1 ≤ k ∧
      u ^ 5 / 2 ≤ h ∧ h ≤ u ^ 5 ∧ (k : ℝ) * h = u ^ 10 ∧ (k : ℝ) ≤ 2 * u ^ 5 ∧
      (4 : ℝ) ^ n₁ < h ∧ h ≤ 4 ^ n ∧ (k : ℝ) * h ≤ indScale t₀ n ∧ h ≤ Real.exp n ∧
      (4 : ℝ) ^ n ≤ u ^ 30 ∧ indScale t₀ n ≤ u ^ 30 ∧ u ^ 5 ≤ 4 ^ n ∧
      t ^ ((2 : ℝ) / 3) = u ^ 10 ∧ t ^ ((2 : ℝ) / 5) = u ^ 6 := by
  obtain ⟨-, hβ1, hn1, ht0, htn_lt, -⟩ := id hR
  obtain ⟨h2n, htn_sq, ht_le4, htn1⟩ := travel_time_bounds ht0 ht1 ht2
  have ht_pos : 0 < t := lt_of_lt_of_le (by positivity) h2n
  obtain ⟨u, hu⟩ : ∃ u, u = t ^ ((1 : ℝ) / 15) := ⟨_, rfl⟩
  have hu15 : u ^ 15 = t := by rw [hu]; exact rpow_fifteenth ht_pos
  have hu0 : 0 < u := by rw [hu]; exact Real.rpow_pos_of_pos ht_pos _
  have hu64n : 64 * (n : ℝ) ^ 6 ≤ u := by
    have : (64 * (n : ℝ) ^ 6) ^ 15 ≤ u ^ 15 := hA.trans (h2n.trans (le_of_eq hu15.symm))
    exact (pow_le_pow_iff_left₀ (by positivity) hu0.le (by norm_num)).1 this
  have hn6 : (1 : ℝ) ≤ (n : ℝ) ^ 6 := one_le_pow₀ (by exact_mod_cast hn)
  have hu64 : 64 ≤ u := by linarith
  have hu5_1 : (1 : ℝ) ≤ u ^ 5 := one_le_pow₀ (by linarith)
  have hu5_pos : 0 < u ^ 5 := by positivity
  obtain ⟨hk1, hk2, hk3⟩ := blocks_k hu5_1
  obtain ⟨h, hh⟩ : ∃ h, h = u ^ 10 / (⌈u ^ 5⌉₊ : ℝ) := ⟨_, rfl⟩
  obtain ⟨hh_lo, hh_hi, hkh⟩ := blocks_h (A := u ^ 5) (B := u ^ 10) (k := ⌈u ^ 5⌉₊)
    hu5_pos (by positivity) hk2 hk3
  rw [← hh] at hh_lo hh_hi hkh
  have hh_lo' : u ^ 5 / 2 ≤ h := by
    have : u ^ 10 / (2 * u ^ 5) = u ^ 5 / 2 := by field_simp
    rwa [this] at hh_lo
  have hh_hi' : h ≤ u ^ 5 := by
    have : u ^ 10 / u ^ 5 = u ^ 5 := by field_simp
    rwa [this] at hh_hi
  have hu5_cube : (u ^ 5) ^ 3 = t := by rw [← pow_mul, hu15]
  have hu5_4n : u ^ 5 ≤ 4 ^ n := by
    have : (u ^ 5) ^ 3 ≤ ((4 : ℝ) ^ n) ^ 3 := by
      rw [hu5_cube]; exact ht_le4.trans (four_pow_succ_le n hn)
    exact (pow_le_pow_iff_left₀ hu5_pos.le (by positivity) (by norm_num)).1 this
  have hh_exp : h ≤ Real.exp n := by
    have : (u ^ 5) ^ 3 ≤ (Real.exp n) ^ 3 := by
      rw [hu5_cube, ← Real.exp_nat_mul]
      refine ht_le4.trans ((four_pow_succ_le_exp n hn).trans (le_of_eq ?_))
      push_cast; ring_nf
    have := (pow_le_pow_iff_left₀ hu5_pos.le (Real.exp_pos _).le (by norm_num)).1 this
    linarith
  have h1 : (4 : ℝ) ^ n₁ < h := by
    refine stepRegime_interval hR (κ := 1 / 6) (by norm_num) ?_ (s := h) ?_
    · have : ((n₁ : ℝ) + 2) / (1 / 6) = ((6 * (n₁ + 2) : ℕ) : ℝ) := by push_cast; ring
      rw [this, Real.rpow_natCast]; exact hβ4
    · have h6 : (indScale t₀ n ^ ((1 : ℝ) / 6)) ^ 6 = indScale t₀ n := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]; norm_num
      have : indScale t₀ n ^ ((1 : ℝ) / 6) ≤ u ^ 5 := by
        refine (pow_le_pow_iff_left₀ (by positivity) hu5_pos.le (by norm_num : (6 : ℕ) ≠ 0)).1 ?_
        rw [h6, ← pow_mul]
        calc indScale t₀ n ≤ t ^ 2 := htn_sq
          _ = u ^ (5 * 6) := by rw [← hu15, ← pow_mul]
      linarith
  have hkh_le : (⌈u ^ 5⌉₊ : ℝ) * h ≤ indScale t₀ n := by
    rw [hkh]
    calc u ^ 10 ≤ u ^ 15 := pow_le_pow_right₀ (by linarith) (by norm_num)
      _ = t := hu15
      _ ≤ _ := ht2
  have h4t : (4 : ℝ) ^ n ≤ u ^ 30 := by
    calc (4 : ℝ) ^ n = (2 ^ n) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
      _ ≤ t ^ 2 := pow_le_pow_left₀ (by positivity) h2n 2
      _ = u ^ 30 := by rw [← hu15, ← pow_mul]
  refine ⟨u, ⌈u ^ 5⌉₊, h, hu64n, hu15, hk1, hh_lo', hh_hi', hkh, hk3, h1, hh_hi'.trans hu5_4n,
    hkh_le, hh_exp, h4t, ?_, hu5_4n, by rw [hu]; exact rpow_two_thirds ht_pos,
    by rw [hu]; exact rpow_two_fifths ht_pos⟩
  calc indScale t₀ n ≤ t ^ 2 := htn_sq
    _ = u ^ 30 := by rw [← hu15, ← pow_mul]

end Data

/-- `e^{-x} ≤ e^{-c' x}` for `c' ≤ 1` and `x ≥ 0`. -/
theorem travel_exp_neg_le_aux {c' : ℝ} (hc : c' ≤ 1) (x : ℝ) (hx : 0 ≤ x) :
    Real.exp (-x) ≤ Real.exp (-(c' * x)) := by
  apply Real.exp_le_exp.2
  nlinarith

/-- **Lemma 7.3**, conditional on `StepCor72` (the conclusion of Corollary 7.2).
ES22 Lemma 7.3. -/
theorem step_lemma73_of_cor72 (hd : 1 ≤ d) {cCat : ℝ} (hc : 0 < cCat) {βCat : ℕ → ℝ}
    (hCor : StepCor72 d cCat βCat) :
    ∃ cTf : ℝ, 0 < cTf ∧ ∃ βTf : ℕ → ℝ, StepTf d cTf βTf := by
  set c' : ℝ := min cCat 1 with hc'def
  have hc' : 0 < c' := lt_min hc one_pos
  obtain ⟨N0, hN0⟩ := eventually_atTop.1 (travel_eventually d hc')
  refine ⟨c' / 2, by positivity, fun n₁ => max (βCat n₁) (max ((12 : ℝ) ^ 16)
    (max ((4 : ℝ) ^ (6 * (n₁ + 2))) ((4 : ℝ) ^ (N0 + 1)))), ?_⟩
  intro n₁ hn₁ β _ n t₀ hβ hR Ωe _ Pe Np hNp t ht1 ht2
  have hβ' : max (βCat n₁) (max ((12 : ℝ) ^ 16)
    (max ((4 : ℝ) ^ (6 * (n₁ + 2))) ((4 : ℝ) ^ (N0 + 1)))) ≤ β := hβ
  simp only [max_le_iff] at hβ'
  obtain ⟨hβc, hβ12, hβ4, hβN⟩ := hβ'
  obtain ⟨-, hβ1, hn1, ht0, htn_lt, -⟩ := id hR
  obtain ⟨htn_gt, htn_le⟩ := indScale_bounds (n := n) ht0
  have hnN : N0 ≤ n := by
    have h1 : (4 : ℝ) ^ (N0 + 1) < 4 ^ (n + 1) :=
      lt_of_le_of_lt hβN (lt_of_lt_of_le htn_lt htn_le)
    have := (pow_lt_pow_iff_right₀ (by norm_num : (1 : ℝ) < 4)).1 h1
    omega
  obtain ⟨h100, hdn, hA, hB, -, -, hC⟩ := hN0 n hnN
  have hn100 : (100 : ℝ) ≤ n := by
    have : (200 : ℝ) ≤ n := by exact_mod_cast h100
    linarith
  have hdn' : (d : ℝ) ≤ n := by
    have : d ≤ n := by omega
    exact_mod_cast this
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  obtain ⟨u, k, h, hu64n, hu15, hk1, hlo, hhi, hkh, hk2, h1, h2, hkh_le, hexp, h4u, htnu, hu54, ht23, ht25⟩ :=
    travel73_data hR hβ4 (by omega) hA ht1 ht2
  have hn6 : (1 : ℝ) ≤ (n : ℝ) ^ 6 := one_le_pow₀ (by linarith)
  have hu64 : 64 ≤ u := by linarith
  have hh0 : 0 < h := by
    have : (0 : ℝ) < u ^ 5 := by positivity
    linarith
  have hht10 := travel73_h10d hdn' (by linarith) hlo hu64n
  have hn3 : 10 * (d : ℝ) ≤ (n : ℝ) ^ 3 := by
    have h2 : (100 : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 := pow_le_pow_left₀ (by norm_num) hn100 2
    have : (n : ℝ) ^ 3 = n * n ^ 2 := by ring
    rw [this]
    nlinarith
  have hv := travel73_hv hd1 hn100 hlo hu64 h4u hexp hB
  have hV : 0 < (k : ℝ) * (7 * d * h) := by
    have : (0 : ℝ) < k := by exact_mod_cast hk1
    positivity
  have htail := travel73_tail hd hNp hht10 hn3
  have key := step_travel_engine hd hCor hR hβc hβ12 hk1 h1 h2 hkh_le
    (K := (n : ℝ) ^ 3 * h) (x := u ^ 6 / 4) (v := 7 * d * h)
    (p := Real.exp (-((n : ℝ) ^ 3))) (by positivity) (by positivity) hv hV hNp htail
  have hrad := travel73_radius k hd (by linarith) hu64n hk2 hhi hh0.le
    (by have := travel_time_bounds ht0 ht1 ht2; exact this.2.2.2) htnu
  have hfm : (n : ℝ) ^ 3 ≤ (u ^ 6 / 4) ^ 2 / (2 * ((k : ℝ) * (7 * d * h) +
      (n : ℝ) ^ 3 * h * (u ^ 6 / 4) / 3)) := by
    have := freedman_exponent_73 (u := u) (h := h) (n := (n : ℝ)) (d := (d : ℝ))
      (by linarith) hdn' hd1 hu64n hh0.le hhi
    have e : (k : ℝ) * (7 * d * h) = 7 * d * u ^ 10 := by rw [← hkh]; ring
    rw [e]; exact this
  have hsub : {ω | ∃ s : ℝ≥0, (s : ℝ) ≤ t ^ ((2 : ℝ) / 3) ∧ t ^ ((2 : ℝ) / 5) ≤
      ‖regenWalk (fun j => copyEnv (Np ω) j) (s : ℝ)‖} ⊆
      {ω | ∃ s : ℝ≥0, (s : ℝ) ≤ k * h ∧ (k : ℝ) * indScale t₀ n ^ (2 * heavyEps d) +
        (n : ℝ) ^ 3 * h + u ^ 6 / 4 ≤ ‖regenWalk (fun j => copyEnv (Np ω) j) (s : ℝ)‖} := by
    rintro ω ⟨s, hs, hts⟩
    refine ⟨s, ?_, ?_⟩
    · rw [hkh, ← ht23]; exact hs
    · have hts' : u ^ 6 ≤ ‖regenWalk (fun j => copyEnv (Np ω) j) (s : ℝ)‖ := by
        rw [← ht25]; exact hts
      exact hrad.trans hts'
  have hn4 : (n : ℝ) < 4 ^ n := by exact_mod_cast Nat.lt_pow_self (by norm_num : 1 < 4)
  have hexpn := travel_exp_neg_le_aux (c' := c') (min_le_right _ _) ((n : ℝ) ^ 3) (by positivity)
  have hk4 : (k : ℝ) ≤ 2 * 4 ^ n := by
    have : (2 : ℝ) * u ^ 5 ≤ 2 * 4 ^ n := by linarith
    exact hk2.trans this
  have hX : 2 * (d : ℝ) * Real.exp (-((u ^ 6 / 4) ^ 2 / (2 * ((k : ℝ) * (7 * d * h) +
      (n : ℝ) ^ 3 * h * (u ^ 6 / 4) / 3)))) ≤ 2 * d * Real.exp (-(c' * (n : ℝ) ^ 3)) := by
    refine mul_le_mul_of_nonneg_left ((Real.exp_le_exp.2 (neg_le_neg hfm)).trans hexpn) (by positivity)
  have := hNp.isProbabilityMeasure
  exact (measureReal_mono hsub).trans (key.trans (travel_sum_le (min_le_left _ _) hexpn hk4
    (hdn'.trans hn4.le) hC hX hk1))

end ElboimSly.Paper.Step
