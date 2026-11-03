/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Step.Lemma73
public import Mathlib

/-!
# Lemma 7.4 (travelling far, conditional on Corollary 7.2)

ES22 Lemma 7.4 (§7; details supplied, F14).

`StepTr d cTr βTr` is the conclusion of Lemma 7.4: for `β ≥ βTr n₁`, `SR(n₁; β, n, t₀)` and all real
`t ∈ [√t_n, t_n]`, `ℙ(sup_{s ≤ t} ‖W(s)‖ ≥ n² √t) ≤ e^{-cTr n³}`.

`step_lemma74_of_cor72` proves it **assuming `StepCor72`** (through `step_lemma73_of_cor72`, which it
uses for the tail of the truncation); a conditional helper under a distinct name. The proof is the
written proof's: the engine `step_travel_engine` with `k = ⌈t^{1/3}⌉` blocks of length `h = t/k`,
truncation level `K = t^{2/5}` (tail from Lemma 7.3 at the same `t`), Freedman level
`x = n²√t/4`. All real powers are powers of `w = t^{1/30}`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology ElboimSly.Cyclic ElboimSly.SRW
open scoped NNReal ENNReal

namespace ElboimSly.Paper.Step

open ElboimSly.Paper

/-- The conclusion of Lemma 7.4 (ES22 Lemma 7.4), with constant `c_tr = cTr` and threshold
`β_tr(n₁) = βTr n₁`. -/
def StepTr (d : ℕ) (cTr : ℝ) (βTr : ℕ → ℝ) : Prop :=
  ∀ n₁ : ℕ, 8 * d ≤ n₁ → ∀ (β : ℝ) [Fact (0 < β)] (n : ℕ) (t₀ : ℝ), βTr n₁ ≤ β →
    StepRegime d n₁ β n t₀ →
    ∀ (Ωe : Type) [MeasurableSpace Ωe] (Pe : Measure Ωe) (N : Ωe → Measure (ℕ × RingSpace d β)),
      IsPoissonPointProcess N ((Measure.count : Measure ℕ).prod (ringIntensity d β)) Pe →
      ∀ t : ℝ, Real.sqrt (indScale t₀ n) ≤ t → t ≤ indScale t₀ n →
        Pe.real {ω | ∃ s : ℝ≥0, (s : ℝ) ≤ t ∧ (n : ℝ) ^ 2 * Real.sqrt t ≤
          ‖regenWalk (fun j => copyEnv (N ω) j) (s : ℝ)‖} ≤ Real.exp (-(cTr * (n : ℝ) ^ 3))

variable {d : ℕ}

/-- Powers of `w = t^{1/30}`. -/
theorem rpow_thirtieth {t : ℝ} (ht : 0 < t) : (t ^ ((1 : ℝ) / 30)) ^ 30 = t := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le]; norm_num

theorem rpow_30_two_thirds {t : ℝ} (ht : 0 < t) :
    t ^ ((2 : ℝ) / 3) = (t ^ ((1 : ℝ) / 30)) ^ 20 := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le]; norm_num

theorem rpow_30_two_fifths {t : ℝ} (ht : 0 < t) :
    t ^ ((2 : ℝ) / 5) = (t ^ ((1 : ℝ) / 30)) ^ 12 := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le]; norm_num

theorem sqrt_eq_pow_30 {t : ℝ} (ht : 0 < t) :
    Real.sqrt t = (t ^ ((1 : ℝ) / 30)) ^ 15 := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul ht.le]; norm_num

section Data

variable {β : ℝ} [Fact (0 < β)]

/-- The block data of Lemma 7.4: `w = t^{1/30}`, `k = ⌈w^{10}⌉`, `h = t/k`. -/
theorem travel74_data {n₁ n : ℕ} {t₀ t : ℝ} (hR : StepRegime d n₁ β n t₀)
    (hβ3 : (4 : ℝ) ^ (3 * (n₁ + 2)) ≤ β) (h200 : 200 ≤ n)
    (hA : (5 * (n : ℝ)) ^ 10 ≤ 2 ^ n)
    (ht1 : Real.sqrt (indScale t₀ n) ≤ t) (ht2 : t ≤ indScale t₀ n) :
    ∃ (w : ℝ) (k : ℕ) (h : ℝ), w ^ 30 = t ∧ 64 ≤ w ∧ 5 * (n : ℝ) ≤ w ^ 3 ∧ 1 ≤ k ∧
      w ^ 20 / 2 ≤ h ∧ h ≤ w ^ 20 ∧ (k : ℝ) * h = w ^ 30 ∧ (k : ℝ) ≤ 2 * w ^ 10 ∧
      (4 : ℝ) ^ n₁ < h ∧ h ≤ 4 ^ n ∧ w ^ 10 ≤ 4 ^ n ∧ (4 : ℝ) ^ n ≤ w ^ 60 ∧
      indScale t₀ n ≤ w ^ 60 ∧ w ^ 24 ≤ Real.exp (3 * n) ∧
      t ^ ((2 : ℝ) / 3) = w ^ 20 ∧ t ^ ((2 : ℝ) / 5) = w ^ 12 ∧ Real.sqrt t = w ^ 15 := by
  obtain ⟨-, hβ1, hn1, ht0, htn_lt, -⟩ := id hR
  obtain ⟨h2n, htn_sq, ht_le4, htn1⟩ := travel_time_bounds ht0 ht1 ht2
  have ht_pos : 0 < t := lt_of_lt_of_le (by positivity) h2n
  obtain ⟨w, hw⟩ : ∃ w, w = t ^ ((1 : ℝ) / 30) := ⟨_, rfl⟩
  have hw30 : w ^ 30 = t := by rw [hw]; exact rpow_thirtieth ht_pos
  have hw0 : 0 < w := by rw [hw]; exact Real.rpow_pos_of_pos ht_pos _
  have hw64 : 64 ≤ w := by
    have h1 : (64 : ℝ) ^ 30 ≤ w ^ 30 := by
      rw [hw30]
      calc (64 : ℝ) ^ 30 = 2 ^ 180 := by norm_num
        _ ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) (by omega)
        _ ≤ t := h2n
    exact (pow_le_pow_iff_left₀ (by norm_num) hw0.le (by norm_num)).1 h1
  have hw3 : 5 * (n : ℝ) ≤ w ^ 3 := by
    have h1 : (5 * (n : ℝ)) ^ 10 ≤ (w ^ 3) ^ 10 := by
      rw [← pow_mul, hw30]; exact hA.trans h2n
    exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by norm_num)).1 h1
  have hw10 : (1 : ℝ) ≤ w ^ 10 := one_le_pow₀ (by linarith)
  have hw10pos : 0 < w ^ 10 := by positivity
  obtain ⟨hk1, hk2, hk3⟩ := blocks_k hw10
  obtain ⟨h, hh⟩ : ∃ h, h = w ^ 30 / (⌈w ^ 10⌉₊ : ℝ) := ⟨_, rfl⟩
  obtain ⟨hh_lo, hh_hi, hkh⟩ := blocks_h (A := w ^ 10) (B := w ^ 30) (k := ⌈w ^ 10⌉₊)
    hw10pos (by positivity) hk2 hk3
  rw [← hh] at hh_lo hh_hi hkh
  have hh_lo' : w ^ 20 / 2 ≤ h := by
    have : w ^ 30 / (2 * w ^ 10) = w ^ 20 / 2 := by field_simp
    rwa [this] at hh_lo
  have hh_hi' : h ≤ w ^ 20 := by
    have : w ^ 30 / w ^ 10 = w ^ 20 := by field_simp
    rwa [this] at hh_hi
  have hw60 : (w ^ 20) ^ 3 = t ^ 2 := by rw [← pow_mul, ← hw30, ← pow_mul]
  have hw20_4n : w ^ 20 ≤ 4 ^ n := by
    have : (w ^ 20) ^ 3 ≤ ((4 : ℝ) ^ n) ^ 3 := by
      rw [hw60]
      calc t ^ 2 ≤ (4 ^ (n + 1)) ^ 2 := pow_le_pow_left₀ ht_pos.le ht_le4 2
        _ = 4 ^ (2 * n + 2) := by rw [← pow_mul]; ring_nf
        _ ≤ ((4 : ℝ) ^ n) ^ 3 := by
          rw [← pow_mul]; exact pow_le_pow_right₀ (by norm_num) (by omega)
    exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by norm_num)).1 this
  have hw10_4n : w ^ 10 ≤ 4 ^ n := by
    have : w ^ 10 ≤ w ^ 20 := pow_le_pow_right₀ (by linarith) (by norm_num)
    linarith
  have h4t : (4 : ℝ) ^ n ≤ w ^ 60 := by
    calc (4 : ℝ) ^ n = (2 ^ n) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
      _ ≤ t ^ 2 := pow_le_pow_left₀ (by positivity) h2n 2
      _ = w ^ 60 := by rw [← hw30, ← pow_mul]
  have htnw : indScale t₀ n ≤ w ^ 60 := by
    calc indScale t₀ n ≤ t ^ 2 := htn_sq
      _ = w ^ 60 := by rw [← hw30, ← pow_mul]
  have hw24 : w ^ 24 ≤ Real.exp (3 * n) := by
    have h5 : (w ^ 24) ^ 5 ≤ (Real.exp (3 * n)) ^ 5 := by
      calc (w ^ 24) ^ 5 = t ^ 4 := by rw [← pow_mul, ← hw30, ← pow_mul]
        _ ≤ (4 ^ (n + 1)) ^ 4 := pow_le_pow_left₀ ht_pos.le ht_le4 4
        _ ≤ (Real.exp (3 * n)) ^ 4 :=
          pow_le_pow_left₀ (by positivity) (four_pow_succ_le_exp n (by omega)) 4
        _ ≤ (Real.exp (3 * n)) ^ 5 := by
          apply pow_le_pow_right₀ _ (by norm_num)
          rw [← Real.exp_zero]; apply Real.exp_le_exp.2; positivity
    exact (pow_le_pow_iff_left₀ (by positivity) (Real.exp_pos _).le (by norm_num)).1 h5
  have h1 : (4 : ℝ) ^ n₁ < h := by
    refine stepRegime_interval hR (κ := 1 / 3) (by norm_num) ?_ (s := h) ?_
    · have : ((n₁ : ℝ) + 2) / (1 / 3) = ((3 * (n₁ + 2) : ℕ) : ℝ) := by push_cast; ring
      rw [this, Real.rpow_natCast]; exact hβ3
    · have h3 : (indScale t₀ n ^ ((1 : ℝ) / 3)) ^ 3 = indScale t₀ n := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]; norm_num
      have : indScale t₀ n ^ ((1 : ℝ) / 3) ≤ w ^ 20 := by
        refine (pow_le_pow_iff_left₀ (by positivity) (by positivity)
          (by norm_num : (3 : ℕ) ≠ 0)).1 ?_
        rw [h3, ← pow_mul]; exact htnw
      linarith
  exact ⟨w, ⌈w ^ 10⌉₊, h, hw30, hw64, hw3, hk1, hh_lo', hh_hi', hkh, hk3, h1,
    hh_hi'.trans hw20_4n, hw10_4n, h4t, htnw, hw24, by rw [hw]; exact rpow_30_two_thirds ht_pos,
    by rw [hw]; exact rpow_30_two_fifths ht_pos, by rw [hw]; exact sqrt_eq_pow_30 ht_pos⟩

end Data

/-- Second-moment arithmetic of Lemma 7.4 (`K = w^{12}`). -/
theorem travel74_hv {n d : ℕ} {w h : ℝ} (hd1 : (1 : ℝ) ≤ d) (hn200 : (200 : ℝ) ≤ n)
    (hlo : w ^ 20 / 2 ≤ h) (hw64 : 64 ≤ w) (h60 : (4 : ℝ) ^ n ≤ w ^ 60)
    (hK : w ^ 24 ≤ Real.exp (3 * n))
    (hB : Real.exp (3 * n) * Real.exp (-((n : ℝ) / 3 - 3 / 2) ^ 2) ≤ 1 / 2) :
    6 * (d : ℝ) * h + 2 * h ^ (2 * indThetaH) +
      (w ^ 12) ^ 2 * Real.exp (-((stepLevel h : ℝ) ^ 2)) ≤ 7 * d * h := by
  have hw20 : (64 : ℝ) ^ 20 ≤ w ^ 20 := pow_le_pow_left₀ (by norm_num) hw64 20
  have hh4096 : 4096 ≤ h := by norm_num at hw20; linarith
  have hh0 : 0 < h := by linarith
  have hh1 : 1 < h := by linarith
  have hm0 : (0 : ℝ) ≤ (n : ℝ) / 3 - 3 / 2 := by linarith
  have hlog : (n : ℝ) / 3 - 3 / 2 + 1 ≤ Real.logb 4 h := by
    rw [Real.le_logb_iff_rpow_le (by norm_num) hh0]
    set a : ℝ := (4 : ℝ) ^ ((n : ℝ) / 3 - 3 / 2 + 1) with ha
    have ha0 : 0 < a := Real.rpow_pos_of_pos (by norm_num) _
    have ha6 : a ^ 6 = (4 : ℝ) ^ (2 * n) / 64 := by
      rw [ha, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
      have : ((n : ℝ) / 3 - 3 / 2 + 1) * ((6 : ℕ) : ℝ) = ((2 * n : ℕ) : ℝ) - 3 := by
        push_cast; ring
      rw [this, Real.rpow_sub (by norm_num), Real.rpow_natCast]; norm_num
    have hh6 : (4 : ℝ) ^ (2 * n) / 64 ≤ h ^ 6 := by
      calc (4 : ℝ) ^ (2 * n) / 64 = ((4 : ℝ) ^ n) ^ 2 / 64 := by rw [pow_mul']
        _ ≤ (w ^ 60) ^ 2 / 64 := by gcongr
        _ = (w ^ 20 / 2) ^ 6 := by ring
        _ ≤ h ^ 6 := by gcongr
    exact (pow_le_pow_iff_left₀ ha0.le hh0.le (by norm_num : (6 : ℕ) ≠ 0)).1
      (by rw [ha6]; exact hh6)
  have S1 := two_mul_rpow_theta_le hh4096
  have S2 : (w ^ 12) ^ 2 * Real.exp (-((stepLevel h : ℝ) ^ 2)) ≤ h / 2 := by
    have e1 := exp_neg_level_sq_le hh1 hm0 hlog
    calc (w ^ 12) ^ 2 * Real.exp (-((stepLevel h : ℝ) ^ 2))
        ≤ Real.exp (3 * n) * Real.exp (-((n : ℝ) / 3 - 3 / 2) ^ 2) := by
          have : (w ^ 12) ^ 2 = w ^ 24 := by ring
          rw [this]; gcongr
      _ ≤ 1 / 2 := hB
      _ ≤ h / 2 := by linarith
  nlinarith [mul_le_mul_of_nonneg_right hd1 hh0.le]

/-- The Freedman exponent of Lemma 7.4: `n³ ≤ x² / (2 (7 d k h + K x / 3))` for `k h = w^{30}`,
`K = w^{12}` and `x = n² w^{15}/4`. -/
theorem freedman_exponent_74 {w n d : ℝ} (hn : 1 ≤ n) (hd : 1024 * d ≤ n) (hd1 : 1 ≤ d)
    (hw : 5 * n ≤ w ^ 3) (hw0 : 0 < w) :
    n ^ 3 ≤ (n ^ 2 * w ^ 15 / 4) ^ 2 / (2 * (7 * d * w ^ 30 + w ^ 12 * (n ^ 2 * w ^ 15 / 4) / 3)) := by
  have hn0 : 0 < n := by linarith
  have hden : 0 < 2 * (7 * d * w ^ 30 + w ^ 12 * (n ^ 2 * w ^ 15 / 4) / 3) := by positivity
  rw [le_div_iff₀ hden]
  have e1 : 14 * d * n ^ 3 * w ^ 30 ≤ n ^ 4 * w ^ 30 / 64 := by
    have : 14 * d * n ^ 3 ≤ n ^ 4 / 64 := by nlinarith [pow_pos hn0 3]
    have hw30 : 0 < w ^ 30 := by positivity
    nlinarith
  have e2 : n ^ 5 * w ^ 27 / 6 ≤ n ^ 4 * w ^ 30 / 30 := by
    have h1 : n * w ^ 27 ≤ w ^ 3 * w ^ 27 / 5 := by nlinarith [pow_pos hw0 27]
    have h4 : 0 < n ^ 4 := by positivity
    calc n ^ 5 * w ^ 27 / 6 = n ^ 4 * (n * w ^ 27) / 6 := by ring
      _ ≤ n ^ 4 * (w ^ 3 * w ^ 27 / 5) / 6 := by gcongr
      _ = n ^ 4 * w ^ 30 / 30 := by ring
  have hpos : 0 < n ^ 4 * w ^ 30 := by positivity
  calc n ^ 3 * (2 * (7 * d * w ^ 30 + w ^ 12 * (n ^ 2 * w ^ 15 / 4) / 3))
      = 14 * d * n ^ 3 * w ^ 30 + n ^ 5 * w ^ 27 / 6 := by ring
    _ ≤ n ^ 4 * w ^ 30 / 64 + n ^ 4 * w ^ 30 / 30 := by linarith
    _ ≤ (n ^ 2 * w ^ 15 / 4) ^ 2 := by nlinarith

/-- The radius arithmetic of Lemma 7.4. -/
theorem travel74_radius {n d : ℕ} {w tn : ℝ} (k : ℕ) (hd : 1 ≤ d) (hn1 : (1 : ℝ) ≤ n)
    (hw64 : 64 ≤ w) (hk : (k : ℝ) ≤ 2 * w ^ 10) (htn1 : 1 ≤ tn) (htn : tn ≤ w ^ 60) :
    (k : ℝ) * tn ^ (2 * heavyEps d) + w ^ 12 + (n : ℝ) ^ 2 * w ^ 15 / 4 ≤
      (n : ℝ) ^ 2 * w ^ 15 := by
  have hw0 : 0 < w := by linarith
  have hA := travel_tn_rpow_le hd (u := w ^ 2) (by nlinarith) htn1 (by
    calc tn ≤ w ^ 60 := htn
      _ = (w ^ 2) ^ 30 := by ring)
  have hA0 : 0 ≤ tn ^ (2 * heavyEps d) := Real.rpow_nonneg (by linarith) _
  have e1 : (k : ℝ) * tn ^ (2 * heavyEps d) ≤ w ^ 12 / 2 := by
    calc (k : ℝ) * tn ^ (2 * heavyEps d) ≤ 2 * w ^ 10 * (w ^ 2 / 4) := by
          apply mul_le_mul hk hA hA0 (by positivity)
      _ = w ^ 12 / 2 := by ring
  have e2 : 2 * w ^ 12 ≤ (n : ℝ) ^ 2 * w ^ 15 / 2 := by
    have hw3 : (64 : ℝ) ^ 3 ≤ w ^ 3 := pow_le_pow_left₀ (by norm_num) hw64 3
    have hn2 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := one_le_pow₀ hn1
    have h12 : 0 < w ^ 12 := by positivity
    have : w ^ 15 = w ^ 3 * w ^ 12 := by ring
    rw [this]
    nlinarith [mul_le_mul hn2 hw3 (by norm_num) (by positivity)]
  have : 0 ≤ (n : ℝ) ^ 2 * w ^ 15 := by positivity
  linarith

/-- **Lemma 7.4**, conditional on `StepCor72` (the conclusion of Corollary 7.2).
ES22 Lemma 7.4. -/
theorem step_lemma74_of_cor72 (hd : 1 ≤ d) {cCat : ℝ} (hc : 0 < cCat) {βCat : ℕ → ℝ}
    (hCor : StepCor72 d cCat βCat) :
    ∃ cTr : ℝ, 0 < cTr ∧ ∃ βTr : ℕ → ℝ, StepTr d cTr βTr := by
  obtain ⟨cTf, hcTf, βTf, hTf⟩ := step_lemma73_of_cor72 hd hc hCor
  set c' : ℝ := min (min cCat 1) cTf with hc'def
  have hc' : 0 < c' := lt_min (lt_min hc one_pos) hcTf
  have hc'cat : c' ≤ cCat := (min_le_left _ _).trans (min_le_left _ _)
  have hc'1 : c' ≤ 1 := (min_le_left _ _).trans (min_le_right _ _)
  have hc'tf : c' ≤ cTf := min_le_right _ _
  obtain ⟨N0, hN0⟩ := eventually_atTop.1 (travel_eventually d hc')
  refine ⟨c' / 2, by positivity, fun n₁ => max (βTf n₁) (max (βCat n₁) (max ((12 : ℝ) ^ 16)
    (max ((4 : ℝ) ^ (3 * (n₁ + 2))) ((4 : ℝ) ^ (N0 + 1))))), ?_⟩
  intro n₁ hn₁ β _ n t₀ hβ hR Ωe _ Pe Np hNp t ht1 ht2
  have hβ' : max (βTf n₁) (max (βCat n₁) (max ((12 : ℝ) ^ 16)
    (max ((4 : ℝ) ^ (3 * (n₁ + 2))) ((4 : ℝ) ^ (N0 + 1))))) ≤ β := hβ
  simp only [max_le_iff] at hβ'
  obtain ⟨hβtf, hβc, hβ12, hβ3, hβN⟩ := hβ'
  obtain ⟨-, hβ1, hn1, ht0, htn_lt, -⟩ := id hR
  obtain ⟨htn_gt, htn_le⟩ := indScale_bounds (n := n) ht0
  have hnN : N0 ≤ n := by
    have h1 : (4 : ℝ) ^ (N0 + 1) < 4 ^ (n + 1) :=
      lt_of_le_of_lt hβN (lt_of_lt_of_le htn_lt htn_le)
    have := (pow_lt_pow_iff_right₀ (by norm_num : (1 : ℝ) < 4)).1 h1
    omega
  obtain ⟨h200, hdn, -, -, hA, hB, hC⟩ := hN0 n hnN
  have hn200 : (200 : ℝ) ≤ n := by exact_mod_cast h200
  have hdn' : 1024 * (d : ℝ) ≤ n := by exact_mod_cast hdn
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  obtain ⟨w, k, h, hw30, hw64, hw3, hk1, hlo, hhi, hkh, hk2, h1, h2, hw10, h4w, htnw, hKw,
    ht23, ht25, hsq⟩ := travel74_data hR hβ3 h200 hA ht1 ht2
  have hw0 : 0 < w := by linarith
  have hh0 : 0 < h := by
    have : (0 : ℝ) < w ^ 20 := by positivity
    linarith
  have hv := travel74_hv hd1 hn200 hlo hw64 h4w hKw hB
  have hV : 0 < (k : ℝ) * (7 * d * h) := by
    have : (0 : ℝ) < k := by exact_mod_cast hk1
    positivity
  have hT := hTf n₁ hn₁ β n t₀ hβtf hR Ωe Pe Np hNp t ht1 ht2
  have htail : Pe.real {ω | ∃ s : ℝ≥0, s ≤ h.toNNReal ∧ w ^ 12 ≤
      ‖regenWalk (fun j => copyEnv (Np ω) j) (s : ℝ)‖} ≤ Real.exp (-(cTf * (n : ℝ) ^ 3)) := by
    have := hNp.isProbabilityMeasure
    refine le_trans (measureReal_mono ?_) hT
    rintro ω ⟨s, hs, hK⟩
    refine ⟨s, ?_, ?_⟩
    · rw [ht23]; exact ((Real.le_toNNReal_iff_coe_le hh0.le).1 hs).trans hhi
    · rw [ht25]; exact hK
  have hkh_le : (k : ℝ) * h ≤ indScale t₀ n := by
    rw [hkh, hw30]; exact ht2
  have key := step_travel_engine hd hCor hR hβc hβ12 hk1 h1 h2 hkh_le
    (K := w ^ 12) (x := (n : ℝ) ^ 2 * w ^ 15 / 4) (v := 7 * d * h)
    (p := Real.exp (-(cTf * (n : ℝ) ^ 3))) (by positivity) (by positivity) hv hV hNp htail
  have htn1 : (1 : ℝ) ≤ indScale t₀ n := (travel_time_bounds ht0 ht1 ht2).2.2.2
  have hrad := travel74_radius (n := n) k hd (by linarith) hw64 hk2 htn1 htnw
  have hfm : (n : ℝ) ^ 3 ≤ ((n : ℝ) ^ 2 * w ^ 15 / 4) ^ 2 / (2 * ((k : ℝ) * (7 * d * h) +
      w ^ 12 * ((n : ℝ) ^ 2 * w ^ 15 / 4) / 3)) := by
    have := freedman_exponent_74 (w := w) (n := (n : ℝ)) (d := (d : ℝ)) (by linarith) hdn' hd1
      hw3 hw0
    have e : (k : ℝ) * (7 * d * h) = 7 * d * w ^ 30 := by rw [← hkh]; ring
    rw [e]; exact this
  have ht_pos : 0 < t := lt_of_lt_of_le (by positivity) (travel_time_bounds ht0 ht1 ht2).1
  have hsub : {ω | ∃ s : ℝ≥0, (s : ℝ) ≤ t ∧ (n : ℝ) ^ 2 * Real.sqrt t ≤
      ‖regenWalk (fun j => copyEnv (Np ω) j) (s : ℝ)‖} ⊆
      {ω | ∃ s : ℝ≥0, (s : ℝ) ≤ k * h ∧ (k : ℝ) * indScale t₀ n ^ (2 * heavyEps d) +
        w ^ 12 + (n : ℝ) ^ 2 * w ^ 15 / 4 ≤ ‖regenWalk (fun j => copyEnv (Np ω) j) (s : ℝ)‖} := by
    rintro ω ⟨s, hs, hts⟩
    refine ⟨s, ?_, ?_⟩
    · rw [hkh, hw30]; exact hs
    · rw [hsq] at hts; exact hrad.trans hts
  have hn4 : (n : ℝ) < 4 ^ n := by exact_mod_cast Nat.lt_pow_self (by norm_num : 1 < 4)
  have hexpn := travel_exp_neg_le_aux (c' := c') hc'1 ((n : ℝ) ^ 3) (by positivity)
  have hk4 : (k : ℝ) ≤ 2 * 4 ^ n := by
    have : (2 : ℝ) * w ^ 10 ≤ 2 * 4 ^ n := by linarith
    exact hk2.trans this
  have hp : Real.exp (-(cTf * (n : ℝ) ^ 3)) ≤ Real.exp (-(c' * (n : ℝ) ^ 3)) := by
    apply Real.exp_le_exp.2
    have h3 : 0 ≤ (n : ℝ) ^ 3 := by positivity
    linarith [mul_le_mul_of_nonneg_right hc'tf h3]
  have hX : 2 * (d : ℝ) * Real.exp (-(((n : ℝ) ^ 2 * w ^ 15 / 4) ^ 2 /
      (2 * ((k : ℝ) * (7 * d * h) + w ^ 12 * ((n : ℝ) ^ 2 * w ^ 15 / 4) / 3)))) ≤
      2 * d * Real.exp (-(c' * (n : ℝ) ^ 3)) :=
    mul_le_mul_of_nonneg_left ((Real.exp_le_exp.2 (neg_le_neg hfm)).trans hexpn) (by positivity)
  have := hNp.isProbabilityMeasure
  exact (measureReal_mono hsub).trans (key.trans (travel_sum_le hc'cat hp hk4
    ((by exact_mod_cast (by omega : d ≤ n) : (d : ℝ) ≤ n).trans hn4.le) hC hX hk1))

end ElboimSly.Paper.Step
