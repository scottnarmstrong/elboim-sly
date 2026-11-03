/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Brownian.TubeBook
import Mathlib

/-!
# The tube lemma, basic form

Tube lemma, basic form.

* `tubeSet`: the path set `𝔗`, defined with the countable dense subset of `[0,T]`;
* `tubeH`, `tubeC0`: the constants `H = max {20K, 16000}` and `c₀(d,K) = exp(-0.04 H d (HK+1))`;
* `tube_basic`: `P(B ∈ 𝔗) ≥ c₀(d, K)`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace ElboimSly.Brownian

/-- Tube lemma, basic form. `H = max {20 K, 16000}`. -/
noncomputable def tubeH (K : ℝ) : ℝ := max (20 * K) 16000

/-- Tube lemma, basic form. `c₀(d,K) = exp(-0.04 H d (H K + 1))`. -/
noncomputable def tubeC0 (d : ℕ) (K : ℝ) : ℝ :=
  Real.exp (-(4 / 100 * tubeH K * d * (tubeH K * K + 1)))

/-- The tube path set: within `ρ` of `f` on the countable dense subset of `[0,T]`, and within
`ρ/10` of `f` at time `T`. -/
def tubeSet (d : ℕ) (x : Fin d → ℝ) (f : ℝ → Fin d → ℝ) (ρ : ℝ) (T : ℝ≥0) : Set (PathSpace d) :=
  {w | (∀ u ∈ denseSub (Set.Icc (0 : ℝ≥0) T), ‖x + w u - f u‖ ≤ ρ) ∧ ‖x + w T - f T‖ ≤ ρ / 10}

section Main

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {d : ℕ}
  {B : ℝ≥0 → Ω → (Fin d → ℝ)} {x : Fin d → ℝ} {f : ℝ → Fin d → ℝ} {h : ℝ≥0} {ρ : ℝ}

omit mΩ in
lemma tubeE_antitone {m n : ℕ} (hmn : m ≤ n) : tubeE B x f h ρ n ⊆ tubeE B x f h ρ m := by
  induction n, hmn using Nat.le_induction with
  | base => exact le_rfl
  | succ n _ ih => exact Set.inter_subset_left.trans ih

omit mΩ in
lemma tubeE_subset_tubeS {k n : ℕ} (hk : k < n) : tubeE B x f h ρ n ⊆ tubeS B x f h ρ k :=
  (tubeE_antitone (x := x) (f := f) (h := h) (ρ := ρ) (B := B) (by omega : k + 1 ≤ n)).trans
    Set.inter_subset_right

/-- Inclusion of the final event of the chain in the tube. -/
theorem tubeE_subset_tube (hB : IsStandardBrownianMotion d B P) {N : ℕ} (hN12 : 12 ≤ N)
    (hρ : 0 < ρ) {K : ℝ} (hx : ‖x - f 0‖ ≤ 3 * ρ / 5) (hh : 0 < (h : ℝ))
    (hLip : ∀ u ∈ Set.Icc (0 : ℝ) ((N : ℝ) * h), ∀ v ∈ Set.Icc (0 : ℝ) ((N : ℝ) * h),
      ‖f u - f v‖ ≤ K / ρ * |u - v|)
    (hKh : K / ρ * h ≤ ρ / 20) :
    ∀ ω ∈ tubeE B x f h ρ N, pathMap B ω ∈ tubeSet d x f ρ ((N : ℝ≥0) * h) := by
  intro ω hω
  obtain ⟨herr, -⟩ := tubeE_errors hB hN12 hρ hx hLip hKh N le_rfl ω hω
  have hcont : Continuous fun t => B t ω := (hB.continuous_zero ω).1
  refine ⟨fun u hu => ?_, ?_⟩
  · have huT : u ≤ (N : ℝ≥0) * h := (denseSub_subset _ hu).2
    have hN0 : 0 < N := by omega
    -- the grid interval containing `u`
    obtain ⟨k, hkN, hku, huk⟩ : ∃ k : ℕ, k < N ∧ (k : ℝ≥0) * h ≤ u ∧ u ≤ ((k : ℝ≥0) + 1) * h := by
      by_cases hfl : ⌊(u : ℝ) / h⌋₊ ≤ N - 1
      · refine ⟨⌊(u : ℝ) / h⌋₊, by omega, ?_, ?_⟩
        · rw [← NNReal.coe_le_coe]
          have := Nat.floor_le (show 0 ≤ (u : ℝ) / h by positivity)
          rw [le_div_iff₀ hh] at this
          push_cast; exact this
        · rw [← NNReal.coe_le_coe]
          have := Nat.lt_floor_add_one ((u : ℝ) / h)
          rw [div_lt_iff₀ hh] at this
          push_cast; exact this.le
      · obtain ⟨k, hkN⟩ : ∃ k, N = k + 1 := ⟨N - 1, by omega⟩
        have hNR : (N : ℝ) = k + 1 := by rw [hkN]; push_cast; ring
        refine ⟨k, by omega, ?_, ?_⟩
        · rw [← NNReal.coe_le_coe]
          have h1 : (N : ℝ) ≤ ⌊(u : ℝ) / h⌋₊ := by exact_mod_cast (by omega : N ≤ ⌊(u : ℝ) / h⌋₊)
          have h2 := Nat.floor_le (show 0 ≤ (u : ℝ) / h by positivity)
          rw [le_div_iff₀ hh] at h2
          push_cast
          nlinarith
        · rw [← NNReal.coe_le_coe]
          have hu' : (u : ℝ) ≤ (N : ℝ) * h := by exact_mod_cast huT
          push_cast
          rw [hNR] at hu'
          exact hu'
    have hSk : ω ∈ tubeS B x f h ρ k := tubeE_subset_tubeS hkN hω
    rw [tubeS_eq] at hSk
    obtain ⟨hsup, -⟩ := hSk
    have hgc : Continuous fun v : ℝ≥0 => ‖B ((k : ℝ≥0) * h + v) ω - B ((k : ℝ≥0) * h) ω‖ :=
      ((hcont.comp (continuous_const.add continuous_id)).sub continuous_const).norm
    have hall := le_on_of_denseSub (J := Set.Icc (0 : ℝ≥0) h) Set.ordConnected_Icc hgc hsup
    have hv : u - (k : ℝ≥0) * h ∈ Set.Icc (0 : ℝ≥0) h := by
      refine ⟨zero_le, ?_⟩
      rw [tsub_le_iff_left]
      calc u ≤ ((k : ℝ≥0) + 1) * h := huk
        _ = _ := by ring
    have hb := hall _ hv
    rw [add_tsub_cancel_of_le hku] at hb
    have hek := herr k (by omega)
    have hz := tubeZ_norm_le (x - f 0) k
    have hf1 : ‖f u - f ((k : ℝ≥0) * h : ℝ≥0)‖ ≤ ρ / 20 := by
      have hu' : (u : ℝ) ≤ (N : ℝ) * h := by exact_mod_cast huT
      have hku' : (((k : ℝ≥0) * h : ℝ≥0) : ℝ) ≤ u := by exact_mod_cast hku
      have hk0 : (0 : ℝ) ≤ (((k : ℝ≥0) * h : ℝ≥0) : ℝ) := NNReal.coe_nonneg _
      have := hLip u ⟨u.2, hu'⟩ _ ⟨hk0, hku'.trans hu'⟩
      refine this.trans (le_trans ?_ hKh)
      have hKρ : 0 ≤ K / ρ := by
        by_contra hneg
        have := hLip 0 ⟨le_rfl, by positivity⟩ ((h : ℝ)) ⟨hh.le, by
          have : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
          nlinarith⟩
        have h0 : 0 ≤ ‖f 0 - f h‖ := norm_nonneg _
        have : K / ρ * |(0 : ℝ) - h| < 0 := by
          rw [zero_sub, abs_neg, abs_of_pos hh]; exact mul_neg_of_neg_of_pos (not_le.1 hneg) hh
        linarith
      refine mul_le_mul_of_nonneg_left ?_ hKρ
      rw [abs_of_nonneg (by linarith)]
      have : (u : ℝ) ≤ (((k : ℝ≥0) + 1) * h : ℝ≥0) := by exact_mod_cast huk
      push_cast at this ⊢
      nlinarith
    have eq : x + B u ω - f u = (tubeErr B x f h k ω + tubeZ (x - f 0) k) +
        (B u ω - B ((k : ℝ≥0) * h) ω) - (f u - f ((k : ℝ≥0) * h : ℝ≥0)) := by
      simp only [tubeErr]; abel
    show ‖x + B u ω - f u‖ ≤ ρ
    rw [eq]
    calc _ ≤ ‖tubeErr B x f h k ω + tubeZ (x - f 0) k‖ + ‖B u ω - B ((k : ℝ≥0) * h) ω‖ +
          ‖f u - f ((k : ℝ≥0) * h : ℝ≥0)‖ := by
          refine (norm_sub_le _ _).trans ?_
          gcongr
          exact norm_add_le _ _
      _ ≤ (ρ / 20 + 3 * ρ / 5) + ρ / 4 + ρ / 20 := by
          gcongr
          exact (norm_add_le _ _).trans (add_le_add hek (hz.trans hx))
      _ ≤ ρ := by linarith
  · have hN := herr N le_rfl
    have : x + B ((N : ℝ≥0) * h) ω - f (((N : ℝ≥0) * h : ℝ≥0)) = tubeErr B x f h N ω := by
      simp only [tubeErr, tubeZ_eq_zero (x - f 0) hN12]; simp
    simp only [pathMap]
    rw [this]
    linarith

/-- Tube lemma, basic form. For a standard `d`-dimensional Brownian motion `B`,
`P(B ∈ 𝔗) ≥ c₀(d,K)`, where `𝔗` is the tube set of `tubeSet`. -/
theorem tube_basic [IsProbabilityMeasure P] (hB : IsStandardBrownianMotion d B P) {K : ℝ}
    (hK : 1 ≤ K) (hρ : 0 < ρ) {T : ℝ≥0} (hT1 : ρ ^ 2 / K ≤ T) (hT2 : (T : ℝ) ≤ K * ρ ^ 2)
    (hf : ∀ u ∈ Set.Icc (0 : ℝ) T, ∀ v ∈ Set.Icc (0 : ℝ) T, ‖f u - f v‖ ≤ K / ρ * |u - v|)
    (hx : ‖x - f 0‖ ≤ 3 * ρ / 5) :
    ENNReal.ofReal (tubeC0 d K) ≤ P {ω | pathMap B ω ∈ tubeSet d x f ρ T} := by
  set H := tubeH K with hHdef
  have hH1 : 20 * K ≤ H := le_max_left _ _
  have hH2 : (16000 : ℝ) ≤ H := le_max_right _ _
  have hK0 : 0 < K := by linarith
  have hρ2 : 0 < ρ ^ 2 := by positivity
  have hTpos : 0 < (T : ℝ) := lt_of_lt_of_le (by positivity) hT1
  have hHT : 20 ≤ H * T / ρ ^ 2 := by
    rw [le_div_iff₀ hρ2]
    have h1 : ρ ^ 2 / K * H ≤ T * H := mul_le_mul_of_nonneg_right hT1 (by linarith)
    have : ρ ^ 2 / K * H = ρ ^ 2 * (H / K) := by ring
    have h2 : 20 ≤ H / K := by rw [le_div_iff₀ hK0]; linarith
    nlinarith
  set N : ℕ := ⌈H * T / ρ ^ 2⌉₊ with hNdef
  have hN1 : H * T / ρ ^ 2 ≤ N := Nat.le_ceil _
  have hN2 : (N : ℝ) < H * T / ρ ^ 2 + 1 := Nat.ceil_lt_add_one (by linarith)
  have hN20 : (20 : ℝ) ≤ N := by linarith
  have hN12 : 12 ≤ N := by
    have : (12 : ℝ) ≤ N := by linarith
    exact_mod_cast this
  have hNpos : (0 : ℝ) < N := by linarith
  set h : ℝ≥0 := T / N with hh
  have hhR : (h : ℝ) = T / N := by simp [hh]
  have hh0 : (0 : ℝ) < h := by rw [hhR]; positivity
  have hhne : h ≠ 0 := by intro h0; rw [h0] at hh0; simp at hh0
  have hNhR : (N : ℝ) * h = T := by rw [hhR]; field_simp
  have hNh : (N : ℝ≥0) * h = T := by
    rw [← NNReal.coe_inj]; push_cast; exact hNhR
  have hΛ1 : H ≤ ρ ^ 2 / h := by
    rw [hhR, div_div_eq_mul_div, le_div_iff₀ hTpos]
    rw [div_le_iff₀ hρ2] at hN1
    nlinarith
  have hΛ2 : ρ ^ 2 / h ≤ 2 * H := by
    rw [hhR, div_div_eq_mul_div, div_le_iff₀ hTpos]
    have h1 : (N : ℝ) ≤ 2 * (H * T / ρ ^ 2) := by linarith
    rw [← mul_div_assoc, le_div_iff₀ hρ2] at h1
    nlinarith
  have hKh : K / ρ * h ≤ ρ / 20 := by
    have h1 : (h : ℝ) ≤ ρ ^ 2 / H := by
      rw [hhR, div_le_div_iff₀ hNpos (by linarith)]
      rw [div_le_iff₀ hρ2] at hN1
      nlinarith
    calc K / ρ * h ≤ K / ρ * (ρ ^ 2 / H) := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = K * ρ / H := by field_simp
      _ ≤ ρ / 20 := by
        rw [div_le_div_iff₀ (by linarith) (by norm_num)]; nlinarith
  have hLip : ∀ u ∈ Set.Icc (0 : ℝ) ((N : ℝ) * h), ∀ v ∈ Set.Icc (0 : ℝ) ((N : ℝ) * h),
      ‖f u - f v‖ ≤ K / ρ * |u - v| := by
    rw [hNhR]; exact hf
  have hΛ0 : 16000 ≤ ρ ^ 2 / h := by linarith
  set q : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-(ρ ^ 2 / h) / 50)) ^ d with hq
  have hchain : ∀ k ≤ N, q ^ k ≤ P (tubeE B x f h ρ k) := by
    intro k
    induction k with
    | zero => intro _; simp [tubeE]
    | succ k ih =>
      intro hk
      have hp : ∀ ω ∈ tubeE B x f h ρ k, ‖tubeP B x f h k ω‖ ≤ 3 * ρ / 20 := fun ω hω =>
        (tubeE_errors hB hN12 hρ hx hLip hKh k (by omega) ω hω).2 (by omega)
      calc q ^ (k + 1) = q * q ^ k := by ring
        _ ≤ q * P (tubeE B x f h ρ k) := mul_le_mul_right (ih (by omega)) _
        _ ≤ P (tubeE B x f h ρ (k + 1)) := tubeE_succ_prob hB hhne hρ hΛ0 k hp
  have hsub := tubeE_subset_tube hB hN12 hρ hx hh0 hLip hKh
  rw [hNh] at hsub
  refine le_trans ?_ (measure_mono (fun ω hω => hsub ω hω) |>.trans' (hchain N le_rfl))
  have hNK : (N : ℝ) ≤ H * K + 1 := by
    have : H * T / ρ ^ 2 ≤ H * K := by
      rw [div_le_iff₀ hρ2]; nlinarith
    linarith
  have h1 : tubeC0 d K ≤ (Real.exp (-(ρ ^ 2 / h) / 50)) ^ (d * N) := by
    rw [← Real.exp_nat_mul]
    unfold tubeC0
    refine Real.exp_le_exp.2 ?_
    push_cast
    have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    have hΛ50 : (ρ ^ 2 / h) / 50 ≤ 4 / 100 * H := by linarith
    have e : (d : ℝ) * N * (-(ρ ^ 2 / h) / 50) = -((ρ ^ 2 / h) / 50 * (d * N)) := by ring
    rw [e, neg_le_neg_iff]
    have hnn : 0 ≤ (ρ ^ 2 / h) / 50 := by positivity
    calc (ρ ^ 2 / h) / 50 * (d * N) ≤ 4 / 100 * H * (d * N) :=
          mul_le_mul_of_nonneg_right hΛ50 (by positivity)
      _ ≤ 4 / 100 * H * (d * (H * K + 1)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hNK hd0) (by positivity)
      _ = _ := by ring
  rw [hq, ← pow_mul, ← ENNReal.ofReal_pow (Real.exp_pos _).le]
  exact ENNReal.ofReal_le_ofReal h1

end Main

end ElboimSly.Brownian
