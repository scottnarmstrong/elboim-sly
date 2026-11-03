/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Base.H1Cover
public import ElboimSly.Foundations.Brownian.Occupation
public import Mathlib

/-!
# (H1) at the base: the occupation event `𝒜_occ`

ES22 Lemma 8.1, Step 1, the bound for `𝒜_occ` (deviations F27, F47, F48).

* `h1_occ_prob`: the probability that some `(x, m)` with `‖x‖ < R` and `m₀ ≤ m ≤ M` violates
  `N_{x,m} ≤ m^{2.1}` is at most `2 (2R+1)^d (M+1) exp(-c_occ (b-1)^{1/10}/4)`.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Paper

open ElboimSly.Brownian

variable {d : ℕ}

open Classical in
theorem tsum_indicator_eq_encard (A : Set ℕ) :
    ∑' i : ℕ, (if i ∈ A then (1 : ℝ≥0∞) else 0) = (A.encard : ℝ≥0∞) := by
  classical
  rw [← ENNReal.tsum_set_one A, tsum_subtype A (fun _ => (1 : ℝ≥0∞))]
  congr 1

theorem finite_ncard_of_encard_le {A : Set ℕ} {y : ℝ} (hy : 0 ≤ y)
    (h : (A.encard : ℝ≥0∞) ≤ ENNReal.ofReal y) : A.Finite ∧ (A.ncard : ℝ) ≤ y := by
  have hne : A.encard ≠ ⊤ := by
    intro htop
    rw [htop] at h
    simp at h
  have hfin : A.Finite := Set.encard_ne_top_iff.1 hne
  refine ⟨hfin, ?_⟩
  have e : ((A.ncard : ℕ) : ℝ≥0∞) = (A.encard : ℝ≥0∞) := by
    rw [← hfin.cast_ncard_eq]; simp
  rw [← e, ← ENNReal.ofReal_natCast, ENNReal.ofReal_le_ofReal_iff hy] at h
  exact h

/-- The good occupation property of the pair `(x, m)`. -/
def OccGood (B : ℝ≥0 → Fin d → ℝ) (x : Fin d → ℤ) (m : ℕ) : Prop :=
  (occSet B x m).Finite ∧ ((occSet B x m).ncard : ℝ) ≤ (m : ℝ) ^ (21 / 10 : ℝ)

open Classical in
theorem occ_bad_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → Fin d → ℝ} (hB : IsStandardBrownianMotion d B P) (hd : 3 ≤ d)
    (x : Fin d → ℤ) {m : ℕ} (hm : 1 ≤ m) :
    P {ω | ¬ OccGood (fun u => B u ω) x m} ≤
      ENNReal.ofReal (2 * Real.exp (-(cocc d) * ((m : ℝ) ^ (1 / 10 : ℝ) / 4))) := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hmpos : (0 : ℝ) < m := by linarith
  have hX : 0 ≤ (m : ℝ) ^ (1 / 10 : ℝ) / 4 := by positivity
  have hocc := occupation_le hB hd 0 (latR x) (σ := Real.sqrt 2) (r := 2 * m)
    (by rw [Real.one_le_sqrt]; norm_num) (by linarith)
    (D := Metric.closedBall (latR x) (2 * m)) Metric.isClosed_closedBall.measurableSet
    le_rfl hX
  refine le_trans (measure_mono ?_) hocc
  intro ω hω
  have hpow : (m : ℝ) ^ (1 / 10 : ℝ) / 4 * (2 * m) ^ 2 = (m : ℝ) ^ (21 / 10 : ℝ) := by
    have : (m : ℝ) ^ (21 / 10 : ℝ) = (m : ℝ) ^ (1 / 10 : ℝ) * (m : ℝ) ^ (2 : ℝ) := by
      rw [← Real.rpow_add hmpos]; norm_num
    rw [this, Real.rpow_two]; ring
  show ENNReal.ofReal ((m : ℝ) ^ (1 / 10 : ℝ) / 4 * (2 * m) ^ 2) <
    ∑' i : ℕ, {ω | 0 + Real.sqrt 2 • B (i : ℝ≥0) ω ∈ Metric.closedBall (latR x) (2 * m)}.indicator
      (1 : Ω → ℝ≥0∞) ω
  rw [hpow]
  have e : (∑' i : ℕ, {ω | 0 + Real.sqrt 2 • B (i : ℝ≥0) ω ∈
      Metric.closedBall (latR x) (2 * m)}.indicator (1 : Ω → ℝ≥0∞) ω) =
      ∑' i : ℕ, (if i ∈ occSet (fun u => B u ω) x m then (1 : ℝ≥0∞) else 0) := by
    congr 1
    funext i
    simp only [Set.indicator_apply, mem_ofPred_eq, Pi.one_apply, occSet, zero_add,
      Metric.mem_closedBall, dist_eq_norm]
    exact if_congr Iff.rfl rfl rfl
  rw [e, tsum_indicator_eq_encard]
  by_contra hcon
  push Not at hcon
  exact hω (finite_ncard_of_encard_le (by positivity) hcon)

/-- The union bound over `(x, m)`. -/
theorem h1_occ_prob {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → Fin d → ℝ} (hB : IsStandardBrownianMotion d B P) (hd : 3 ≤ d)
    {R : ℝ} (hR : 0 ≤ R) {m0 M : ℕ} {b : ℝ} (hb : 2 ≤ b) (hm0 : b - 1 ≤ m0) :
    P {ω | ∃ x : Fin d → ℤ, ‖x‖ < R ∧ ∃ m : ℕ, m0 ≤ m ∧ m ≤ M ∧
        ¬ OccGood (fun u => B u ω) x m} ≤
      ENNReal.ofReal (2 * (2 * R + 1) ^ d * ((M : ℝ) + 1) *
        Real.exp (-(cocc d) * (b - 1) ^ (1 / 10 : ℝ) / 4)) := by
  have hm01 : (1 : ℝ) ≤ m0 := by linarith
  set E : ℝ := Real.exp (-(cocc d) * (b - 1) ^ (1 / 10 : ℝ) / 4) with hE
  have hsub : {ω | ∃ x : Fin d → ℤ, ‖x‖ < R ∧ ∃ m : ℕ, m0 ≤ m ∧ m ≤ M ∧
      ¬ OccGood (fun u => B u ω) x m} ⊆
      ⋃ x ∈ ballBox d R, ⋃ m ∈ Finset.Icc m0 M, {ω | ¬ OccGood (fun u => B u ω) x m} := by
    rintro ω ⟨x, hx, m, h1, h2, h3⟩
    simp only [mem_iUnion]
    exact ⟨x, mem_ballBox hx, m,
      Finset.mem_Icc.2 ⟨h1, h2⟩, h3⟩
  have hterm : ∀ x : Fin d → ℤ, ∀ m ∈ Finset.Icc m0 M,
      P {ω | ¬ OccGood (fun u => B u ω) x m} ≤ ENNReal.ofReal (2 * E) := by
    intro x m hm
    have hm0m : m0 ≤ m := (Finset.mem_Icc.1 hm).1
    have hmm : (b - 1 : ℝ) ≤ m := hm0.trans (by exact_mod_cast hm0m)
    refine (occ_bad_le hB hd x (by
      have : (1 : ℝ) ≤ m := by linarith
      exact_mod_cast this)).trans (ENNReal.ofReal_le_ofReal ?_)
    have h1 : (b - 1) ^ (1 / 10 : ℝ) ≤ (m : ℝ) ^ (1 / 10 : ℝ) :=
      Real.rpow_le_rpow (by linarith) hmm (by norm_num)
    have hc := cocc_pos d
    have : Real.exp (-(cocc d) * ((m : ℝ) ^ (1 / 10 : ℝ) / 4)) ≤ E := by
      rw [hE]
      apply Real.exp_le_exp.2
      nlinarith
    linarith
  calc P {ω | ∃ x : Fin d → ℤ, ‖x‖ < R ∧ ∃ m : ℕ, m0 ≤ m ∧ m ≤ M ∧
        ¬ OccGood (fun u => B u ω) x m}
      ≤ P (⋃ x ∈ ballBox d R, ⋃ m ∈ Finset.Icc m0 M, {ω | ¬ OccGood (fun u => B u ω) x m}) :=
        measure_mono hsub
    _ ≤ ∑ x ∈ ballBox d R, P (⋃ m ∈ Finset.Icc m0 M, {ω | ¬ OccGood (fun u => B u ω) x m}) :=
        measure_biUnion_finset_le _ _
    _ ≤ ∑ x ∈ ballBox d R, ∑ m ∈ Finset.Icc m0 M, P {ω | ¬ OccGood (fun u => B u ω) x m} :=
        Finset.sum_le_sum fun x _ => measure_biUnion_finset_le _ _
    _ ≤ ∑ _x ∈ ballBox d R, ∑ _m ∈ Finset.Icc m0 M, ENNReal.ofReal (2 * E) :=
        Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun m hm => hterm x m hm
    _ = ENNReal.ofReal (((ballBox d R).card : ℝ) * ((M + 1 - m0 : ℕ) : ℝ) * (2 * E)) := by
        simp only [Finset.sum_const, nsmul_eq_mul, Nat.card_Icc]
        rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ ((ballBox d R).card : ℝ) *
            ((M + 1 - m0 : ℕ) : ℝ)),
          ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ ((ballBox d R).card : ℝ)),
          ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]
        ring
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ?_
        have h1 := card_ballBox d hR
        have h2 : ((M + 1 - m0 : ℕ) : ℝ) ≤ (M : ℝ) + 1 := by
          have : M + 1 - m0 ≤ M + 1 := Nat.sub_le _ _
          exact_mod_cast this
        have hE0 : 0 ≤ E := (Real.exp_pos _).le
        calc ((ballBox d R).card : ℝ) * ((M + 1 - m0 : ℕ) : ℝ) * (2 * E)
            ≤ (2 * R + 1) ^ d * ((M : ℝ) + 1) * (2 * E) := by gcongr
          _ = 2 * (2 * R + 1) ^ d * ((M : ℝ) + 1) * E := by ring

end ElboimSly.Paper

end
