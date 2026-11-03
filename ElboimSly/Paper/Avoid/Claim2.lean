/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Avoid.Claim2Window
public import ElboimSly.Foundations.Cyclic.CycFast
public import Mathlib

/-!
# ES22 §4: Claim 4.2

ES22 Claim 4.2 (§4). Under (S1)–(S2), for every real `L` with
`4^{n₀+1} ≤ L ≤ 4ⁿ` and every `A ⊆ {‖u‖ ≥ L}` with `|A ∩ [-r, r]^d| ≤ r^{8/3}` for `r ≥ L`,
`P(∀ s ≤ 4ⁿ, W(s) ∉ A) ≥ 1 - C L^{-1/30}` with `C` depending only on `d`.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Paper

open ElboimSly.Cyclic

/-- The union bound over windows: the bad event `∃ s ≤ 4ⁿ, W(s) ∈ A` is covered by the initial
segment and the windows `ℓ₀ < ℓ ≤ n`. -/
theorem bad_subset {d : ℕ} {Ω : Type*} (W : Ω → ℝ → Fin d → ℤ) (A : Set (Fin d → ℤ)) {ℓ₀ n : ℕ} :
    {ω | ∃ s : ℝ, 0 ≤ s ∧ s ≤ (4 : ℝ) ^ n ∧ W ω s ∈ A} ⊆
      {ω | ∃ s : ℝ, 0 ≤ s ∧ s ≤ (4 : ℝ) ^ ℓ₀ ∧ W ω s ∈ A} ∪
        ⋃ ℓ ∈ Finset.Ioc ℓ₀ n, {ω | ∃ s : ℝ, (4 : ℝ) ^ (ℓ - 1) ≤ s ∧ s ≤ 4 ^ ℓ ∧ W ω s ∈ A} := by
  intro ω ⟨s, hs0, hsn, hsA⟩
  by_cases h : s ≤ (4 : ℝ) ^ ℓ₀
  · exact Or.inl ⟨s, hs0, h, hsA⟩
  · right
    push Not at h
    have h1 : 1 < s := lt_of_le_of_lt (one_le_pow₀ (by norm_num)) h
    obtain ⟨a, b⟩ := avoidLevel_spec h1
    have hge := avoidLevel_ge h
    have hlt := avoidLevel_lt h1 hsn
    simp only [mem_iUnion, Finset.mem_Ioc, mem_ofPred_eq]
    refine ⟨avoidLevel s + 1, ⟨by omega, by omega⟩, s, ?_, b, hsA⟩
    simpa using a.le

section

variable {d : ℕ}

theorem boxExpr_nonneg (d ℓ : ℕ) : 0 ≤ boxExpr d ℓ := by
  unfold boxExpr; positivity

/-- **ES22 Claim 4.2** (probability of the bad event). -/
theorem es4_claim2_bad (hd : 5 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (β : ℝ) [Fact (0 < β)] (n₀ n : ℕ) (t₀ : ℝ),
      Es4Params d β n₀ n t₀ → ∀ {Ω : Type} [MeasurableSpace Ω] (Pr : Measure Ω)
        (N : Ω → Measure (CycS ℕ d β)), IsPoissonPointProcess N (cycIntensity ℕ d β) Pr →
        ∀ {L : ℝ}, (4 : ℝ) ^ (n₀ + 1) ≤ L → L ≤ (4 : ℝ) ^ n →
        ∀ {A : Set (Fin d → ℤ)}, (∀ u ∈ A, L ≤ ‖u‖) →
        (∀ r : ℝ, L ≤ r → ((A ∩ {u | ‖u‖ ≤ r}).ncard : ℝ) ≤ r ^ (8 / 3 : ℝ)) →
        Pr {ω | ∃ s : ℝ, 0 ≤ s ∧ s ≤ (4 : ℝ) ^ n ∧ avoidWalk N ω s ∈ A} ≤
          ENNReal.ofReal (C * L ^ (-(1 : ℝ) / 30)) := by
  obtain ⟨Cf, cf, hCf, hcf, hf⟩ := cyc_fast.{0} (d := d) (by omega)
  obtain ⟨K, hK, hKb⟩ := box_arith d hd
  obtain ⟨M1, hM1, hM1b⟩ := poly_mul_q_bdd (2 * d + 6)
  obtain ⟨M2, hM2, hM2b⟩ := exp_quad_le hcf
  set C1 : ℝ := 3 + K * M1 + Cf * M2 with hC1
  have hq0 := qSeries_pos
  have hq1 := qSeries_lt_one
  set C2 : ℝ := 3 + C1 / (1 - qSeries) with hC2
  have hC1p : 0 < C1 := by positivity
  have hC2p : 0 < C2 := by
    have : 0 < 1 - qSeries := by linarith
    positivity
  refine ⟨2 * C2, by positivity, ?_⟩
  intro β _ n₀ n t₀ hp Ω _ Pr N hN L hL1 hL2 A hA1 hA2
  have hβ1 : (1 : ℝ) ≤ β := le_trans (by norm_num) hp.beta_sigma
  -- the window estimate in terms of `q^ℓ`
  have hfast : ∀ {L' t : ℝ}, 1 ≤ L' → 1 ≤ t →
      Pr.real {ω | cycTfast (avoidEnv N ω) L' ≤ ENNReal.ofReal t} ≤
        Cf * t ^ 2 * Real.exp (-(cf * L')) := by
    intro L' t h1 h2
    have := hf β hβ1 Ω Pr N hN h1 h2
    simpa only [avoidEnv_eq_cycSlice] using this
  have hwin : ∀ ℓ : ℕ, n₀ < ℓ → ℓ ≤ n →
      Pr {ω | ∃ s : ℝ, (4 : ℝ) ^ (ℓ - 1) ≤ s ∧ s ≤ 4 ^ ℓ ∧ avoidWalk N ω s ∈ A} ≤
        ENNReal.ofReal (C1 * qSeries ^ ℓ) := by
    intro ℓ h1 h2
    have hℓ1 : 1 ≤ ℓ := by have := hp.eight_le; omega
    refine (es4_window hp hN hfast hA1 hA2 h1 h2).trans ?_
    rw [← ENNReal.ofReal_add (by positivity) (boxExpr_nonneg d ℓ),
      ← ENNReal.ofReal_add (add_nonneg (by positivity) (boxExpr_nonneg d ℓ)) (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have e1 : Real.exp (-(((ℓ - 1 : ℕ) : ℝ) ^ 2)) ≤ 3 * qSeries ^ ℓ := by
      have := exp_sq_le ℓ hℓ1
      rw [Nat.cast_sub hℓ1] at *
      simpa using this
    have e2 : boxExpr d ℓ ≤ K * M1 * qSeries ^ ℓ := by
      have h := hKb ℓ hℓ1
      unfold boxExpr
      refine h.trans ?_
      have hm := hM1b ℓ
      have hqp : 0 ≤ qSeries ^ ℓ := by positivity
      calc K * (ℓ : ℝ) ^ (2 * d + 6) * (qSeries ^ ℓ) ^ 2
          = K * ((ℓ : ℝ) ^ (2 * d + 6) * qSeries ^ ℓ) * qSeries ^ ℓ := by ring
        _ ≤ K * M1 * qSeries ^ ℓ := by gcongr
    have e3 : Cf * ((4 : ℝ) ^ ℓ) ^ 2 * Real.exp (-(cf * ((ℓ : ℝ) ^ 2))) ≤
        Cf * M2 * qSeries ^ ℓ := by
      have h := hM2b ℓ
      have : ((4 : ℝ) ^ ℓ) ^ 2 = 16 ^ ℓ := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
      rw [this]
      calc Cf * 16 ^ ℓ * Real.exp (-(cf * ((ℓ : ℝ) ^ 2)))
          = Cf * ((16 : ℝ) ^ ℓ * Real.exp (-(cf * ((ℓ : ℝ) ^ 2)))) := by ring
        _ ≤ Cf * (M2 * qSeries ^ ℓ) := by gcongr
        _ = _ := by ring
    rw [hC1]
    nlinarith
  -- choose ℓ₀
  have hL0 : 1 ≤ L := by
    refine le_trans ?_ hL1
    exact one_le_pow₀ (by norm_num)
  set ℓ₀ : ℕ := Nat.log 4 ⌊L⌋₊ with hℓ₀
  have hfl : 1 ≤ ⌊L⌋₊ := Nat.le_floor (by simpa using hL0)
  have hlo : (4 : ℕ) ^ ℓ₀ ≤ ⌊L⌋₊ := Nat.pow_log_le_self 4 (by omega)
  have hhi : ⌊L⌋₊ < (4 : ℕ) ^ (ℓ₀ + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
  have hlo' : (4 : ℝ) ^ ℓ₀ ≤ L := by
    have : ((4 : ℕ) ^ ℓ₀ : ℝ) ≤ ⌊L⌋₊ := by exact_mod_cast hlo
    exact (by simpa using this : (4 : ℝ) ^ ℓ₀ ≤ ⌊L⌋₊).trans (Nat.floor_le (by linarith))
  have hhi' : L < (4 : ℝ) ^ (ℓ₀ + 1) := by
    have h1 : L < ⌊L⌋₊ + 1 := Nat.lt_floor_add_one L
    have h2 : (⌊L⌋₊ : ℝ) + 1 ≤ ((4 : ℕ) ^ (ℓ₀ + 1) : ℕ) := by exact_mod_cast hhi
    simpa using h1.trans_le h2
  have hℓ₀n₀ : n₀ + 1 ≤ ℓ₀ := by
    apply Nat.le_log_of_pow_le (by norm_num)
    apply Nat.le_floor
    simpa using hL1
  have hℓ₀n : ℓ₀ ≤ n := by
    have : 4 ^ ℓ₀ ≤ 4 ^ n := by
      have h : (4 : ℝ) ^ ℓ₀ ≤ 4 ^ n := hlo'.trans hL2
      exact_mod_cast h
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 this
  -- initial segment
  have h0 : Pr {ω | ∃ s : ℝ, 0 ≤ s ∧ s ≤ (4 : ℝ) ^ ℓ₀ ∧ avoidWalk N ω s ∈ A} ≤
      ENNReal.ofReal (3 * qSeries ^ ℓ₀) := by
    have hℓ1 : 1 ≤ ℓ₀ := by omega
    have hb := es4_hyp_b hp hN (T := (4 : ℝ) ^ ℓ₀)
      (pow_lt_pow_right₀ (by norm_num) (by omega)) (pow_le_pow_right₀ (by norm_num) hℓ₀n)
    rw [avoidLevel_pow ℓ₀ hℓ1] at hb
    have hsq : Real.sqrt ((4 : ℝ) ^ ℓ₀) = 2 ^ ℓ₀ := by
      rw [show (4 : ℝ) ^ ℓ₀ = (2 ^ ℓ₀) ^ 2 by rw [← pow_mul, mul_comm, pow_mul]; norm_num]
      exact Real.sqrt_sq (by positivity)
    rw [hsq] at hb
    refine le_trans (measure_mono ?_) (hb.trans (ENNReal.ofReal_le_ofReal ?_))
    · rintro ω ⟨s, hs0, hs1, hsA⟩
      have hR : ((ℓ₀ - 1 : ℕ) : ℝ) ^ 2 * 2 ^ ℓ₀ ≤ ‖avoidWalk N ω s‖ := by
        have h1 : ((ℓ₀ - 1 : ℕ) : ℝ) ^ 2 ≤ 2 ^ ℓ₀ := by
          rcases sq_pred_le_two_pow ℓ₀ with h | h
          · rw [Nat.cast_sub hℓ1]; simpa using h
          · omega
        calc ((ℓ₀ - 1 : ℕ) : ℝ) ^ 2 * 2 ^ ℓ₀ ≤ 2 ^ ℓ₀ * 2 ^ ℓ₀ := by gcongr
          _ = 4 ^ ℓ₀ := by rw [← mul_pow]; norm_num
          _ ≤ L := hlo'
          _ ≤ ‖avoidWalk N ω s‖ := hA1 _ hsA
      show ENNReal.ofReal _ ≤ _
      refine le_trans (ENNReal.ofReal_le_ofReal hR) ?_
      exact le_iSup_of_le (⟨s, hs0, hs1⟩ : Set.Icc (0 : ℝ) (4 ^ ℓ₀)) le_rfl
    · have := exp_sq_le ℓ₀ hℓ1
      rw [Nat.cast_sub hℓ1]
      simpa using this
  -- the union bound
  have hsum : Pr {ω | ∃ s : ℝ, 0 ≤ s ∧ s ≤ (4 : ℝ) ^ n ∧ avoidWalk N ω s ∈ A} ≤
      ENNReal.ofReal (C2 * qSeries ^ ℓ₀) := by
    refine (measure_mono (bad_subset (fun ω s => avoidWalk N ω s) A (ℓ₀ := ℓ₀) (n := n))).trans ?_
    refine (measure_union_le _ _).trans ?_
    have hw : Pr (⋃ ℓ ∈ Finset.Ioc ℓ₀ n,
        {ω | ∃ s : ℝ, (4 : ℝ) ^ (ℓ - 1) ≤ s ∧ s ≤ 4 ^ ℓ ∧ avoidWalk N ω s ∈ A}) ≤
        ENNReal.ofReal (C1 * qSeries ^ (ℓ₀ + 1) / (1 - qSeries)) := by
      refine (measure_biUnion_finset_le _ _).trans ?_
      calc _ ≤ ∑ ℓ ∈ Finset.Ioc ℓ₀ n, ENNReal.ofReal (C1 * qSeries ^ ℓ) :=
            Finset.sum_le_sum fun ℓ hℓ => hwin ℓ (by
              have := (Finset.mem_Ioc.1 hℓ).1; omega) (Finset.mem_Ioc.1 hℓ).2
        _ = ENNReal.ofReal (∑ ℓ ∈ Finset.Ioc ℓ₀ n, C1 * qSeries ^ ℓ) :=
            (ENNReal.ofReal_sum_of_nonneg fun ℓ _ => by positivity).symm
        _ ≤ _ := by
            apply ENNReal.ofReal_le_ofReal
            rw [← Finset.mul_sum, mul_div_assoc]
            exact mul_le_mul_of_nonneg_left (sum_Ioc_geom_le hq0 hq1 ℓ₀ n) hC1p.le
    refine add_le_add h0 hw |>.trans ?_
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have : C1 * qSeries ^ (ℓ₀ + 1) / (1 - qSeries) ≤ C1 / (1 - qSeries) * qSeries ^ ℓ₀ := by
      rw [pow_succ]
      have : 0 < 1 - qSeries := by linarith
      rw [div_mul_eq_mul_div, mul_comm C1, mul_assoc]
      apply div_le_div_of_nonneg_right _ this.le
      have : qSeries ^ ℓ₀ * qSeries ≤ qSeries ^ ℓ₀ := by
        nlinarith [pow_pos hq0 ℓ₀]
      nlinarith [pow_pos hq0 ℓ₀, hC1p]
    rw [hC2]
    nlinarith [pow_pos hq0 ℓ₀]
  -- conversion to `L^{-1/30}`
  refine hsum.trans (ENNReal.ofReal_le_ofReal ?_)
  have hLpos : 0 < L := by linarith
  have h2l : Real.sqrt L / 2 ≤ 2 ^ ℓ₀ := by
    have : Real.sqrt L ≤ 2 ^ (ℓ₀ + 1) := by
      apply Real.sqrt_le_iff.2
      refine ⟨by positivity, ?_⟩
      rw [show ((2 : ℝ) ^ (ℓ₀ + 1)) ^ 2 = 4 ^ (ℓ₀ + 1) by
        rw [← pow_mul, mul_comm, pow_mul]; norm_num]
      exact hhi'.le
    rw [pow_succ] at this
    linarith
  have hq : qSeries ^ ℓ₀ ≤ 2 * L ^ (-(1 : ℝ) / 30) := by
    rw [qSeries_pow]
    have hpos : 0 < Real.sqrt L / 2 := by positivity
    have e2 : (2 : ℝ) ^ (-(1 : ℝ) / 15) = ((2 : ℝ) ^ ((1 : ℝ) / 15))⁻¹ := by
      rw [← Real.rpow_neg (by norm_num)]; congr 1; ring
    have e3 : Real.sqrt L ^ (-(1 : ℝ) / 15) = L ^ (-(1 : ℝ) / 30) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hLpos.le]; congr 1; ring
    have e4 : (2 : ℝ) ^ ((1 : ℝ) / 15) ≤ 2 := by
      calc (2 : ℝ) ^ ((1 : ℝ) / 15) ≤ (2 : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        _ = 2 := Real.rpow_one 2
    calc ((2 : ℝ) ^ ℓ₀) ^ (-(1 : ℝ) / 15) ≤ (Real.sqrt L / 2) ^ (-(1 : ℝ) / 15) :=
          Real.rpow_le_rpow_of_nonpos hpos h2l (by norm_num)
      _ = L ^ (-(1 : ℝ) / 30) * (2 : ℝ) ^ ((1 : ℝ) / 15) := by
          rw [Real.div_rpow (Real.sqrt_nonneg _) (by norm_num), e2, e3, div_inv_eq_mul]
      _ ≤ L ^ (-(1 : ℝ) / 30) * 2 := by gcongr
      _ = 2 * L ^ (-(1 : ℝ) / 30) := by ring
  calc C2 * qSeries ^ ℓ₀ ≤ C2 * (2 * L ^ (-(1 : ℝ) / 30)) := by gcongr
    _ = 2 * C2 * L ^ (-(1 : ℝ) / 30) := by ring

end

end ElboimSly.Paper

end
