/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Avoid.Claim2Count
public import Mathlib

/-!
# ES22 §4, Claim 4.2: the window estimate

ES22 Claim 4.2, "Window `ℓ`". For `n₀ < ℓ ≤ n` and a set `A` of lattice points with
`|A ∩ [-r, r]^d| ≤ r^{8/3}` (`r ≥ L`) and `A ⊆ {‖u‖ ≥ L}`,
`P(∃ s ∈ [4^{ℓ-1}, 4^ℓ], W(s) ∈ A)` is at most the sum of three terms: the maximal bound
(the induction hypothesis at arbitrary times (b)), the integer-time bound (the induction hypothesis at arbitrary times (a) and a union bound), and the
probability that `t_fast(ℓ²) ≤ 4^ℓ` (ES22 Claim 2.3).
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Paper

open ElboimSly.Cyclic

/-- The integer-time bound `4^ℓ (3ℓ²)^d (2ℓ² 2^ℓ)^{8/3} (4^{ℓ-1})^{-d/2+1/10}`. -/
noncomputable def boxExpr (d ℓ : ℕ) : ℝ :=
  (4 : ℝ) ^ ℓ * ((3 * (ℓ : ℝ) ^ 2) ^ d * (2 * (ℓ : ℝ) ^ 2 * 2 ^ ℓ) ^ (8 / 3 : ℝ)) *
    ((4 : ℝ) ^ (ℓ - 1)) ^ (-(d : ℝ) / 2 + 1 / 10)

section

variable {d : ℕ} {β : ℝ} [Fact (0 < β)] {n₀ n : ℕ} {t₀ : ℝ} {Ω : Type} [MeasurableSpace Ω]
  {Pr : Measure Ω} {N : Ω → Measure (CycS ℕ d β)}

theorem sparse_ncard_le {A : Set (Fin d → ℤ)} {L : ℝ} (hA1 : ∀ u ∈ A, L ≤ ‖u‖)
    (hA2 : ∀ r : ℝ, L ≤ r → ((A ∩ {u | ‖u‖ ≤ r}).ncard : ℝ) ≤ r ^ (8 / 3 : ℝ)) {r : ℝ}
    (hr : 0 ≤ r) : ((A ∩ {u | ‖u‖ ≤ r}).ncard : ℝ) ≤ r ^ (8 / 3 : ℝ) := by
  by_cases h : L ≤ r
  · exact hA2 r h
  · have : A ∩ {u | ‖u‖ ≤ r} = ∅ := by
      ext u
      simp only [mem_inter_iff, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and, not_le]
      intro hu
      have := hA1 u hu
      linarith [not_le.1 h]
    rw [this]
    simp only [Set.ncard_empty, Nat.cast_zero]
    positivity

/-- **Window `ℓ`** of ES22 Claim 4.2. -/
theorem es4_window (hp : Es4Params d β n₀ n t₀)
    (hN : IsPoissonPointProcess N (cycIntensity ℕ d β) Pr) {Cf cf : ℝ}
    (hfast : ∀ {L' t : ℝ}, 1 ≤ L' → 1 ≤ t →
      Pr.real {ω | cycTfast (avoidEnv N ω) L' ≤ ENNReal.ofReal t} ≤
        Cf * t ^ 2 * Real.exp (-(cf * L')))
    {A : Set (Fin d → ℤ)} {L : ℝ} (hA1 : ∀ u ∈ A, L ≤ ‖u‖)
    (hA2 : ∀ r : ℝ, L ≤ r → ((A ∩ {u | ‖u‖ ≤ r}).ncard : ℝ) ≤ r ^ (8 / 3 : ℝ))
    {ℓ : ℕ} (hℓ0 : n₀ < ℓ) (hℓn : ℓ ≤ n) :
    Pr {ω | ∃ s : ℝ, (4 : ℝ) ^ (ℓ - 1) ≤ s ∧ s ≤ 4 ^ ℓ ∧ avoidWalk N ω s ∈ A} ≤
      ENNReal.ofReal (Real.exp (-(((ℓ - 1 : ℕ) : ℝ) ^ 2))) + ENNReal.ofReal (boxExpr d ℓ) +
        ENNReal.ofReal (Cf * ((4 : ℝ) ^ ℓ) ^ 2 * Real.exp (-(cf * ((ℓ : ℝ) ^ 2)))) := by
  have hℓ1 : 1 ≤ ℓ := by have := hp.eight_le; omega
  have hℓR : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ1
  have hd5 := hp.five_le
  have h4pos : (1 : ℝ) ≤ 4 ^ (ℓ - 1) := one_le_pow₀ (by norm_num)
  have h4ℓ : (4 : ℝ) ^ (ℓ - 1) ≤ 4 ^ ℓ := pow_le_pow_right₀ (by norm_num) (by omega)
  have h4n : (4 : ℝ) ^ ℓ ≤ 4 ^ n := pow_le_pow_right₀ (by norm_num) hℓn
  -- the three exceptional events
  set R : ℝ := ((ℓ - 1 : ℕ) : ℝ) ^ 2 * Real.sqrt ((4 : ℝ) ^ ℓ) with hR
  have hsq : Real.sqrt ((4 : ℝ) ^ ℓ) = 2 ^ ℓ := by
    rw [show (4 : ℝ) ^ ℓ = (2 ^ ℓ) ^ 2 by rw [← pow_mul, mul_comm, pow_mul]; norm_num]
    exact Real.sqrt_sq (by positivity)
  set m : ℕ := (ℓ - 1) ^ 2 * 2 ^ ℓ with hm
  have hmR : (m : ℝ) = R := by rw [hR, hsq, hm]; push_cast; ring
  set F1 : Set Ω := {ω | ENNReal.ofReal R ≤ ⨆ s : Set.Icc (0 : ℝ) (4 ^ ℓ),
    ENNReal.ofReal ‖avoidWalk N ω s‖} with hF1
  set F3 : Set Ω := {ω | cycTfast (avoidEnv N ω) ((ℓ : ℝ) ^ 2) ≤ ENNReal.ofReal ((4 : ℝ) ^ ℓ)}
    with hF3
  set U := nearSet A m ((ℓ : ℝ) ^ 2) with hU
  set F2 : Set Ω := ⋃ μ ∈ Finset.Icc ((4 : ℕ) ^ (ℓ - 1)) ((4 : ℕ) ^ ℓ), ⋃ u ∈ U,
    {ω | avoidWalk N ω (μ : ℝ) = u} with hF2
  have hsub : {ω | ∃ s : ℝ, (4 : ℝ) ^ (ℓ - 1) ≤ s ∧ s ≤ 4 ^ ℓ ∧ avoidWalk N ω s ∈ A} ⊆
      F1 ∪ F2 ∪ F3 := by
    intro ω hω
    obtain ⟨s, hs1, hs2, hsA⟩ := hω
    by_cases h1 : ω ∈ F1
    · exact Or.inl (Or.inl h1)
    by_cases h3 : ω ∈ F3
    · exact Or.inr h3
    refine Or.inl (Or.inr ?_)
    have hs0 : 0 ≤ s := by linarith
    set μ : ℕ := ⌈s⌉₊ with hμ
    have hμ1 : s ≤ μ := Nat.le_ceil s
    have hμ2 : (μ : ℝ) < s + 1 := Nat.ceil_lt_add_one hs0
    have hμlo : (4 : ℕ) ^ (ℓ - 1) ≤ μ := by
      have : ((4 : ℕ) ^ (ℓ - 1) : ℝ) ≤ μ := by push_cast; linarith
      exact_mod_cast this
    have hμhi : μ ≤ (4 : ℕ) ^ ℓ := by
      have : (μ : ℝ) ≤ ((4 : ℕ) ^ ℓ : ℕ) := by
        have : μ ≤ ⌈(4 : ℝ) ^ ℓ⌉₊ := Nat.ceil_mono hs2
        have h' : ⌈(4 : ℝ) ^ ℓ⌉₊ = (4 : ℕ) ^ ℓ := by
          rw [show (4 : ℝ) ^ ℓ = (((4 : ℕ) ^ ℓ : ℕ) : ℝ) by push_cast; rfl, Nat.ceil_natCast]
        exact_mod_cast h'.symm ▸ this
      exact_mod_cast this
    -- not F3: ‖W μ - W s‖ < ℓ²
    have hclose : ‖avoidWalk N ω (μ : ℝ) - avoidWalk N ω s‖ < (ℓ : ℝ) ^ 2 := by
      by_contra hcon
      push Not at hcon
      have hmem : (μ : ℝ) ∈ {t : ℝ | 0 < t ∧ ∃ s' : ℝ, t - 1 ≤ s' ∧ s' ≤ t ∧
          (ℓ : ℝ) ^ 2 ≤ ‖regenWalk (avoidEnv N ω) t - regenWalk (avoidEnv N ω) (max s' 0)‖} := by
        refine ⟨by linarith, s, by linarith, hμ1, ?_⟩
        rw [max_eq_left hs0]
        exact hcon
      have hle : (μ : ℝ) ≤ (4 : ℝ) ^ ℓ := by
        have : (μ : ℝ) ≤ ((4 : ℕ) ^ ℓ : ℕ) := by exact_mod_cast hμhi
        simpa using this
      have hT : cycTfast (avoidEnv N ω) ((ℓ : ℝ) ^ 2) ≤ ENNReal.ofReal ((4 : ℝ) ^ ℓ) :=
        iInf₂_le_of_le (μ : ℝ) hmem (ENNReal.ofReal_le_ofReal hle)
      exact h3 hT
    -- not F1: ‖W μ‖ < R
    have hbig : ‖avoidWalk N ω (μ : ℝ)‖ < R := by
      by_contra hcon
      push Not at hcon
      have hle : (μ : ℝ) ≤ (4 : ℝ) ^ ℓ := by
        have : (μ : ℝ) ≤ ((4 : ℕ) ^ ℓ : ℕ) := by exact_mod_cast hμhi
        simpa using this
      exact h1 (le_trans (ENNReal.ofReal_le_ofReal hcon)
        (le_iSup_of_le (⟨(μ : ℝ), by positivity, hle⟩ : Set.Icc (0 : ℝ) (4 ^ ℓ)) le_rfl))
    simp only [hF2, mem_iUnion, mem_ofPred_eq]
    refine ⟨μ, Finset.mem_Icc.2 ⟨hμlo, hμhi⟩, avoidWalk N ω (μ : ℝ), ?_, rfl⟩
    rw [hU, mem_nearSet]
    exact ⟨hmR ▸ hbig.le, avoidWalk N ω s, hsA, hclose⟩
  -- bounds
  have hB1 : Pr F1 ≤ ENNReal.ofReal (Real.exp (-(((ℓ - 1 : ℕ) : ℝ) ^ 2))) := by
    have := es4_hyp_b hp hN (T := (4 : ℝ) ^ ℓ)
      (pow_lt_pow_right₀ (by norm_num) hℓ0) h4n
    rw [avoidLevel_pow ℓ hℓ1] at this
    exact this
  have hB3 : Pr F3 ≤ ENNReal.ofReal (Cf * ((4 : ℝ) ^ ℓ) ^ 2 * Real.exp (-(cf * ((ℓ : ℝ) ^ 2)))) := by
    have hf := hfast (L' := (ℓ : ℝ) ^ 2) (t := (4 : ℝ) ^ ℓ)
      (by nlinarith) (one_le_pow₀ (by norm_num))
    have := hN.isProbabilityMeasure
    have h2 : Pr F3 = ENNReal.ofReal (Pr.real F3) := by
      rw [Measure.real, ENNReal.ofReal_toReal (measure_ne_top _ _)]
    rw [h2]
    exact ENNReal.ofReal_le_ofReal hf
  have hB2 : Pr F2 ≤ ENNReal.ofReal (boxExpr d ℓ) := by
    have := hN.isProbabilityMeasure
    set e : ℝ := -(d : ℝ) / 2 + 1 / 10 with he
    have he0 : e ≤ 0 := by
      have : (5 : ℝ) ≤ d := by exact_mod_cast hd5
      rw [he]; linarith
    set c : ℝ := ((4 : ℝ) ^ (ℓ - 1)) ^ e with hc
    have hc0 : 0 ≤ c := by positivity
    -- card U
    have hr0 : (0 : ℝ) ≤ (ℓ : ℝ) ^ 2 := by positivity
    have hcard := card_nearSet_le A m ((ℓ : ℝ) ^ 2) hr0
    have hk : ⌈(ℓ : ℝ) ^ 2⌉₊ = ℓ ^ 2 := by
      rw [show (ℓ : ℝ) ^ 2 = ((ℓ ^ 2 : ℕ) : ℝ) by push_cast; rfl, Nat.ceil_natCast]
    rw [hk] at hcard
    have h2l : (1 : ℝ) ≤ 2 ^ ℓ := one_le_pow₀ (by norm_num)
    have hcastm : ((ℓ - 1 : ℕ) : ℝ) ≤ ℓ := by exact_mod_cast Nat.sub_le ℓ 1
    have hr' : ((m + ℓ ^ 2 : ℕ) : ℝ) ≤ 2 * (ℓ : ℝ) ^ 2 * 2 ^ ℓ := by
      have : (m : ℝ) ≤ (ℓ : ℝ) ^ 2 * 2 ^ ℓ := by
        rw [hm]; push_cast
        gcongr
      push_cast
      nlinarith [sq_nonneg (ℓ : ℝ), mul_nonneg (sq_nonneg (ℓ : ℝ)) (sub_nonneg.2 h2l)]
    have hnc := sparse_ncard_le hA1 hA2 (r := ((m + ℓ ^ 2 : ℕ) : ℝ)) (by positivity)
    have hnc2 : ((A ∩ {u | ‖u‖ ≤ ((m + ℓ ^ 2 : ℕ) : ℝ)}).ncard : ℝ) ≤
        (2 * (ℓ : ℝ) ^ 2 * 2 ^ ℓ) ^ (8 / 3 : ℝ) :=
      hnc.trans (Real.rpow_le_rpow (by positivity) hr' (by norm_num))
    have hUc : (U.card : ℝ) ≤ (3 * (ℓ : ℝ) ^ 2) ^ d * (2 * (ℓ : ℝ) ^ 2 * 2 ^ ℓ) ^ (8 / 3 : ℝ) := by
      refine hcard.trans ?_
      gcongr
      · push_cast; nlinarith [sq_nonneg (ℓ : ℝ)]
    have hIcc : ((Finset.Icc ((4 : ℕ) ^ (ℓ - 1)) ((4 : ℕ) ^ ℓ)).card : ℝ) ≤ (4 : ℝ) ^ ℓ := by
      rw [Nat.card_Icc]
      have h1 : 1 ≤ (4 : ℕ) ^ (ℓ - 1) := Nat.one_le_pow _ _ (by norm_num)
      have : (4 : ℕ) ^ ℓ + 1 - (4 : ℕ) ^ (ℓ - 1) ≤ (4 : ℕ) ^ ℓ := by
        generalize (4 : ℕ) ^ ℓ = a
        generalize (4 : ℕ) ^ (ℓ - 1) = b at h1
        omega
      calc (((4 : ℕ) ^ ℓ + 1 - (4 : ℕ) ^ (ℓ - 1) : ℕ) : ℝ) ≤ (((4 : ℕ) ^ ℓ : ℕ) : ℝ) := by
            exact_mod_cast this
        _ = (4 : ℝ) ^ ℓ := by push_cast; rfl
    -- probability of each point
    have hpt : ∀ μ ∈ Finset.Icc ((4 : ℕ) ^ (ℓ - 1)) ((4 : ℕ) ^ ℓ), ∀ u : Fin d → ℤ,
        Pr {ω | avoidWalk N ω (μ : ℝ) = u} ≤ ENNReal.ofReal c := by
      intro μ hμ u
      rw [Finset.mem_Icc] at hμ
      have hμ1 : ((4 : ℝ) ^ (ℓ - 1)) ≤ μ := by exact_mod_cast hμ.1
      have hμ2 : (μ : ℝ) ≤ 4 ^ n := by
        refine le_trans ?_ h4n
        exact_mod_cast hμ.2
      have := es4_hyp_a hp hN (t := (μ : ℝ)) ⟨h4pos.trans hμ1, hμ2⟩ u
      refine this.trans (ENNReal.ofReal_le_ofReal ?_)
      exact Real.rpow_le_rpow_of_nonpos (by positivity) hμ1 he0
    calc Pr F2 ≤ ∑ μ ∈ Finset.Icc ((4 : ℕ) ^ (ℓ - 1)) ((4 : ℕ) ^ ℓ),
          Pr (⋃ u ∈ U, {ω | avoidWalk N ω (μ : ℝ) = u}) := measure_biUnion_finset_le _ _
      _ ≤ ∑ μ ∈ Finset.Icc ((4 : ℕ) ^ (ℓ - 1)) ((4 : ℕ) ^ ℓ), ∑ u ∈ U,
          Pr {ω | avoidWalk N ω (μ : ℝ) = u} :=
        Finset.sum_le_sum fun μ _ => measure_biUnion_finset_le _ _
      _ ≤ ∑ μ ∈ Finset.Icc ((4 : ℕ) ^ (ℓ - 1)) ((4 : ℕ) ^ ℓ), ∑ u ∈ U, ENNReal.ofReal c :=
        Finset.sum_le_sum fun μ hμ => Finset.sum_le_sum fun u _ => hpt μ hμ u
      _ = ENNReal.ofReal (((Finset.Icc ((4 : ℕ) ^ (ℓ - 1)) ((4 : ℕ) ^ ℓ)).card : ℝ) *
          (U.card : ℝ) * c) := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]
        simp [mul_assoc]
      _ ≤ ENNReal.ofReal (boxExpr d ℓ) := by
        apply ENNReal.ofReal_le_ofReal
        unfold boxExpr
        rw [← hc]
        calc _ ≤ (4 : ℝ) ^ ℓ * ((3 * (ℓ : ℝ) ^ 2) ^ d * (2 * (ℓ : ℝ) ^ 2 * 2 ^ ℓ) ^ (8 / 3 : ℝ))
              * c := by gcongr
          _ = _ := by rw [hc]
  calc Pr {ω | ∃ s : ℝ, (4 : ℝ) ^ (ℓ - 1) ≤ s ∧ s ≤ 4 ^ ℓ ∧ avoidWalk N ω s ∈ A}
      ≤ Pr (F1 ∪ F2 ∪ F3) := measure_mono hsub
    _ ≤ Pr (F1 ∪ F2) + Pr F3 := measure_union_le _ _
    _ ≤ (Pr F1 + Pr F2) + Pr F3 := by gcongr; exact measure_union_le _ _
    _ ≤ _ := by gcongr

end

end ElboimSly.Paper

end
