/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Avoid.Setting
public import Mathlib

/-!
# ES22 §4: the induction hypothesis at arbitrary times

The induction hypothesis at arbitrary times. Under (S1)–(S2), for a real `T ∈ (4^{n₀}, 4ⁿ]` and
`n_T = ⌈log₄ T⌉ - 1` (`avoidLevel T`), parts (a)–(d): the point bound, the maximal bound, the
relaxed path bound and the Brownian coupling with `σ_T ∈ [1, 2]`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Paper

open ElboimSly.Cyclic

/-- `n_T = ⌈log₄ T⌉ - 1`. The induction hypothesis at arbitrary times. -/
noncomputable def avoidLevel (T : ℝ) : ℕ := ⌈Real.logb 4 T⌉₊ - 1

theorem avoidLevel_spec {T : ℝ} (hT : 1 < T) :
    (4 : ℝ) ^ avoidLevel T < T ∧ T ≤ (4 : ℝ) ^ (avoidLevel T + 1) := by
  have hT0 : 0 < T := by linarith
  have hx : 0 < Real.logb 4 T := Real.logb_pos (by norm_num) hT
  have hm : 0 < ⌈Real.logb 4 T⌉₊ := Nat.ceil_pos.2 hx
  have h1 : (⌈Real.logb 4 T⌉₊ : ℝ) < Real.logb 4 T + 1 := Nat.ceil_lt_add_one hx.le
  have h2 : Real.logb 4 T ≤ ⌈Real.logb 4 T⌉₊ := Nat.le_ceil _
  have hcast : ((avoidLevel T : ℕ) : ℝ) + 1 = ⌈Real.logb 4 T⌉₊ := by
    unfold avoidLevel
    rw [Nat.cast_sub hm]
    simp
  constructor
  · have : ((avoidLevel T : ℕ) : ℝ) < Real.logb 4 T := by linarith
    have := (Real.lt_logb_iff_rpow_lt (by norm_num : (1 : ℝ) < 4) hT0).1 this
    simpa [Real.rpow_natCast] using this
  · have : Real.logb 4 T ≤ ((avoidLevel T + 1 : ℕ) : ℝ) := by push_cast; linarith
    have := (Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ) < 4) hT0).1 this
    rwa [Real.rpow_natCast] at this

theorem avoidLevel_ge {n₀ : ℕ} {T : ℝ} (hT : (4 : ℝ) ^ n₀ < T) : n₀ ≤ avoidLevel T := by
  have h1 : 1 < T := lt_of_le_of_lt (one_le_pow₀ (by norm_num)) hT
  obtain ⟨-, h2⟩ := avoidLevel_spec h1
  by_contra h
  push Not at h
  have : (4 : ℝ) ^ (avoidLevel T + 1) ≤ 4 ^ n₀ := pow_le_pow_right₀ (by norm_num) h
  linarith

theorem avoidLevel_lt {n : ℕ} {T : ℝ} (hT1 : 1 < T) (hT : T ≤ (4 : ℝ) ^ n) : avoidLevel T < n := by
  obtain ⟨h2, -⟩ := avoidLevel_spec hT1
  by_contra h
  push Not at h
  have : (4 : ℝ) ^ n ≤ 4 ^ avoidLevel T := pow_le_pow_right₀ (by norm_num) h
  linarith

section

variable {d : ℕ} {β : ℝ} [Fact (0 < β)] {n₀ n : ℕ} {t₀ : ℝ}

/-- `AdmitsBMCoupling` is monotone in the failure probability. -/
theorem admitsBMCoupling_mono {T : ℝ≥0} {law : Measure (Set.Icc (0 : ℝ≥0) T → Fin d → ℤ)}
    {σ ε η η' : ℝ} (h : AdmitsBMCoupling d T law σ ε η) (hη : η ≤ η') :
    AdmitsBMCoupling d T law σ ε η' := by
  obtain ⟨Q, h1, h2, h3, h4⟩ := h
  exact ⟨Q, h1, h2, h3, h4.trans (ENNReal.ofReal_le_ofReal hη)⟩

theorem indFailBound_le (β t₀ : ℝ) (m : ℕ) : indFailBound β t₀ m ≤ Real.exp (-((m : ℝ) ^ 2)) := by
  unfold indFailBound
  split_ifs
  · apply Real.exp_le_exp.2
    have : (m : ℝ) ^ 2 ≤ (m : ℝ) ^ 3 := by
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · simp
      · exact pow_le_pow_right₀ (by exact_mod_cast hm) (by norm_num)
    linarith
  · exact le_rfl

/-- The levels used by the induction hypothesis at arbitrary times: for `T ∈ (4^{n₀}, 4ⁿ]`, the level `n_T` and the initial time
`t₀' = T / 4^{n_T} ∈ (1, 4]` satisfy `n₀ ≤ n_T < n` and `t_{n_T}(t₀') = T`. -/
theorem avoidLevel_data {T : ℝ} (h1 : (4 : ℝ) ^ n₀ < T) (h2 : T ≤ (4 : ℝ) ^ n) :
    n₀ ≤ avoidLevel T ∧ avoidLevel T < n ∧ 1 < T / 4 ^ avoidLevel T ∧
      T / 4 ^ avoidLevel T ≤ 4 ∧ indScale (T / 4 ^ avoidLevel T) (avoidLevel T) = T := by
  have hT1 : 1 < T := lt_of_le_of_lt (one_le_pow₀ (by norm_num)) h1
  obtain ⟨h3, h4⟩ := avoidLevel_spec hT1
  have hpos : (0 : ℝ) < 4 ^ avoidLevel T := by positivity
  refine ⟨avoidLevel_ge h1, avoidLevel_lt hT1 h2, ?_, ?_, ?_⟩
  · rw [lt_div_iff₀ hpos]; linarith
  · rw [div_le_iff₀ hpos]; rw [pow_succ] at h4; linarith
  · unfold indScale; field_simp

omit [Fact (0 < β)] in
/-- `|σ - √2| ≤ 3 β^{-1/16}` and `β ≥ 10^14` give `σ ∈ [1, 2]`. -/
theorem sigma_mem_Icc {σ : ℝ} (hβ : (10 : ℝ) ^ 14 ≤ β) {T : ℝ} (hT : 0 < T)
    (h : |σ - Real.sqrt 2| ≤ max (3 * β ^ (-(1 : ℝ) / 16) - T ^ (-(1 : ℝ) / 16)) 0) :
    σ ∈ Set.Icc (1 : ℝ) 2 := by
  have hβ0 : 0 < β := lt_of_lt_of_le (by positivity) hβ
  set x := β ^ ((1 : ℝ) / 16) with hx
  have hx0 : 0 < x := Real.rpow_pos_of_pos hβ0 _
  have hx16 : x ^ 16 = β := by
    rw [hx, ← Real.rpow_natCast, ← Real.rpow_mul hβ0.le]; norm_num
  have hx73 : (7.3 : ℝ) ≤ x := by
    by_contra hlt
    push Not at hlt
    have : x ^ 16 < (7.3 : ℝ) ^ 16 := pow_lt_pow_left₀ hlt hx0.le (by norm_num)
    have h2 : (7.3 : ℝ) ^ 16 < (10 : ℝ) ^ 14 := by norm_num
    linarith
  have hneg : β ^ (-(1 : ℝ) / 16) = x⁻¹ := by
    rw [hx, ← Real.rpow_neg hβ0.le]; congr 1; ring
  have hTn : 0 < T ^ (-(1 : ℝ) / 16) := Real.rpow_pos_of_pos hT _
  have hinv : x⁻¹ ≤ 1 / 7.3 := by
    rw [one_div]; exact inv_anti₀ (by norm_num) hx73
  have hbd : |σ - Real.sqrt 2| ≤ 0.4111 := by
    refine h.trans (max_le ?_ (by norm_num))
    rw [hneg]
    have : 3 * x⁻¹ ≤ 3 * (1 / 7.3) := by gcongr
    norm_num at this ⊢
    linarith
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have hlo : (1.4142 : ℝ) ≤ Real.sqrt 2 := by nlinarith
  have hhi : Real.sqrt 2 ≤ 1.4143 := by nlinarith
  rw [abs_le] at hbd
  constructor <;> linarith [hbd.1, hbd.2]

end

section

variable {d : ℕ} {β : ℝ} [Fact (0 < β)] {n₀ n : ℕ} {t₀ : ℝ} {Ω : Type} [MeasurableSpace Ω]
  {Pr : Measure Ω} {N : Ω → Measure (CycS ℕ d β)}

/-- **the induction hypothesis at arbitrary times (a)**: `P(W(t) = u) ≤ t^{-d/2 + 0.1}` for all real `t ∈ [1, 4ⁿ]` and
`u ∈ ℤᵈ`. (This is (H2) of `H(β, n-1, 4)`, as `t_{n-1} = 4ⁿ` for `t₀ = 4`.) -/
theorem es4_hyp_a (hp : Es4Params d β n₀ n t₀)
    (hN : IsPoissonPointProcess N (cycIntensity ℕ d β) Pr) {t : ℝ}
    (ht : t ∈ Set.Icc (1 : ℝ) (4 ^ n)) (u : Fin d → ℤ) :
    Pr {ω | avoidWalk N ω t = u} ≤ ENNReal.ofReal (t ^ (-(d : ℝ) / 2 + 1 / 10)) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := hp.lt; have := Nat.zero_le n₀; omega⟩
  have hH := (hp.ind m (by have := hp.lt; omega) (by omega) 4 (by norm_num) le_rfl).1 Ω Pr N hN
  have := hH.2.1 t (by
    refine ⟨ht.1, ?_⟩
    have : indScale 4 m = 4 ^ (m + 1) := by unfold indScale; ring
    rw [this]; exact ht.2) u
  exact this

/-- **the induction hypothesis at arbitrary times (b)**: the maximal bound at level `n_T`. -/
theorem es4_hyp_b (hp : Es4Params d β n₀ n t₀)
    (hN : IsPoissonPointProcess N (cycIntensity ℕ d β) Pr) {T : ℝ}
    (h1 : (4 : ℝ) ^ n₀ < T) (h2 : T ≤ (4 : ℝ) ^ n) :
    Pr {ω | ENNReal.ofReal (((avoidLevel T : ℕ) : ℝ) ^ 2 * Real.sqrt T) ≤
        ⨆ s : Set.Icc (0 : ℝ) T, ENNReal.ofReal ‖avoidWalk N ω s‖} ≤
      ENNReal.ofReal (Real.exp (-((avoidLevel T : ℕ) : ℝ) ^ 2)) := by
  obtain ⟨a1, a2, a3, a4, a5⟩ := avoidLevel_data h1 h2
  have hH := (hp.ind _ a1 a2 _ a3 a4).1 Ω Pr N hN
  have h3 := hH.2.2.1
  unfold IndH3 at h3
  rw [a5] at h3
  exact h3.trans (ENNReal.ofReal_le_ofReal (by
    have := indFailBound_le β (T / 4 ^ avoidLevel T) (avoidLevel T)
    simpa using this))

/-- **the induction hypothesis at arbitrary times (c)**: `W|[0,T]` is a relaxed path with probability `≥ 1 - e^{-n_T²}`. -/
theorem es4_hyp_c (hp : Es4Params d β n₀ n t₀)
    (hN : IsPoissonPointProcess N (cycIntensity ℕ d β) Pr) {T : ℝ}
    (h1 : (4 : ℝ) ^ n₀ < T) (h2 : T ≤ (4 : ℝ) ^ n) :
    ENNReal.ofReal (1 - Real.exp (-((avoidLevel T : ℕ) : ℝ) ^ 2)) ≤
      Pr {ω | IsRelaxedPath (avoidEnv N ω) T} := by
  obtain ⟨a1, a2, a3, a4, a5⟩ := avoidLevel_data h1 h2
  have hH := (hp.ind _ a1 a2 _ a3 a4).1 Ω Pr N hN
  have h3 := hH.1
  unfold IndH1 at h3
  rw [a5] at h3
  refine le_trans (ENNReal.ofReal_le_ofReal ?_) h3
  have := indFailBound_le β (T / 4 ^ avoidLevel T) (avoidLevel T)
  linarith

/-- **the induction hypothesis at arbitrary times (d)**: there is `σ_T ∈ [1, 2]` such that `W` admits a `(σ_T, T^{θ_H})`-coupling
up to time `T` with failure probability `e^{-n_T²}`. -/
theorem es4_hyp_d (hp : Es4Params d β n₀ n t₀)
    (hN : IsPoissonPointProcess N (cycIntensity ℕ d β) Pr) {T : ℝ}
    (h1 : (4 : ℝ) ^ n₀ < T) (h2 : T ≤ (4 : ℝ) ^ n) :
    ∃ σ ∈ Set.Icc (1 : ℝ) 2, AdmitsBMCoupling d T.toNNReal
      (Pr.map (fun ω (t : Set.Icc (0 : ℝ≥0) T.toNNReal) => avoidWalk N ω ((t : ℝ≥0) : ℝ)))
      σ (T ^ indThetaH) (Real.exp (-((avoidLevel T : ℕ) : ℝ) ^ 2)) := by
  obtain ⟨a1, a2, a3, a4, a5⟩ := avoidLevel_data h1 h2
  have hH := (hp.ind _ a1 a2 _ a3 a4).1 Ω Pr N hN
  have h4 := hH.2.2.2
  unfold IndH4 at h4
  rw [a5] at h4
  obtain ⟨σ, hσ, hc⟩ := h4
  have hT0 : 0 < T := lt_of_le_of_lt (by positivity) h1
  refine ⟨σ, sigma_mem_Icc hp.beta_sigma hT0 hσ, admitsBMCoupling_mono hc ?_⟩
  have := indFailBound_le β (T / 4 ^ avoidLevel T) (avoidLevel T)
  simpa using this

end

end ElboimSly.Paper

end
