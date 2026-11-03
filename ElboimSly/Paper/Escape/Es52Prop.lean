/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Escape.Es52Step2
public import ElboimSly.Paper.Escape.Es52Num
public import ElboimSly.Paper.Escape.Es54
public import ElboimSly.Paper.Heavy.Entrance
public import Mathlib

/-!
# ES22 Proposition 5.2, conditional on `Es55Concl`

ES22 Proposition 5.2.  `Es52Concl k` is the statement: there are `c₅₂ > 0` depending only on
`d = k + 2` and `β₅₂ = β₅₂(n₀)` such that, in a setting with `β ≥ β₅₂(n₀)`, for every admissible
block `B = B_u`,
`P(ξ_B ≤ t_n, ξ_B < t_reg, π_B ≤ n^{-γ}) ≤ exp(-c₅₂ n³)`.

`es5_2_of_es55` proves it from the conclusion `Es55Concl k` of ES22 Lemma 5.5 (rule 6: a distinctly
named conditional helper; `es5_4` is proved).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Escape

open ElboimSly ElboimSly.Cyclic ElboimSly.Interchange ElboimSly.Paper ElboimSly.Brownian

variable {k : ℕ}

/-- The statement of ES22 Proposition 5.2: `c₅₂` depends only on `d`, `β₅₂` on `(d, n₀)`. -/
def Es52Concl (k : ℕ) : Prop :=
  ∃ c52 : ℝ, 0 < c52 ∧ ∃ β52 : ℕ → ℝ, ∀ {β : ℝ} [Fact (0 < β)] {n₀ n : ℕ} {t₀ : ℝ} {Ω : Type}
    {𝒢₀ : MeasurableSpace Ω} [MeasurableSpace Ω] {Pr : Measure Ω}
    {N N' : Ω → Measure (CycS ℕ (k + 2) β)}
    (_ : Es4Setting (k + 2) β n₀ n t₀ 𝒢₀ Pr N N'), β52 n₀ ≤ β →
    ∀ (u : Fin (k + 2) → ℤ), EscAdmissible (escJ n) u →
      Pr {ω | escXi (escWalk (N ω)) (escBlock (escJ n) u) ≤ ENNReal.ofReal (indScale t₀ n) ∧
        escXi (escWalk (N ω)) (escBlock (escJ n) u) < cycTreg (copyEnv (N ω) 0) ∧
        escPi Pr N n (escJ n) (indScale t₀ n) (escBlock (escJ n) u) ω ≤
          ENNReal.ofReal ((n : ℝ) ^ (-escGamma (k + 2)))} ≤
        ENNReal.ofReal (Real.exp (-(c52 * (n : ℝ) ^ 3)))

/-- `M ≤ n` once `β ≥ 4^{M+1}` in a setting (`β < t_n ≤ 4^{n+1}`). -/
theorem le_of_four_pow_le {n M : ℕ} {t₀ β : ℝ} (h4 : t₀ ≤ 4) (ht : β < indScale t₀ n)
    (hβ : (4 : ℝ) ^ (M + 1) ≤ β) : M ≤ n := by
  by_contra hc
  push Not at hc
  have h1 : (4 : ℝ) ^ (n + 1) ≤ 4 ^ M := pow_le_pow_right₀ (by norm_num) (by omega)
  have h2 : (4 : ℝ) ^ n * t₀ ≤ 4 ^ (n + 1) := by rw [pow_succ]; gcongr
  have h3 : (4 : ℝ) ^ M < 4 ^ (M + 1) := pow_lt_pow_right₀ (by norm_num) (by omega)
  unfold indScale at ht
  have := calc β < 4 ^ n * t₀ := ht
    _ ≤ 4 ^ (n + 1) := h2
    _ ≤ 4 ^ M := h1
    _ < 4 ^ (M + 1) := h3
  exact absurd hβ (not_le.2 this)

theorem four_pow_succ_ge {n : ℕ} {t₀ β : ℝ} (h4 : t₀ ≤ 4) (ht : β < indScale t₀ n) :
    β ≤ (4 : ℝ) ^ (n + 1) := by
  have h2 : (4 : ℝ) ^ n * t₀ ≤ 4 ^ (n + 1) := by rw [pow_succ]; gcongr
  unfold indScale at ht
  linarith

theorem escIstar_real_ge {n : ℕ} (hn : 2000 ≤ n) :
    (n : ℝ) ^ 3 / 2 ≤ (escIstar n (escJ n) : ℝ) := by
  have h := escIstar_ge (n := n) (by omega)
  have h2 : 9 * n ^ 3 < 16 * (9 * n ^ 3 / 16 + 1) := Nat.lt_mul_div_succ _ (by norm_num)
  have h3 : (9 * n ^ 3 : ℝ) < 16 * ((escIstar n (escJ n) : ℝ) + 1) := by
    have : 9 * n ^ 3 < 16 * (escIstar n (escJ n) + 1) := by omega
    exact_mod_cast this
  have hnR : (2000 : ℝ) ≤ n := by exact_mod_cast hn
  nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2000) hnR 3]

/-- At the (finite) entrance time the walk is in the block. -/
theorem escWalk_xi_mem {n : ℕ} {u : Fin (k + 2) → ℤ} {β : ℝ} [Fact (0 < β)]
    {ν : Measure (CycS ℕ (k + 2) β)} (hν : CycGood ν)
    (hfin : escXi (escWalk ν) (escBlock (escJ n) u) ≠ ⊤) :
    escWalk ν (escXi (escWalk ν) (escBlock (escJ n) u)).toReal ∈ escBlock (escJ n) u := by
  have hw := isCyclicPath_escWalk hν
  have hex : ∃ s : ℝ, 0 ≤ s ∧ escWalk ν s ∈ escBlock (escJ n) u := by
    by_contra hno
    push Not at hno
    exact hfin ((escXi_eq_entranceTime _ _).trans (entranceTime_eq_top_of_empty hno))
  obtain ⟨s, hs, hws⟩ := hex
  obtain ⟨s'', h0, -, hmem, heq⟩ := exists_entrance_real hw hs hws
  rw [escXi_eq_entranceTime, heq, ENNReal.toReal_ofReal h0]
  exact hmem

theorem escWalk_zero_eq {β : ℝ} [Fact (0 < β)] {ν : Measure (CycS ℕ (k + 2) β)} (hν : CycGood ν) :
    escWalk ν 0 = 0 := by
  rw [escWalk_eq_first hν le_rfl (by simp)]
  exact cycWalk_zero (hν 0) 0 0

/-- **ES22 Proposition 5.2**, conditional on `Es55Concl k` (ES22 Lemma 5.5). -/
theorem es5_2_of_es55 (hk : 3 ≤ k) (h55 : Es55Concl k) : Es52Concl k := by
  obtain ⟨β53, h53⟩ := es5_4 hk
  obtain ⟨β55, h55'⟩ := h55
  have hcl : 0 < cline (k + 2) := cline_pos' _
  set M : ℕ := max 2000 ⌈56 / cline (k + 2)⌉₊ with hM
  refine ⟨cline (k + 2) / 8, by positivity,
    fun n₀ => max (max (β53 n₀) (β55 n₀)) ((4 : ℝ) ^ (M + 1)), ?_⟩
  intro β _ n₀ n t₀ Ω 𝒢₀ mΩ Pr N N' hS hβ u hadm
  have hp := hS.params
  have hβ0 : 0 < β := Fact.out
  have h53le : β53 n₀ ≤ β := (le_max_left _ _).trans ((le_max_left _ _).trans hβ)
  have h55le : β55 n₀ ≤ β := (le_max_right _ _).trans ((le_max_left _ _).trans hβ)
  have hMn : M ≤ n := le_of_four_pow_le hp.le_four hp.beta_lt ((le_max_right _ _).trans hβ)
  have hn : 2000 ≤ n := (le_max_left _ _).trans hMn
  have hN56 : 56 / cline (k + 2) ≤ n := by
    refine (Nat.le_ceil _).trans ?_
    exact_mod_cast (le_max_right _ _).trans hMn
  have hlb := log_le_pow_forty hn hp.le_four hβ0 hp.beta_lt
  have hβ4 := four_pow_succ_ge hp.le_four hp.beta_lt
  have hIge := escIstar_real_ge hn
  have hj := one_le_escJ hn
  have hgood := CycSchemeEnv.ae_cycGood' hS.space.ppp
  have hS1 := es52_step1_sum hS hn hlb u hadm
    (fun β' i hi1 hiI => h55' hS h55le u hadm β' i hi1 hiI)
    (fun β' => h53 hS h53le u hadm β')
  have hnum := num_main hcl hβ0 hn hN56 hβ4 hIge
  -- the `B⁺` half
  have hS2 : Pr {ω | CycGood (N ω) ∧
        escXi (escWalk (N ω)) (escBlock (escJ n) u) ≤ ENNReal.ofReal (indScale t₀ n) ∧
        escXi (escWalk (N ω)) (escBlock (escJ n) u) < cycTreg (copyEnv (N ω) 0) ∧
        escWalk (N ω) (escXi (escWalk (N ω)) (escBlock (escJ n) u)).toReal ∈
          escBlockPlus (escJ n) u ∧
        escPiG Pr N n (indScale t₀ n) u ω ≤ ENNReal.ofReal ((n : ℝ) ^ (-escGamma (k + 2)))} ≤
      ⌈β⌉₊ * (2 * (1 - ENNReal.ofReal (cline (k + 2) / 2)) ^ escIstar n (escJ n)) := by
    by_cases hu : u = 0
    · subst hu
      refine le_trans (le_of_eq ?_) zero_le
      convert measure_empty (μ := Pr)
      ext ω
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
      rintro ⟨hg, -, -, h3, -⟩
      have h0 : (0 : Fin (k + 2) → ℤ) ∈ escBlock (escJ n) 0 := fun c => by simp
      have hle : escXi (escWalk (N ω)) (escBlock (escJ n) 0) ≤ 0 := by
        rw [escXi_eq_entranceTime]
        have := entranceTime_le_of_mem (w := escWalk (N ω)) (B := escBlock (escJ n) 0) (s := 0)
          le_rfl (by rw [escWalk_zero_eq hg]; exact h0)
        simpa using this
      have hξ : escXi (escWalk (N ω)) (escBlock (escJ n) 0) = 0 := le_antisymm hle bot_le
      rw [hξ, ENNReal.toReal_zero, escWalk_zero_eq hg] at h3
      refine h3.2 ⟨⟨by simp, ?_⟩, fun c _ => ⟨by simp, ?_⟩⟩
      · simp
      · simp
    · have hS' := es4Setting_envRefl hS
      have hadm' : EscAdmissible (escJ n) (reflU (escJ n) u) := reflAut_admissible hadm hu
      exact es52_step2 hS hn hlb u hu hadm
        (fun β' i hi1 hiI => h55' hS' h55le _ hadm' β' i hi1 hiI)
        (fun β' => h53 hS' h53le _ hadm' β')
  have hsub : {ω | escXi (escWalk (N ω)) (escBlock (escJ n) u) ≤ ENNReal.ofReal (indScale t₀ n) ∧
        escXi (escWalk (N ω)) (escBlock (escJ n) u) < cycTreg (copyEnv (N ω) 0) ∧
        escPi Pr N n (escJ n) (indScale t₀ n) (escBlock (escJ n) u) ω ≤
          ENNReal.ofReal ((n : ℝ) ^ (-escGamma (k + 2)))} ≤ᵐ[Pr]
      ({ω | CycGood (N ω) ∧
        escXi (escWalk (N ω)) (escBlock (escJ n) u) ≤ ENNReal.ofReal (indScale t₀ n) ∧
        escXi (escWalk (N ω)) (escBlock (escJ n) u) < cycTreg (copyEnv (N ω) 0) ∧
        escWalk (N ω) (escXi (escWalk (N ω)) (escBlock (escJ n) u)).toReal ∈
          escBlockMinus (escJ n) u ∧
        escPiG Pr N n (indScale t₀ n) u ω ≤ ENNReal.ofReal ((n : ℝ) ^ (-escGamma (k + 2)))} ∪
      {ω | CycGood (N ω) ∧
        escXi (escWalk (N ω)) (escBlock (escJ n) u) ≤ ENNReal.ofReal (indScale t₀ n) ∧
        escXi (escWalk (N ω)) (escBlock (escJ n) u) < cycTreg (copyEnv (N ω) 0) ∧
        escWalk (N ω) (escXi (escWalk (N ω)) (escBlock (escJ n) u)).toReal ∈
          escBlockPlus (escJ n) u ∧
        escPiG Pr N n (indScale t₀ n) u ω ≤ ENNReal.ofReal ((n : ℝ) ^ (-escGamma (k + 2)))}) := by
    filter_upwards [hgood] with ω hg hω
    obtain ⟨h1, h2, h3⟩ := hω
    have hfin : escXi (escWalk (N ω)) (escBlock (escJ n) u) ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top h1
    have hmem := escWalk_xi_mem (n := n) (u := u) hg hfin
    have hπ := (escPiG_le_escPi Pr N n (indScale t₀ n) u ω).trans h3
    by_cases hm : escWalk (N ω) (escXi (escWalk (N ω)) (escBlock (escJ n) u)).toReal ∈
        escBlockMinus (escJ n) u
    · exact Or.inl ⟨hg, h1, h2, hm, hπ⟩
    · exact Or.inr ⟨hg, h1, h2, ⟨hmem, hm⟩, hπ⟩
  calc _ ≤ Pr _ := measure_mono_ae hsub
    _ ≤ _ + _ := measure_union_le _ _
    _ ≤ ⌈β⌉₊ * (2 * (1 - ENNReal.ofReal (cline (k + 2) / 2)) ^ escIstar n (escJ n)) +
        ⌈β⌉₊ * (2 * (1 - ENNReal.ofReal (cline (k + 2) / 2)) ^ escIstar n (escJ n)) := by
        gcongr
    _ = 2 * ((⌈β⌉₊ : ℝ≥0∞) * (2 * (1 - ENNReal.ofReal (cline (k + 2) / 2)) ^ escIstar n (escJ n))) :=
        (two_mul _).symm
    _ ≤ _ := hnum

end ElboimSly.Paper.Escape
