/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Escape.Es55Stmt
public import ElboimSly.Paper.Escape.Es4Transfer
public import Mathlib

/-!
# Lemma 5.5: Step 2 and the assembly (conditional on Step 1)

ES22 Lemma 5.5.

`Es55Step1` is the conclusion of Step 1 of the proof of ES22 Lemma 5.5 (a lower bound
`n^{-γ+1}` for `Φ_{Con_i}(cycRec(S₃))` on `𝒦(β') ∩ 𝒜_i ∩ {r_i ≤ 4^{j-1}, W_i^←(r_i) ∈ F_B}`),
and `Es55Meas` collects the measurability facts the tower argument uses (the sets are events of the
indicated records).  `es5_5_of_step1` combines them with ES22 Claim 5.7 (`es5_7_space`) and the
tower property (`es5_5_step2`).  This is a conditional helper (distinctly named); it does not stand
in for ES22 Lemma 5.5.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace ElboimSly.Paper.Escape

open ElboimSly ElboimSly.Cyclic ElboimSly.Paper ElboimSly.Brownian ElboimSly.Cyclic.CycSchemeEnv

variable {k : ℕ}

/-- The exit set `{r_i ≤ 4^{j-1}, W_i^←(r_i) ∈ F_B}` of Step 1, with the parameter `S` of
`es5_7_space` fixed to `4^j / 4`. -/
noncomputable def es55Exit (β : ℝ) [Fact (0 < β)] (n : ℕ) (u : EscV k) (β' i : ℕ) :
    Set (Measure (CycS ℕ (k + 2) β)) :=
  exitSet (β := β) (escJ n) u (Real.toNNReal (((2 : ℝ) ^ escJ n) ^ 2 / 4))
    (((0 : ℕ), escPoint n (escJ n) u i, (β' : ℝ), false) : CycData ℕ (k + 2))

/-- **Conclusion of Step 1 of ES22 Lemma 5.5** (given `ℱ_{S₃}`). -/
def Es55Step1 (k : ℕ) : Prop :=
  ∃ b : ℕ → ℝ, ∀ {β : ℝ} [Fact (0 < β)] {n₀ n : ℕ} {t₀ : ℝ} {Ω : Type}
    {𝒢₀ : MeasurableSpace Ω} [MeasurableSpace Ω] {Pr : Measure Ω}
    {N N' : Ω → Measure (CycS ℕ (k + 2) β)}
    (hS : Es4Setting (k + 2) β n₀ n t₀ 𝒢₀ Pr N N'), b n₀ ≤ β →
    ∀ (u : Fin (k + 2) → ℤ), EscAdmissible (escJ n) u → ∀ (β' i : ℕ), 1 ≤ i →
      i ≤ escIstar n (escJ n) →
      ∀ᵐ ω ∂Pr, N ω ∈ (escKSet β (indScale t₀ n) n β' u ∩
          escASet n u β' (hlog_of_params hS.params) i) ∩ es55Exit β n u β' i →
        ENNReal.ofReal ((n : ℝ) ^ (-escGamma (k + 2) + 1)) ≤
          resPhi (plan5 n β (indScale t₀ n) u β' i (hlog_of_params hS.params)) Pr N
            (lamT (plan5 n β (indScale t₀ n) u β' i (hlog_of_params hS.params)) N
              (escIstar n (escJ n) + 2))
            (escConSet β n u i) ω

/-- The measurability facts used by the tower argument of ES22 Lemma 5.5. -/
def Es55Meas (k : ℕ) : Prop :=
  ∀ {β : ℝ} [Fact (0 < β)] {n₀ n : ℕ} {t₀ : ℝ} {Ω : Type}
    {𝒢₀ : MeasurableSpace Ω} [_mΩ : MeasurableSpace Ω] {Pr : Measure Ω}
    {N N' : Ω → Measure (CycS ℕ (k + 2) β)}
    (hS : Es4Setting (k + 2) β n₀ n t₀ 𝒢₀ Pr N N') (u : Fin (k + 2) → ℤ) (β' i : ℕ),
    1 ≤ i → i ≤ escIstar n (escJ n) →
    MeasurableSet (escKSet β (indScale t₀ n) n β' u ∩
          escASet n u β' (hlog_of_params hS.params) i) ∧
    MeasurableSet (escConSet β n u i) ∧
    (∀ (hT : IsStoppingTime (cycMultiFilt
        (plan5 n β (indScale t₀ n) u β' i (hlog_of_params hS.params)) 𝒢₀
        hS.space.ppp.measurable hS.space.le Pr)
        (lamT (plan5 n β (indScale t₀ n) u β' i (hlog_of_params hS.params)) N
          (escIstar n (escJ n) + 1))),
      MeasurableSet[hT.measurableSpace] (N ⁻¹' (escKSet β (indScale t₀ n) n β' u ∩
          escASet n u β' (hlog_of_params hS.params) i))) ∧
    (∀ (hT : IsStoppingTime (cycMultiFilt
        (plan5 n β (indScale t₀ n) u β' i (hlog_of_params hS.params)) 𝒢₀
        hS.space.ppp.measurable hS.space.le Pr)
        (lamT (plan5 n β (indScale t₀ n) u β' i (hlog_of_params hS.params)) N
          (escIstar n (escJ n) + 2))),
      MeasurableSet[hT.measurableSpace] (N ⁻¹' ((escKSet β (indScale t₀ n) n β' u ∩
          escASet n u β' (hlog_of_params hS.params) i) ∩ es55Exit β n u β' i)))

theorem exists_four_pow_le {β : ℝ} {n M : ℕ} {t₀ : ℝ} (h4 : t₀ ≤ 4) (ht : β < 4 ^ n * t₀)
    (hβ : (4 : ℝ) ^ (M + 1) ≤ β) : M ≤ n := by
  by_contra hc
  push Not at hc
  have h1 : (4 : ℝ) ^ (n + 1) ≤ 4 ^ (M + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
  have h2 : (4 : ℝ) ^ n * t₀ ≤ 4 ^ (n + 1) := by rw [pow_succ]; gcongr
  linarith

theorem es55_numeric {n : ℕ} {c γ : ℝ} (_hc : 0 < c) (hn : 4 ≤ n * c) (hn0 : 0 < n) :
    2 * ENNReal.ofReal ((n : ℝ) ^ (-γ)) ≤
      ENNReal.ofReal ((n : ℝ) ^ (-γ + 1)) * ENNReal.ofReal (c / 2) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn0
  rw [← ENNReal.ofReal_mul (by positivity), show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp,
    ← ENNReal.ofReal_mul (by norm_num)]
  refine ENNReal.ofReal_le_ofReal ?_
  have e : (n : ℝ) ^ (-γ + 1) = (n : ℝ) ^ (-γ) * n := by
    rw [Real.rpow_add hn', Real.rpow_one]
  rw [e]
  have hp : 0 < (n : ℝ) ^ (-γ) := Real.rpow_pos_of_pos hn' _
  nlinarith

/-- **ES22 Lemma 5.5 from Step 1** (conditional helper): Step 2 of the proof, combining the Step 1
bound with ES22 Claim 5.7 through the tower property. -/
theorem es5_5_of_step1 (hk : 3 ≤ k) (h1 : Es55Step1 k) (hm : Es55Meas k) : Es55Concl k := by
  have hd : 5 ≤ k + 2 := by omega
  obtain ⟨b, H1⟩ := h1
  have H7 := es5_7_space (k := k) hd
  choose b57 hb57 using H7
  set c : ℝ := c57 (k + 2) with hcdef
  have hc : 0 < c := ctube_pos _ _
  set M : ℕ := ⌈4 / c⌉₊ with hM
  refine ⟨fun n₀ => max (b n₀) (max (b57 n₀) ((4 : ℝ) ^ (M + 1))), ?_⟩
  intro β _ n₀ n t₀ Ω 𝒢₀ mΩ Pr N N' hS hβ u hadm β' i hi1 hiI
  have hβb : b n₀ ≤ β := le_trans (le_max_left _ _) hβ
  have hβ57 : b57 n₀ ≤ β := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hβ
  have hβM : (4 : ℝ) ^ (M + 1) ≤ β :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hβ
  have hMn : M ≤ n := exists_four_pow_le hS.params.le_four hS.params.beta_lt hβM
  have hn0 : 0 < n := by
    have := hS.params.lt
    have := hS.params.eight_le
    omega
  have hnc : 4 ≤ (n : ℝ) * c := by
    have h1 : 4 / c ≤ M := Nat.le_ceil _
    have h2 : (M : ℝ) ≤ n := by exact_mod_cast hMn
    rw [div_le_iff₀ hc] at h1
    nlinarith
  have hPr : IsProbabilityMeasure Pr := hS.space.ppp.isProbabilityMeasure
  set hlog := hlog_of_params hS.params with hhlog
  set P := plan5 n β (indScale t₀ n) u β' i hlog with hP
  set I := escIstar n (escJ n) with hI
  have hN := hS.space.ppp
  have hN' := hS.space.ppp'
  have h𝒢 := hS.space.le
  have hPfin : PlanFin P := plan5_planFin n β (indScale t₀ n) u β' i hlog
  have hKeq : P.K = ((I + 2 : ℕ) : ℕ∞) := rfl
  have hK0 : 0 < P.K := by rw [hKeq]; exact_mod_cast Nat.succ_pos _
  have hk1 : ((I + 1 : ℕ) : ℕ∞) < P.K := by rw [hKeq]; exact_mod_cast Nat.lt_succ_self _
  have hT2 := isStoppingTime_lam 𝒢₀ P hN.measurable h𝒢 Pr hPfin hk1
  have hT3 := isStoppingTime_lam_succ 𝒢₀ P hN.measurable h𝒢 Pr hPfin hk1
  have hfin : ∀ k' : ℕ, (k' : ℕ∞) ≤ P.K → Pr {ω | lamT P N k' ω ≠ ⊤} = 1 := by
    intro k' hk'
    have : {ω | lamT P N k' ω ≠ ⊤} = univ := by
      ext ω; exact ⟨fun _ => trivial, fun _ => lamT_ne_top P hPfin ω hk'⟩
    rw [this, measure_univ]
  have hTT : lamT P N (I + 1) ≤ lamT P N (I + 1 + 1) := by
    intro ω
    exact lam_mono (Nat.le_succ _)
  obtain ⟨hKm, hCm, hKT, hKET⟩ := hm hS u β' i hi1 hiI
  have hEm : MeasurableSet (es55Exit β n u β' i) := measurableSet_exitSet _ _ _ _
  have hstep1 := H1 hS hβb u hadm β' i hi1 hiI
  have hc7 := hb57 n₀ β hβ57 n t₀ hS.params 𝒢₀ hS.space (indScale t₀ n) u β' i hlog hi1 hiI
    (S := Real.toNNReal (((2 : ℝ) ^ escJ n) ^ 2 / 4))
    (Real.coe_toNNReal _ (by positivity))
  have key := es5_5_step2 P 𝒢₀ hN hN' hS.space.indep hS.space.indep' hK0 h𝒢 hT2 hT3 hTT
    (hfin _ (by rw [hKeq]; exact_mod_cast Nat.le_succ _)) (hfin _ (by rw [hKeq]))
    hKm hEm hCm (hKT hT2) (hKET hT3) hstep1
    (by filter_upwards [hc7] with ω hω _ using hω)
  filter_upwards [key] with ω hω hmem
  refine le_trans ?_ (hω hmem)
  have hγ : True := trivial
  exact es55_numeric hc hnc hn0

end ElboimSly.Paper.Escape
