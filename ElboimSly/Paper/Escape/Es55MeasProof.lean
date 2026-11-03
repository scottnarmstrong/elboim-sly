/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Escape.Es55MeasProofSets
public import ElboimSly.Paper.Escape.Es52Meas3
public import ElboimSly.Paper.Escape.Es52Meas2
public import Mathlib

/-!
# `Es55Meas`: the measurability facts of the tower argument of ES22 Lemma 5.5

ES22 Lemma 5.5 (Step 2).  `es55Meas : Es55Meas k` assembles
`measurableSet_entries` / `measurableSet_preimage_lam` (events determined by the first `I + 1`,
respectively `I + 2`, final entries of `𝒫₅`) with `measurableSet_escConSet`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace ElboimSly.Paper.Escape

open ElboimSly ElboimSly.Cyclic ElboimSly.Cyclic.CycSchemeEnv ElboimSly.Paper

set_option linter.unusedSectionVars false

variable {k : ℕ}

theorem one_le_escJ_of_lt {n : ℕ} (hn : 2 ≤ n) : 1 ≤ escJ n := by
  by_contra h
  have h0 : escJ n = 0 := by omega
  have := le_two_pow_escJ n
  rw [h0] at this
  have h2 : 2 ^ 20 ≤ n ^ 20 := Nat.pow_le_pow_left hn 20
  norm_num at this h2
  omega

/-- **`Es55Meas`**: the measurability facts used by the tower argument of ES22 Lemma 5.5. -/
theorem es55Meas : Es55Meas k := by
  intro β _ n₀ n t₀ Ω 𝒢₀ mΩ Pr N N' hS u β' i hi1 hiI
  have hn : 2 ≤ n := by
    have := hS.params.lt
    have := hS.params.eight_le
    omega
  have hj := one_le_escJ_of_lt hn
  set hlog := hlog_of_params hS.params with hhlog
  set tn := indScale t₀ n
  have hNm : Measurable N := hS.space.ppp.measurable
  have hgood := ae_cycGood' hS.space.ppp
  have hP := plan5_planFin n β tn u β' i hlog
  obtain ⟨Φ1, hΦ1, hS1⟩ := exists_phi_KA (β := β) n tn u β' i hlog hi1 hiI
  obtain ⟨Φ2, hΦ2, hS2⟩ := exists_phi_KAE (β := β) n tn u β' i hlog hi1 hiI hj
  refine ⟨?_, measurableSet_escConSet n u i, ?_, ?_⟩
  · exact measurableSet_entries hP (K := escIstar n (escJ n) + 1)
      (by rw [plan5_K]; exact_mod_cast (by omega)) hΦ1 hS1
  · intro hT
    exact measurableSet_preimage_lam 𝒢₀ _ hP hNm hS.space.le Pr hgood
      (K := escIstar n (escJ n) + 1) (by rw [plan5_K]; exact_mod_cast (by omega)) hT hΦ1 hS1
  · intro hT
    exact measurableSet_preimage_lam 𝒢₀ _ hP hNm hS.space.le Pr hgood
      (K := escIstar n (escJ n) + 2) (by rw [plan5_K]) hT hΦ2 hS2

end ElboimSly.Paper.Escape
