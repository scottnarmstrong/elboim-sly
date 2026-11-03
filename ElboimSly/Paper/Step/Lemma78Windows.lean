/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Step.Lemma78Order

/-!
# Short gaps

Short gaps (ES22 §7), path level. The input `hfar` is the
conclusion of ES22 Lemma 6.8 and `hocc` is the occupation bound for the exceptional set
`{t : W₂(t) ∈ E_t}` (occupation before closing); the numerical conditions `hL1`, `hL2` are the
"for `n` large" inequalities `t'_k + 1 + t_n^{ε/3} < t_n^ε` and `2t'_k + 4 + t_n^{ε/3} < t_n^ε`.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Step

open ElboimSly.Paper

variable {d : ℕ} {Ω : Type*}

namespace Step78Data

variable (D : Step78Data d Ω) (ω : Ω)

/-- Short gaps. `bad t` stands for `W₂(t) ∈ E_t`; `L = t_n^ε`,
`g = t_n^{ε/3}`, `tk = t'_k`. -/
theorem gap_le {bad : ℝ → Prop} {L g tk : ℝ} (hg : 0 ≤ g)
    (_hL1 : tk + 1 + g < L) (hL2 : 2 * tk + 4 + g < L) (htk : 0 ≤ tk)
    (hocc : volume {t : ℝ | t ∈ Icc 0 (D.T : ℝ) ∧ bad t} ≤ ENNReal.ofReal g)
    (hfar : ∀ t ∈ Icc (2 * tk + 4) (D.T : ℝ), ¬ bad t →
      ∃ s ∈ Icc (t - tk) t, s ∈ D.farSet ω)
    {J : ℕ} (_hzJ : D.zeta J ω = (D.T : WithTop ℝ≥0)) {i : ℕ} (hi1 : 1 ≤ i) (hiJ : i ≤ J) :
    toR (D.zeta i ω) - toR (D.zp (i - 1) ω) ≤ L := by
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have hzT : toR (D.zeta (j + 1) ω) ≤ (D.T : ℝ) := by
    have := toR_mono (T := D.T) (le_refl _) (D.zeta_le_T ω (j + 1))
    rwa [toR_coe] at this
  set a : ℝ := toR (D.zp j ω) with ha
  have ha0 : 0 ≤ a := NNReal.coe_nonneg _
  by_cases hcase : a ≤ (D.T : ℝ) - L
  · -- a window of length L starting at a
    have hIlen : g < (a + L) - max (a + tk + 1) (2 * tk + 4) := by
      rcases le_total (a + tk + 1) (2 * tk + 4) with h | h
      · rw [max_eq_right h]; linarith
      · rw [max_eq_left h]; linarith
    set lo : ℝ := max (a + tk + 1) (2 * tk + 4) with hlo
    have hex : ∃ t ∈ Icc lo (a + L), ¬ (t ∈ Icc 0 (D.T : ℝ) ∧ bad t) := by
      by_contra hno
      push Not at hno
      have hsub : Icc lo (a + L) ⊆ {t : ℝ | t ∈ Icc 0 (D.T : ℝ) ∧ bad t} := hno
      have h1 := (measure_mono hsub).trans hocc
      rw [Real.volume_Icc] at h1
      have h2 := (ENNReal.ofReal_le_ofReal_iff hg).1 h1
      linarith
    obtain ⟨t, ht, hnb⟩ := hex
    have hlo1 : a + tk + 1 ≤ lo := le_max_left _ _
    have hlo2 : 2 * tk + 4 ≤ lo := le_max_right _ _
    have htT : t ≤ (D.T : ℝ) := by linarith [ht.2]
    have ht0 : 0 ≤ t := by linarith [ht.1]
    have hnb' : ¬ bad t := fun hb => hnb ⟨⟨ht0, htT⟩, hb⟩
    obtain ⟨s, hs, hsfar⟩ := hfar t ⟨by linarith [ht.1], htT⟩ hnb'
    have hs0 : 0 ≤ s := by linarith [hs.1, ht.1, hlo2, htk]
    have hsa : a ≤ s := by linarith [hs.1, ht.1, hlo1]
    have hsL : s ≤ a + L := by linarith [hs.2, ht.2]
    -- ζ_{j+1} ≤ s
    have hzp : D.zp j ω = ((D.zp j ω).untopD 0 : ℝ≥0) := coe_untopD_of_le (D.zp_le_T ω j)
    have hle : D.zeta (j + 1) ω ≤ ((s.toNNReal : ℝ≥0) : WithTop ℝ≥0) := by
      refine le_trans (min_le_right _ _) ?_
      refine iInf₂_le s.toNNReal ⟨?_, ?_⟩
      · rw [Real.coe_toNNReal _ hs0]; exact hsfar
      · rw [hzp, WithTop.coe_le_coe, ← NNReal.coe_le_coe, Real.coe_toNNReal _ hs0]
        exact hsa
    have := toR_mono (T := s.toNNReal) (le_refl _) hle
    rw [toR_coe, Real.coe_toNNReal _ hs0] at this
    linarith
  · push Not at hcase
    linarith

/-- On `{J ≤ n³}` (some `ζ_J = t'_n` with `J ≤ n³`), `|𝔓_n| < 3.9^n`: the deterministic part of the
proof of ES22 Lemma 7.8, from covering fP_n and short gaps; `hnum` is
`n³ (t_n^ε + 3.89^n) < 3.9^n` ("for `n` large"). -/
theorem pn_small {W1 : ℝ → Fin d → ℤ} {bad : ℝ → Prop} {L g tk : ℝ} (hg : 0 ≤ g)
    (hL1 : tk + 1 + g < L) (hL2 : 2 * tk + 4 + g < L) (htk : 0 ≤ tk) (_hL0 : 0 ≤ L)
    (hocc : volume {t : ℝ | t ∈ Icc 0 (D.T : ℝ) ∧ bad t} ≤ ENNReal.ofReal g)
    (hfar : ∀ t ∈ Icc (2 * tk + 4) (D.T : ℝ), ¬ bad t →
      ∃ s ∈ Icc (t - tk) t, s ∈ D.farSet ω)
    (hV : D.V ω = W1 '' Icc 0 (D.T : ℝ))
    (hJ : ∃ J : ℕ, 1 ≤ J ∧ J ≤ D.n ^ 3 ∧ D.zeta J ω = (D.T : WithTop ℝ≥0))
    (hnum : (D.n : ℝ) ^ 3 * (L + (389 / 100 : ℝ) ^ D.n) < (39 / 10 : ℝ) ^ D.n) :
    volume {s : ℝ | s ∈ Icc 0 (D.T : ℝ) ∧ ∃ s₁ ∈ Icc 0 (D.T : ℝ),
        ‖W1 s₁ - D.path ω s‖ ≤ (19 / 10 : ℝ) ^ D.n} < ENNReal.ofReal ((39 / 10 : ℝ) ^ D.n) := by
  obtain ⟨J, hJ1, hJn, hzJ⟩ := hJ
  refine lt_of_le_of_lt (D.cover_path ω hJ1 hzJ hV) ?_
  rw [ENNReal.ofReal_lt_ofReal_iff (by positivity)]
  have hsum : ∑ i ∈ Finset.Icc 1 J, (toR (D.zeta i ω) - toR (D.zp (i - 1) ω)) ≤ J * L := by
    calc _ ≤ ∑ _i ∈ Finset.Icc 1 J, L :=
          Finset.sum_le_sum fun i hi => gap_le D ω (bad := bad) hg hL1 hL2 htk hocc hfar hzJ
            (Finset.mem_Icc.1 hi).1 (Finset.mem_Icc.1 hi).2
      _ = J * L := by simp
  have hJn' : (J : ℝ) ≤ (D.n : ℝ) ^ 3 := by exact_mod_cast hJn
  have hc : 0 ≤ (389 / 100 : ℝ) ^ D.n := by positivity
  have hJ1' : (1 : ℝ) ≤ J := by exact_mod_cast hJ1
  calc _ ≤ J * L + ((J : ℝ) - 1) * (389 / 100 : ℝ) ^ D.n := by linarith
    _ ≤ (D.n : ℝ) ^ 3 * L + (D.n : ℝ) ^ 3 * (389 / 100 : ℝ) ^ D.n := by
        have : ((J : ℝ) - 1) * (389 / 100 : ℝ) ^ D.n ≤ (D.n : ℝ) ^ 3 * (389 / 100 : ℝ) ^ D.n :=
          mul_le_mul_of_nonneg_right (by linarith) hc
        nlinarith
    _ < _ := by nlinarith

end Step78Data

end ElboimSly.Paper.Step

end
