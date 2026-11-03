/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycThitDriven
public import ElboimSly.Foundations.Cyclic.DrivenMain
public import Mathlib

/-!
# ES22 Lemma 2.1: the hitting time bound and Step 1

ES22 Lemma 2.1. For `x ∈ cycCF` and `0 < t < treg^x`, with
`h = drivenThit b x t`:

* `drivenThit_le_treg`: `h ≤ treg^x`;
* `miss`: before `h`, no pair `(s, s')` is a hit;
* `step1`: left limits `W(u-)`, `W(u'-)` of a pair `u ∈ (t, h]`, `u' ∈ (0, t]`, `u - u' ∈ βℤ_{≥1}`
  are far apart (Step 1 of the written proof).
-/

@[expose] public section

open Filter Topology Set MeasureTheory
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

variable {d : ℕ} {b : ℝ≥0} {x : ℝ≥0 → Fin d → ℤ}

theorem norm_le_one_of_unit {v : Fin d → ℤ} (hv : IsUnitStep v) : ‖v‖ ≤ 1 := by
  refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => ?_
  rw [Int.norm_eq_abs]
  have h1 : |v i| ≤ ∑ j, |v j| :=
    Finset.single_le_sum (f := fun j => |v j|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i)
  have h2 : ∑ j, |v j| = 1 := hv
  have : |v i| ≤ 1 := h1.trans h2.le
  exact_mod_cast this

/-- `h = t_hit(t) ≤ treg^x`. -/
theorem drivenThit_le_treg (hb : 0 < b) (hx : x ∈ CycCF b) {t : ℝ≥0} (ht0 : 0 < t)
    (htτ : (t : ℝ≥0∞) < drivenTreg b x) : drivenThit b x t ≤ drivenTreg b x := by
  have hxr : IsRegPath x := hx.1.toIsRegPath
  by_cases hτ : drivenTreg b x = ⊤
  · rw [hτ]; exact le_top
  obtain ⟨τ0, hτ0⟩ : ∃ τ0 : ℝ≥0, drivenTreg b x = τ0 := ⟨_, (ENNReal.coe_toNNReal hτ).symm⟩
  obtain ⟨ε, hε, hεV⟩ := drivenRegenFrom_after b hb hxr hτ0
  obtain ⟨ε1, hε1, hεW⟩ : ∃ ε1 : ℝ≥0, 0 < ε1 ∧ ∀ u : ℝ≥0, u < ε1 → drivenWalk b x u = 0 := by
    have h := (drivenWalk_isRegPath hxr hb).rc 0
    rw [drivenWalk_zero hxr hb] at h
    obtain ⟨c, hc, hsub⟩ := (mem_nhdsGE_iff_exists_Ico_subset (a := (0 : ℝ≥0))).1 h
    exact ⟨c, hc, fun u hu => hsub ⟨zero_le, hu⟩⟩
  have htτ' : t < τ0 := by
    have := htτ; rw [hτ0] at this; exact_mod_cast this
  rcases pathTreg_top_or b (drivenWalk b x) with h | ⟨j, hj1, hj, -⟩
  · exact absurd h hτ
  have hτj : τ0 = j * b := by
    have : (τ0 : ℝ≥0∞) = ((j * b : ℝ≥0) : ℝ≥0∞) := by rw [← hτ0]; exact hj
    exact_mod_cast this
  rw [hτ0]
  refine ENNReal.le_of_forall_pos_le_add fun e he _ => ?_
  have hM : 0 < min (min ε ε1) (min t e) := lt_min (lt_min hε hε1) (lt_min ht0 he)
  set m : ℝ≥0 := min (min ε ε1) (min t e) / 2 with hm
  have hm0 : 0 < m := half_pos hM
  have hm2 : m < min (min ε ε1) (min t e) := half_lt_self hM
  have hmε : m < ε := hm2.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hmε1 : m < ε1 := hm2.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have hmt : m < t := hm2.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hme : m < e := hm2.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hmτ : (m : ℝ≥0∞) < drivenTreg b x := (by exact_mod_cast hmt : (m : ℝ≥0∞) < t).trans htτ
  have hmem : (τ0 + m : ℝ≥0) ∈ {s : ℝ≥0 | t < s ∧ ∃ k : ℤ, ∃ s' : ℝ≥0, (s' : ℝ) = s + k * b ∧
      drivenRegenAlpha b x t < s' ∧ s' < t ∧
      ‖drivenRegenFrom b x s - drivenRegenFrom b x s'‖ ≤ 1} := by
    refine ⟨htτ'.trans_le le_self_add, -(j : ℤ), m, ?_, ?_, hmt, ?_⟩
    · have : (τ0 : ℝ) = j * b := by exact_mod_cast hτj
      push_cast; rw [this]; ring
    · rw [drivenRegenAlpha_of_lt b x htτ]; exact hm0
    · rw [hεV m hmε, drivenRegenFrom_of_lt b x hmτ, hεW m hmε1]; simp
  have h1 : drivenThit b x t ≤ ((τ0 + m : ℝ≥0) : ℝ≥0∞) := by
    unfold drivenThit; exact iInf₂_le_of_le _ hmem le_rfl
  refine h1.trans ?_
  push_cast
  exact add_le_add le_rfl (by exact_mod_cast hme.le)

/-- Before `t_hit`, no pair `(s, s')` is a hit. -/
theorem miss (hb : 0 < b) (hx : x ∈ CycCF b) {t : ℝ≥0} (ht0 : 0 < t)
    (htτ : (t : ℝ≥0∞) < drivenTreg b x) {s s' : ℝ≥0} {k : ℤ} (hts : t < s)
    (hsh : (s : ℝ≥0∞) < drivenThit b x t) (hk : (s' : ℝ) = s + k * b) (h0 : 0 < s')
    (hst : s' < t) : ¬ ‖drivenWalk b x s - drivenWalk b x s'‖ ≤ 1 := by
  intro hle
  have hsτ : (s : ℝ≥0∞) < drivenTreg b x := hsh.trans_le (drivenThit_le_treg hb hx ht0 htτ)
  have ht' : (s' : ℝ≥0∞) < drivenTreg b x :=
    (by exact_mod_cast hst : (s' : ℝ≥0∞) < t).trans htτ
  have hmem : s ∈ {s : ℝ≥0 | t < s ∧ ∃ k : ℤ, ∃ s' : ℝ≥0, (s' : ℝ) = s + k * b ∧
      drivenRegenAlpha b x t < s' ∧ s' < t ∧
      ‖drivenRegenFrom b x s - drivenRegenFrom b x s'‖ ≤ 1} :=
    ⟨hts, k, s', hk, by rw [drivenRegenAlpha_of_lt b x htτ]; exact h0, hst, by
      rw [drivenRegenFrom_of_lt b x hsτ, drivenRegenFrom_of_lt b x ht']; exact hle⟩
  have : drivenThit b x t ≤ s := by
    unfold drivenThit; exact iInf₂_le_of_le _ hmem le_rfl
  exact absurd this (not_le.2 hsh)

/-- **Step 1** (left limits are far). -/
theorem step1 (hb : 0 < b) (hx : x ∈ CycCF b) {t : ℝ≥0} (ht0 : 0 < t)
    (htτ : (t : ℝ≥0∞) < drivenTreg b x) {u u' : ℝ≥0} {j : ℕ} (htu : t < u)
    (huh : (u : ℝ≥0∞) ≤ drivenThit b x t) (hu'0 : 0 < u') (hu't : u' ≤ t)
    (hu : u = u' + j * b) :
    ¬ ‖leftVal (drivenWalk b x) u - leftVal (drivenWalk b x) u'‖ ≤ 1 := by
  have hW := drivenWalk_isRegPath hx.1.toIsRegPath hb
  have hu0 : 0 < u := lt_of_le_of_lt zero_le htu
  have e1 := hW.eventually_leftVal hu0
  have e2 := hW.eventually_leftVal hu'0
  obtain ⟨l1, hl1m, hsub1⟩ := (mem_nhdsLT_iff_exists_Ioo_subset' hu0).1 e1
  obtain ⟨l2, hl2m, hsub2⟩ := (mem_nhdsLT_iff_exists_Ioo_subset' hu'0).1 e2
  have hl1 : l1 < u := hl1m
  have hl2 : l2 < u' := hl2m
  have hlt : max (max l1 t) (l2 + j * b) < u := by
    refine max_lt (max_lt hl1 htu) ?_
    rw [hu]; exact add_lt_add_left hl2 _
  obtain ⟨v, hv1, hv2⟩ := exists_between hlt
  have hv1' : max l1 t < v := lt_of_le_of_lt (le_max_left _ _) hv1
  have hv1'' : l2 + j * b < v := lt_of_le_of_lt (le_max_right _ _) hv1
  have hl1v : l1 < v := lt_of_le_of_lt (le_max_left _ _) hv1'
  have htv : t < v := lt_of_le_of_lt (le_max_right _ _) hv1'
  have hjv : (j : ℝ≥0) * b ≤ v := le_trans le_add_self hv1''.le
  have hvv : v - j * b + j * b = v := tsub_add_cancel_of_le hjv
  have hl2v : l2 < v - j * b := lt_tsub_iff_right.2 hv1''
  have hv'u : v - j * b < u' := by
    rw [tsub_lt_iff_right hjv]; rw [hu] at hv2; exact hv2
  intro hle
  refine miss hb hx ht0 htτ (k := -(j : ℤ)) htv (lt_of_lt_of_le (by exact_mod_cast hv2) huh) ?_
    (lt_of_le_of_lt zero_le hl2v) (hv'u.trans_le hu't) ?_
  · have : (v : ℝ) = ((v - j * b : ℝ≥0) : ℝ) + j * b := by exact_mod_cast hvv.symm
    push_cast; linarith
  · rw [hsub1 ⟨hl1v, hv2⟩, hsub2 ⟨hl2v, hv'u⟩]; exact hle

end ElboimSly.Cyclic

end
