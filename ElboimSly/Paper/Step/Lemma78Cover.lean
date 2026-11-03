/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import Mathlib

/-!
# Covering `𝔓_n` (abstract form)

Covering fP_n (ES22 §7). For reals `ζ_i ≤ ζ'_i`, `ζ'_{i-1} ≤ ζ_i`
(`ζ'_0 = 0`) with `ζ_J = T`, and a set `P ⊆ [0,T]` containing no `r ∈ [ζ_i + c, ζ'_i)`, `i < J`,
`|P| ≤ ∑_{i=1}^J (ζ_i - ζ'_{i-1}) + (J-1) c`.
-/

@[expose] public section

open MeasureTheory Set

namespace ElboimSly.Paper.Step

/-- Covering fP_n. Here `z i = ζ_i`, `zp i = ζ'_i`, `c = 3.89^n`. -/
theorem step78_cover {z zp : ℕ → ℝ} {T c : ℝ} {P : Set ℝ} {J : ℕ} (hc : 0 ≤ c)
    (hzp0 : zp 0 = 0) (hlo : ∀ i, zp i ≤ z (i + 1)) (_hhi : ∀ i, 1 ≤ i → z i ≤ zp i)
    (hJ : 1 ≤ J) (hzJ : z J = T) (hP : P ⊆ Icc 0 T)
    (hfar : ∀ i, 1 ≤ i → i < J → ∀ r, z i + c ≤ r → r < zp i → r ∉ P) :
    volume P ≤ ENNReal.ofReal
      (∑ i ∈ Finset.Icc 1 J, (z i - zp (i - 1)) + ((J : ℝ) - 1) * c) := by
  have hnn : ∀ m, 0 ≤ ∑ i ∈ Finset.Icc 1 m, (z i - zp (i - 1)) := by
    intro m
    refine Finset.sum_nonneg fun i hi => ?_
    obtain ⟨h1, _⟩ := Finset.mem_Icc.1 hi
    have := hlo (i - 1)
    rw [Nat.sub_add_cancel h1] at this
    linarith
  have key : ∀ m, 1 ≤ m → m ≤ J → volume (P ∩ Ico 0 (z m)) ≤ ENNReal.ofReal
      (∑ i ∈ Finset.Icc 1 m, (z i - zp (i - 1)) + ((m : ℝ) - 1) * c) := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base =>
      intro _
      have : P ∩ Ico 0 (z 1) ⊆ Ico 0 (z 1) := inter_subset_right
      refine (measure_mono this).trans ?_
      simp [hzp0]
    | succ m hm ih =>
      intro hmJ
      have ih := ih (by omega)
      have hsub : P ∩ Ico 0 (z (m + 1)) ⊆ (P ∩ Ico 0 (z m)) ∪ Ico (z m) (z m + c) ∪
          Ico (zp m) (z (m + 1)) := by
        intro r ⟨hrP, hr0, hr1⟩
        by_cases h1 : r < z m
        · exact Or.inl (Or.inl ⟨hrP, hr0, h1⟩)
        · push Not at h1
          by_cases h2 : r < z m + c
          · exact Or.inl (Or.inr ⟨h1, h2⟩)
          · push Not at h2
            by_cases h3 : r < zp m
            · exact absurd hrP (hfar m hm (by omega) r h2 h3)
            · push Not at h3
              exact Or.inr ⟨h3, hr1⟩
      refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
      refine (add_le_add ((measure_union_le _ _).trans (add_le_add ih le_rfl)) le_rfl).trans ?_
      rw [Real.volume_Ico, Real.volume_Ico]
      have e1 : 0 ≤ z m + c - z m := by linarith
      have hz : zp m ≤ z (m + 1) := hlo m
      have e2 : 0 ≤ z (m + 1) - zp m := by linarith
      have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
      have hq : 0 ≤ ((m : ℝ) - 1) * c := mul_nonneg (by linarith) hc
      have hs0 := hnn m
      rw [← ENNReal.ofReal_add (by linarith) e1, ← ENNReal.ofReal_add (by linarith) e2]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [Finset.sum_Icc_succ_top (by omega)]
      push_cast
      linarith
  have hsub : P ⊆ (P ∩ Ico 0 (z J)) ∪ {T} := by
    intro r hr
    have := hP hr
    by_cases h : r < T
    · exact Or.inl ⟨hr, this.1, hzJ ▸ h⟩
    · exact Or.inr (le_antisymm this.2 (not_lt.1 h))
  calc volume P ≤ volume (P ∩ Ico 0 (z J)) + volume ({T} : Set ℝ) :=
        (measure_mono hsub).trans (measure_union_le _ _)
    _ ≤ _ := by
        rw [Real.volume_singleton, add_zero]
        exact key J hJ le_rfl

end ElboimSly.Paper.Step

end
