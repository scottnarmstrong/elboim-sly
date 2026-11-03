/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Step.NaturalCouplingLaw
public import Mathlib

/-!
# The concatenated walk at an intermediate time

Laws in the natural coupling, used in ES22 Lemma 7.3 and ES22 Lemma 7.4 ("on `⋂ 𝒜_i`,
`W̃(jh) = ∑_{i≤j} X_i`, and for `s ∈ [(j-1)h, jh]`, `W̃(s) = ∑_{i<j} X_i + W_j(s-(j-1)h)`").

`stepCatList_range'_apply` evaluates the iterated concatenation `stepCatList` of the pairs
`(s i, Z i)` at a time `u` lying in the `j`-th block; `stepNatTilde_apply` is the form for the
natural coupling, and `exists_block` finds the block of a time.
-/

@[expose] public section

open scoped NNReal

namespace ElboimSly.Paper.Step

open ElboimSly.Paper

/-- The iterated concatenation of the pairs `(s i, Z i)`, `i ∈ [a, a+m)`, evaluated at a time in
the `j`-th block, is `∑_{i<j} Z_i(s_i) + Z_j(u - S_j)`. -/
theorem stepCatList_range'_apply {V : Type*} [AddCommMonoid V] (s : ℕ → ℝ≥0)
    (Z : ℕ → ℝ≥0 → V) :
    ∀ (m a j : ℕ) (u : ℝ≥0), 1 ≤ m → a ≤ j → j < a + m →
      (j = a ∨ ∑ i ∈ Finset.Ico a j, s i < u) →
      (j + 1 < a + m → u ≤ ∑ i ∈ Finset.Ico a (j + 1), s i) →
      stepCatList ((List.range' a m).map fun i => (s i, Z i)) u =
        ∑ i ∈ Finset.Ico a j, Z i (s i) + Z j (u - ∑ i ∈ Finset.Ico a j, s i) := by
  intro m
  induction m with
  | zero => intro a j u h; omega
  | succ m ih =>
    intro a j u _ haj hjm hlow hup
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · have hja : j = a := by omega
      subst hja
      simp [List.range'_succ, stepCatList]
    · obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      have hl2 : (List.range' (a + 1) (m' + 1)).map (fun i => (s i, Z i)) =
          (s (a + 1), Z (a + 1)) ::
            (List.range' (a + 1 + 1) m').map (fun i => (s i, Z i)) := by
        simp [List.range'_succ]
      have hlist : (List.range' a (m' + 1 + 1)).map (fun i => (s i, Z i)) =
          (s a, Z a) :: (s (a + 1), Z (a + 1)) ::
            (List.range' (a + 1 + 1) m').map (fun i => (s i, Z i)) := by
        simp [List.range'_succ]
      rw [hlist, stepCatList, ← hl2]
      rcases Nat.eq_or_lt_of_le haj with hja | hja
      · subst hja
        have : u ≤ s a := by
          have := hup (by omega)
          simpa [Finset.sum_Ico_succ_top] using this
        simp [stepCat_of_le _ _ this]
      · have hsa : s a ≤ ∑ i ∈ Finset.Ico a j, s i := by
          rw [Finset.sum_eq_sum_Ico_succ_bot (by omega)]
          exact le_self_add
        have hlt : s a < u := by
          rcases hlow with h | h
          · omega
          · exact lt_of_le_of_lt hsa h
        rw [stepCat_of_gt _ _ hlt]
        have hIH := ih (a + 1) j (u - s a) (by omega) (by omega) (by omega)
          (by
            rcases hlow with h | h
            · omega
            · right
              rw [Finset.sum_eq_sum_Ico_succ_bot (by omega)] at h
              rw [lt_tsub_iff_left]; exact h)
          (by
            intro hj1
            have := hup (by omega)
            rw [Finset.sum_eq_sum_Ico_succ_bot (by omega)] at this
            rw [tsub_le_iff_left]; exact this)
        rw [hIH, Finset.sum_eq_sum_Ico_succ_bot (by omega : a < j),
          Finset.sum_eq_sum_Ico_succ_bot (by omega : a < j), tsub_tsub, add_assoc]

variable {d : ℕ}

/-- The block decomposition of `W̃`: for `j < ℓ` and `u` with `S_j < u` or `j = 0`, and
`u ≤ S_{j+1}` unless `j` is the last block. -/
theorem stepNatTilde_apply (β : ℝ) (a : ℝ≥0) (s : ℕ → ℝ≥0) (ℓ : ℕ)
    (Y : ℝ≥0 → Fin d → ℤ) (j : ℕ) (u : ℝ≥0) (hj : j < ℓ)
    (hlow : j = 0 ∨ stepPartial s j < u)
    (hup : j + 1 < ℓ → u ≤ stepPartial s (j + 1)) :
    stepNatTilde β a s ℓ Y u =
      ∑ i ∈ Finset.range j, stepWalkZ β a s Y i (s i) +
        stepWalkZ β a s Y j (u - stepPartial s j) := by
  have hP : ∀ j, stepPartial s j = ∑ i ∈ Finset.Ico 0 j, s i := fun j => by
    rw [stepPartial, Finset.range_eq_Ico]
  have h := stepCatList_range'_apply (V := Fin d → ℤ) s (stepWalkZ β a s Y) ℓ 0 j u (by omega)
    (by omega) (by omega) (by rw [← hP]; exact hlow)
    (fun h => by rw [← hP]; exact hup (by omega))
  rw [← hP] at h
  rw [Finset.range_eq_Ico]
  simpa [stepNatTilde, List.range_eq_range'] using h

/-- Every time lies in some block `j < ℓ` (for `ℓ ≥ 1`). -/
theorem exists_block (s : ℕ → ℝ≥0) (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (u : ℝ≥0) :
    ∃ j, j < ℓ ∧ (j = 0 ∨ stepPartial s j < u) ∧
      (j + 1 < ℓ → u ≤ stepPartial s (j + 1)) := by
  classical
  obtain ⟨hle, hP, hgr⟩ := (Nat.findGreatest_eq_iff
    (P := fun j => stepPartial s j < u) (k := ℓ - 1)).1 rfl
  refine ⟨Nat.findGreatest (fun j => stepPartial s j < u) (ℓ - 1), by omega, ?_, fun hlt => ?_⟩
  · by_cases h : Nat.findGreatest (fun j => stepPartial s j < u) (ℓ - 1) = 0
    · exact Or.inl h
    · exact Or.inr (hP h)
  · exact not_lt.1 (hgr (Nat.lt_succ_self _) (by omega))

end ElboimSly.Paper.Step
