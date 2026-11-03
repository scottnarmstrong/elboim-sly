/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Heavy.NoFast

/-!
# Lemma 7.8, far lemma: block geometry

ES22 Lemma 6.8, "Cover of `V`": a translate `u + B` of a block of `ℬ_k` meets at most
`2^d` blocks of `ℬ_k`.
-/

@[expose] public section

open Set

namespace ElboimSly.Paper.Step

open ElboimSly ElboimSly.Paper

variable {d : ℕ}

/-- The blocks of `ℬ_k` meeting a set `A`. -/
def step78MeetBlocks (k : ℕ) (A : Set (Fin d → ℤ)) : Set (Fin d → ℤ) :=
  {ι' | ∃ x ∈ A, x ∈ heavyBlock k ι'}

theorem ediv_window {m x b : ℤ} (hb : 0 < b) (h1 : m ≤ x) (h2 : x < m + b) :
    m / b ≤ x / b ∧ x / b ≤ m / b + 1 := by
  refine ⟨Int.ediv_le_ediv hb h1, ?_⟩
  have : (m + 1 * b) / b = m / b + 1 := Int.add_mul_ediv_right m 1 hb.ne'
  rw [one_mul] at this
  rw [← this]
  exact Int.ediv_le_ediv hb h2.le

/-- A translate of a block meets at most `2^d` blocks of the same level. -/
theorem ncard_meetBlocks_translate_le (k : ℕ) (u ι : Fin d → ℤ) :
    (step78MeetBlocks k ((fun x => u + x) '' heavyBlock k ι)).Finite ∧
    (step78MeetBlocks k ((fun x => u + x) '' heavyBlock k ι)).ncard ≤ 2 ^ d := by
  classical
  have hb : (0 : ℤ) < 2 ^ k := by positivity
  set a : Fin d → ℤ := fun c => (u c + ι c * 2 ^ k) / 2 ^ k with ha
  let S : Finset (Fin d → ℤ) := Fintype.piFinset fun c => ({a c, a c + 1} : Finset ℤ)
  have hsub : step78MeetBlocks k ((fun x => u + x) '' heavyBlock k ι) ⊆ (S : Set (Fin d → ℤ)) := by
    rintro ι' ⟨x, ⟨y, hy, rfl⟩, hx⟩
    simp only [S, Finset.mem_coe, Fintype.mem_piFinset, Finset.mem_insert, Finset.mem_singleton]
    intro c
    have hyc : y c / 2 ^ k = ι c := hy c
    have h1 : ι c * 2 ^ k ≤ y c := by
      have := Int.mul_ediv_self_le (x := y c) (k := 2 ^ k) hb.ne'
      rw [hyc] at this; linarith
    have h2 : y c < ι c * 2 ^ k + 2 ^ k := by
      have := Int.lt_mul_ediv_self_add (x := y c) hb
      rw [hyc] at this; linarith
    have hw := ediv_window hb (m := u c + ι c * 2 ^ k) (x := (u + y) c) (by simp; linarith)
      (by simp; linarith)
    have hxc : (u + y) c / 2 ^ k = ι' c := hx c
    rw [hxc] at hw
    have hac : a c = (u c + ι c * 2 ^ k) / 2 ^ k := rfl
    omega
  have hfin : (S : Set (Fin d → ℤ)).Finite := S.finite_toSet
  refine ⟨hfin.subset hsub, (Set.ncard_le_ncard hsub hfin).trans ?_⟩
  rw [Set.ncard_coe_finset]
  calc S.card = ∏ c : Fin d, ({a c, a c + 1} : Finset ℤ).card := Fintype.card_piFinset _
    _ ≤ ∏ _c : Fin d, 2 := Finset.prod_le_prod fun c _ => Finset.card_le_two
    _ = 2 ^ d := by simp

end ElboimSly.Paper.Step

end
