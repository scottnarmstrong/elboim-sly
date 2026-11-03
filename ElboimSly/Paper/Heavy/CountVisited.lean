/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Heavy.JumpCount
public import ElboimSly.Paper.Heavy.Blocks

/-!
# Counting visited vertices

Supporting material for ES22 Lemma 6.4 (supplement).

* `IsCyclicPath.ncard_image_Icc_le`: a cyclic path with `n` jumps in `(a, b]` visits at most
  `n + 1` vertices during `[a, b]`.
* `ncard_heavyBlock_le`: a block of `ℬ_j` has at most `2^{jd}` vertices.
-/

@[expose] public section

open Filter Topology Set

namespace ElboimSly.Paper

variable {d : ℕ} {w : ℝ → Fin d → ℤ}

theorem IsCyclicPath.image_Icc_count (hw : IsCyclicPath w) :
    ∀ (n : ℕ) (a b : ℝ), 0 ≤ a → a ≤ b → (cycJumpSet w ∩ Ioc a b).ncard = n →
      (w '' Icc a b).Finite ∧ (w '' Icc a b).ncard ≤ n + 1 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro a b ha hab hn
  set S := cycJumpSet w ∩ Ioc a b with hS
  have hfin : S.Finite := (hw.fin b).subset fun x hx => ⟨hx.1, hx.2.2⟩
  by_cases hne : S.Nonempty
  · obtain ⟨r, hrS, hrmax⟩ := Set.exists_max_image S id hfin hne
    have hra : a < r := hrS.2.1
    have hrb : r ≤ b := hrS.2.2
    set S' := S \ {r} with hS'
    have hfin' : S'.Finite := hfin.sdiff
    have hcard' : S'.ncard + 1 = n := by
      rw [← hn]
      have := Set.ncard_sdiff_singleton_add_one hrS hfin
      simpa [hS'] using this
    have hlt : ∀ x ∈ S', x < r := fun x hx =>
      lt_of_le_of_ne (hrmax x hx.1) (by simpa using hx.2)
    have e2 : ∀ᶠ u in 𝓝[<] r, a < u ∧ u < r := by
      filter_upwards [Ioo_mem_nhdsLT hra] with u hu using hu
    have e3 : ∀ᶠ u in 𝓝[<] r, ∀ x ∈ S', x < u := by
      rw [Filter.eventually_all_finite hfin']
      intro x hx
      filter_upwards [Ioo_mem_nhdsLT (hlt x hx)] with u hu using hu.1
    obtain ⟨u, hu2, hu3⟩ := (e2.and e3).exists
    obtain ⟨hau, hur⟩ := hu2
    have hsub : cycJumpSet w ∩ Ioc a u ⊆ S' := by
      intro x hx
      refine ⟨⟨hx.1, hx.2.1, hx.2.2.trans (hur.le.trans hrb)⟩, ?_⟩
      simp only [mem_singleton_iff]
      exact ne_of_lt (lt_of_le_of_lt hx.2.2 hur)
    have hm : (cycJumpSet w ∩ Ioc a u).ncard ≤ S'.ncard := Set.ncard_le_ncard hsub hfin'
    obtain ⟨ihf, ihc⟩ := ih (cycJumpSet w ∩ Ioc a u).ncard (by omega) a u ha hau.le rfl
    have hbr : ∀ x ∈ Icc r b, w x = w r := by
      intro x hx
      refine hw.eq_of_no_jump (ha.trans hra.le) hx.1 fun y hy hyj => ?_
      have : y ∈ S := ⟨hyj, hra.trans hy.1, hy.2.trans hx.2⟩
      exact absurd (hrmax y this) (not_le.2 hy.1)
    have hmid : ∀ x ∈ Icc u r, x < r → w x = w u := by
      intro x hx hxr
      refine hw.eq_of_no_jump (ha.trans hau.le) hx.1 fun y hy hyj => ?_
      have hyS : y ∈ S := ⟨hyj, hau.trans hy.1, (hy.2.trans hx.2).trans hrb⟩
      have hyr : y ≠ r := ne_of_lt (lt_of_le_of_lt hy.2 hxr)
      exact absurd (hu3 y ⟨hyS, hyr⟩) (not_lt.2 hy.1.le)
    have hsubset : w '' Icc a b ⊆ w '' Icc a u ∪ {w r} := by
      rintro _ ⟨x, hx, rfl⟩
      rcases le_or_gt x u with hxu | hxu
      · exact Or.inl ⟨x, ⟨hx.1, hxu⟩, rfl⟩
      · rcases lt_or_ge x r with hxr | hxr
        · exact Or.inl ⟨u, ⟨hau.le, le_rfl⟩, (hmid x ⟨hxu.le, hxr.le⟩ hxr).symm⟩
        · exact Or.inr (hbr x ⟨hxr, hx.2⟩)
    have hfin2 : (w '' Icc a u ∪ {w r}).Finite := ihf.union (finite_singleton _)
    refine ⟨hfin2.subset hsubset, ?_⟩
    calc (w '' Icc a b).ncard ≤ (w '' Icc a u ∪ {w r}).ncard := Set.ncard_le_ncard hsubset hfin2
      _ ≤ (w '' Icc a u).ncard + ({w r} : Set _).ncard := Set.ncard_union_le _ _
      _ ≤ n + 1 := by simp; omega
  · have hn0 : n = 0 := by
      rw [← hn]; simp [Set.not_nonempty_iff_eq_empty.1 hne]
    have hconst : ∀ x ∈ Icc a b, w x = w a := fun x hx =>
      hw.eq_of_no_jump ha hx.1 fun y hy hyj => hne ⟨y, hyj, hy.1, hy.2.trans hx.2⟩
    have : w '' Icc a b ⊆ {w a} := by
      rintro _ ⟨x, hx, rfl⟩; exact hconst x hx
    refine ⟨(finite_singleton _).subset this, ?_⟩
    calc (w '' Icc a b).ncard ≤ ({w a} : Set _).ncard := Set.ncard_le_ncard this (finite_singleton _)
      _ ≤ n + 1 := by simp

theorem IsCyclicPath.ncard_image_Icc_le (hw : IsCyclicPath w) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    (w '' Icc a b).Finite ∧ (w '' Icc a b).ncard ≤ cycJumpCount w a b + 1 :=
  hw.image_Icc_count _ a b ha hab rfl

theorem ncard_heavyBlock_le (j : ℕ) (ι : Fin d → ℤ) :
    (heavyBlock j ι).Finite ∧ (heavyBlock j ι).ncard ≤ (2 ^ j) ^ d := by
  have hsub : heavyBlock j ι ⊆
      ↑(Fintype.piFinset fun c : Fin d => Finset.Ico (2 ^ j * ι c) (2 ^ j * ι c + 2 ^ j)) := by
    intro x hx
    simp only [Finset.mem_coe, Fintype.mem_piFinset, Finset.mem_Ico]
    intro c
    have hp : (0 : ℤ) < 2 ^ j := by positivity
    have h1 := Int.emod_add_mul_ediv (x c) (2 ^ j)
    have h3 := Int.emod_nonneg (x c) hp.ne'
    have h4 := Int.emod_lt_of_pos (x c) hp
    rw [hx c] at h1
    constructor <;> nlinarith
  have hfin := (Finset.finite_toSet _).subset hsub
  refine ⟨hfin, ?_⟩
  calc (heavyBlock j ι).ncard ≤ (↑(Fintype.piFinset fun c : Fin d =>
        Finset.Ico (2 ^ j * ι c) (2 ^ j * ι c + 2 ^ j)) : Set (Fin d → ℤ)).ncard :=
        Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    _ = (Fintype.piFinset fun c : Fin d =>
        Finset.Ico (2 ^ j * ι c) (2 ^ j * ι c + 2 ^ j)).card := Set.ncard_coe_finset _
    _ = (2 ^ j) ^ d := by
        rw [Fintype.card_piFinset]
        have h : ((2 : ℤ) ^ j).toNat = 2 ^ j := by
          have := Int.toNat_natCast (2 ^ j)
          push_cast at this
          exact this
        simp [Int.card_Ico, h]

end ElboimSly.Paper
