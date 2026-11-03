/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycSchemeDrvDef
public import Mathlib

/-!
# The driving scheme (b): `v ↦ {w, w + v}` is a bijection onto the edges at `w`

The driving scheme (b), "The map `v ↦ {w, w + v}` is a bijection from `𝒟` onto the edges
at `w`".
-/

@[expose] public section

open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

open SRW

variable {d : ℕ}

theorem Dir.vec_apply_fst (v : Dir d) : v.vec v.1 = if v.2 then 1 else -1 := by
  simp [Dir.vec]

theorem Dir.vec_injective : Function.Injective (Dir.vec : Dir d → Fin d → ℤ) := by
  rintro ⟨i, b⟩ ⟨i', b'⟩ h
  have h1 := congrFun h i
  by_cases hi : i = i'
  · subst hi
    cases b <;> cases b' <;> simp_all [Dir.vec]
  · exfalso
    simp [Dir.vec, Pi.single_eq_of_ne hi] at h1
    split_ifs at h1; simp_all

theorem stepEdge_injective (w : Fin d → ℤ) : Function.Injective (stepEdge w) := by
  intro v v' h
  have h1 : s(w, w + v.vec) = s(w, w + v'.vec) := congrArg Subtype.val h
  rw [Sym2.congr_right] at h1
  exact Dir.vec_injective (add_left_cancel h1)

theorem exists_stepEdge (w : Fin d → ℤ) (e : Edge d) (he : Edge.Mem w e) :
    ∃ v : Dir d, stepEdge w v = e := by
  obtain ⟨u, u', hu, hadj⟩ := e.2
  have hw : w ∈ e.1 := he
  rw [hu, Sym2.mem_iff] at hw
  -- the other endpoint `x` of `e` satisfies `s(w, x) = e` and `‖w - x‖₁ = 1`
  obtain ⟨x, hx, hxe⟩ : ∃ x : Fin d → ℤ, ∑ i, |w i - x i| = 1 ∧ e.1 = s(w, x) := by
    rcases hw with rfl | rfl
    · exact ⟨u', hadj, hu⟩
    · refine ⟨u, ?_, by rw [hu, Sym2.eq_swap]⟩
      have : ∑ i, |w i - u i| = ∑ i, |u i - w i| := Finset.sum_congr rfl fun i _ => abs_sub_comm _ _
      rw [this]; exact hadj
  -- some coordinate differs by exactly one
  have hpos : ∃ i, x i ≠ w i := by
    by_contra hcon
    push Not at hcon
    have : ∑ i, |w i - x i| = 0 := Finset.sum_eq_zero fun i _ => by simp [hcon i]
    omega
  obtain ⟨i, hi⟩ := hpos
  have hle : |w i - x i| ≤ 1 := by
    rw [← hx]
    exact Finset.single_le_sum (f := fun j => |w j - x j|) (fun j _ => abs_nonneg _)
      (Finset.mem_univ i)
  have hge : 1 ≤ |w i - x i| := by
    have : w i - x i ≠ 0 := sub_ne_zero.2 (Ne.symm hi)
    exact Int.one_le_abs this
  have habs : |w i - x i| = 1 := le_antisymm hle hge
  have hothers : ∀ j, j ≠ i → x j = w j := by
    intro j hj
    have h1 : ∑ k, |w k - x k| = |w i - x i| + ∑ k ∈ Finset.univ.erase i, |w k - x k| :=
      (Finset.add_sum_erase _ _ (Finset.mem_univ i)).symm
    have h2 : ∑ k ∈ Finset.univ.erase i, |w k - x k| = 0 := by omega
    have h3 := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => abs_nonneg _)).1 h2 j
      (Finset.mem_erase.2 ⟨hj, Finset.mem_univ j⟩)
    simpa [sub_eq_zero, eq_comm] using h3
  have hx' : x = w + (Dir.vec (i, decide (x i = w i + 1))) := by
    funext j
    by_cases hj : j = i
    · subst hj
      simp only [Pi.add_apply, Dir.vec]
      rw [Pi.single_eq_same]
      rcases abs_eq (zero_le_one' ℤ) |>.1 habs with h | h <;>
        by_cases hd : x j = w j + 1 <;> simp [hd] <;> omega
    · simp [Dir.vec, Pi.single_eq_of_ne hj, hothers j hj]
  refine ⟨(i, decide (x i = w i + 1)), Subtype.ext ?_⟩
  show s(w, w + Dir.vec (i, decide (x i = w i + 1))) = e.1
  rw [hxe, ← hx']

end ElboimSly.Cyclic

end
