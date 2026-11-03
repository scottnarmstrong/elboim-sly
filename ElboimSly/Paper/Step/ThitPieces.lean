/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Step.RelaxedStoppingApp
public import Mathlib

/-!
# Piecewise-constant sets are locally of type `[l, r)`

Structure of relaxed times; stopping times (a), (d): auxiliary facts used for the sets
`{s : ‖w s - w (s - jβ)‖ ≤ 1}` and `{s : α s ≤ c}` that appear in the stopping-time proof of
`thit(R)`.
-/

@[expose] public section

open Set

namespace ElboimSly.Paper

variable {d : ℕ}

/-- A single interval `[a, b)` is locally of type `[l, r)`. -/
theorem isLocIco_Ico (a b : ℝ) : IsLocIco (Ico a b) := by
  classical
  intro M
  by_cases hab : a < b
  · refine ⟨{(a, b)}, by simpa using hab, ?_⟩
    simp
  · refine ⟨∅, by simp, ?_⟩
    have : Ico a b = ∅ := Ico_eq_empty hab
    simp [this]

/-- A set whose membership only changes at the points of a finite set (on each bounded interval)
is locally of type `[l, r)`. -/
theorem isLocIco_of_pieces {S : Set ℝ}
    (hE : ∀ M : ℝ, ∃ E : Finset ℝ, 0 ∈ E ∧ (∀ x ∈ E, 0 ≤ x) ∧ (∃ x ∈ E, M < x) ∧
      ∀ a b : ℝ, 0 ≤ a → a ≤ b → (∀ x ∈ E, x ∉ Ioc a b) → (b ∈ S ↔ a ∈ S)) :
    IsLocIco S := by
  classical
  intro M
  obtain ⟨E, h0, hpos, ⟨x₀, hx₀, hMx₀⟩, hS⟩ := hE M
  refine ⟨(E ×ˢ E).filter
    (fun q : ℝ × ℝ => q.1 < q.2 ∧ (∀ x ∈ E, x ∉ Ioo q.1 q.2) ∧ q.1 ∈ S),
    fun p hp => (Finset.mem_filter.1 hp).2.1, ?_⟩
  ext t
  simp only [mem_inter_iff, mem_iUnion, Finset.mem_filter, Finset.mem_product, exists_prop,
    mem_Ico, mem_Icc]
  constructor
  · rintro ⟨ht, ht0, htM⟩
    have hEt : (E.filter (· ≤ t)).Nonempty := ⟨0, by simp [h0, ht0]⟩
    set e := (E.filter (· ≤ t)).max' hEt with he
    have hemem := Finset.max'_mem (E.filter (· ≤ t)) hEt
    simp only [Finset.mem_filter] at hemem
    have hmax : ∀ x ∈ E, x ≤ t → x ≤ e := fun x hx hxt =>
      Finset.le_max' (E.filter (· ≤ t)) x (by simp [hx, hxt])
    have hGt : (E.filter (t < ·)).Nonempty :=
      ⟨x₀, by simp only [Finset.mem_filter]; exact ⟨hx₀, by linarith⟩⟩
    set e' := (E.filter (t < ·)).min' hGt with he'
    have he'mem := Finset.min'_mem (E.filter (t < ·)) hGt
    simp only [Finset.mem_filter] at he'mem
    have hmin : ∀ x ∈ E, t < x → e' ≤ x := fun x hx hex =>
      Finset.min'_le (E.filter (t < ·)) x (by simp [hx, hex])
    have hno : ∀ x ∈ E, x ∉ Ioc e t := fun x hx hxm =>
      absurd (hmax x hx hxm.2) (not_le.2 hxm.1)
    have heS : e ∈ S := (hS e t (hpos e hemem.1) hemem.2 hno).1 ht
    refine ⟨⟨(e, e'), ⟨⟨hemem.1, he'mem.1⟩, ?_, ?_, heS⟩, ?_, ?_⟩, ht0, htM⟩
    · exact lt_of_le_of_lt hemem.2 he'mem.2
    · intro x hx hxm
      by_cases hxt : x ≤ t
      · exact absurd (hmax x hx hxt) (not_le.2 hxm.1)
      · exact absurd (hmin x hx (not_le.1 hxt)) (not_le.2 hxm.2)
    · exact hemem.2
    · exact lt_of_lt_of_le he'mem.2 le_rfl
  · rintro ⟨⟨⟨e, e'⟩, ⟨⟨he, he'⟩, hee', hno, heS⟩, hte, hte'⟩, ht0, htM⟩
    simp only at hee' hno heS hte hte'
    refine ⟨(hS e t (hpos e he) hte fun x hx hxm => hno x hx ⟨hxm.1, ?_⟩).2 heS, ht0, htM⟩
    exact lt_of_le_of_lt hxm.2 hte'

/-- The event times of `(w, α)` give a finite set on which the values of `w` and `α` only change. -/
theorem StepEventsFinite.const_form {w : ℝ → Fin d → ℤ} {α : ℝ → ℝ} (h : StepEventsFinite w α)
    (M : ℝ) : ∃ E : Finset ℝ, 0 ∈ E ∧ (∀ x ∈ E, 0 ≤ x) ∧ (∃ x ∈ E, M < x) ∧
      ∀ a b : ℝ, 0 ≤ a → a ≤ b → (∀ x ∈ E, x ∉ Ioc a b) → w b = w a ∧ α b = α a := by
  classical
  obtain ⟨E, h0, hpos, htop, hpiece, -⟩ := h M
  refine ⟨E, h0, hpos, htop, fun a b ha hab hno => ?_⟩
  have hEt : (E.filter (· ≤ a)).Nonempty := ⟨0, by simp [h0, ha]⟩
  set e := (E.filter (· ≤ a)).max' hEt with he
  have hemem := Finset.max'_mem (E.filter (· ≤ a)) hEt
  simp only [Finset.mem_filter] at hemem
  have hmax : ∀ x ∈ E, x ≤ a → x ≤ e := fun x hx hxt =>
    Finset.le_max' (E.filter (· ≤ a)) x (by simp [hx, hxt])
  have h1 := hpiece e hemem.1 a hemem.2 fun x hx => by
    by_cases hxa : x ≤ a
    · exact Or.inl (hmax x hx hxa)
    · exact Or.inr (not_le.1 hxa)
  have h2 := hpiece e hemem.1 b (hemem.2.trans hab) fun x hx => by
    by_cases hxa : x ≤ a
    · exact Or.inl (hmax x hx hxa)
    · right
      by_contra hxb
      exact hno x hx ⟨not_le.1 hxa, not_lt.1 hxb⟩
  exact ⟨h2.1.trans h1.1.symm, h2.2.trans h1.2.symm⟩

/-- The set `{s : α s ≤ c}` is locally of type `[l, r)`. -/
theorem isLocIco_alpha_le {w : ℝ → Fin d → ℤ} {α : ℝ → ℝ} (h : StepEventsFinite w α) (c : ℝ) :
    IsLocIco {s | α s ≤ c} := by
  refine isLocIco_of_pieces fun M => ?_
  obtain ⟨E, h0, hpos, htop, hc⟩ := h.const_form M
  refine ⟨E, h0, hpos, htop, fun a b ha hab hno => ?_⟩
  simp only [mem_ofPred_eq, (hc a b ha hab hno).2]

/-- The set `{s : ‖w s - w (s - jβ)‖ ≤ 1}`. -/
def stepVj (β : ℝ) (w : ℝ → Fin d → ℤ) (j : ℕ) : Set ℝ :=
  {s | ‖w s - w (s - j * β)‖ ≤ 1}

/-- The sets `{s : ‖w s - w (s - jβ)‖ ≤ 1}` are locally of type `[l, r)`, for a path that is
constant on the negative half-line. -/
theorem isLocIco_stepVj {β : ℝ} (hβ : 0 < β) {w : ℝ → Fin d → ℤ}
    (hneg : ∀ a b : ℝ, a ≤ b → b ≤ 0 → w b = w a)
    (hw : ∀ M : ℝ, ∃ E : Finset ℝ, 0 ∈ E ∧ (∀ x ∈ E, 0 ≤ x) ∧ (∃ x ∈ E, M < x) ∧
      ∀ a b : ℝ, 0 ≤ a → a ≤ b → (∀ x ∈ E, x ∉ Ioc a b) → w b = w a) (j : ℕ) :
    IsLocIco (stepVj β w j) := by
  classical
  refine isLocIco_of_pieces fun M => ?_
  obtain ⟨E, h0, hpos, ⟨x₀, hx₀, hMx₀⟩, hc⟩ := hw M
  have hjβ : 0 ≤ (j : ℝ) * β := by positivity
  refine ⟨E ∪ E.image (· + j * β), ?_, ?_, ⟨x₀, Finset.mem_union_left _ hx₀, hMx₀⟩, ?_⟩
  · exact Finset.mem_union_left _ h0
  · intro x hx
    rcases Finset.mem_union.1 hx with hx | hx
    · exact hpos x hx
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hx
      exact add_nonneg (hpos y hy) hjβ
  · intro a b ha hab hno
    have h1 : w b = w a := hc a b ha hab fun x hx => hno x (Finset.mem_union_left _ hx)
    have h2 : w (b - j * β) = w (a - j * β) := by
      by_cases hb : b - j * β ≤ 0
      · exact hneg _ _ (by linarith) hb
      · push Not at hb
        by_cases haj : 0 ≤ a - j * β
        · refine hc _ _ haj (by linarith) fun x hx hxm => hno (x + j * β)
            (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hx)) ⟨by linarith [hxm.1],
              by linarith [hxm.2]⟩
        · push Not at haj
          exfalso
          exact hno (0 + j * β) (Finset.mem_union_right _ (Finset.mem_image_of_mem _ h0))
            ⟨by linarith, by linarith⟩
    simp only [stepVj, mem_ofPred_eq, h1, h2]

end ElboimSly.Paper
