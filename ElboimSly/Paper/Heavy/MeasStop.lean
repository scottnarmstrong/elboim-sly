/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Heavy.Entrance
public import Mathlib.Probability.Process.Stopping

/-!
# Stopping times for adapted cyclic paths: entrance times

Measurability (a), first part.

`AdaptedCyclic f w` says that `w : Ω → ℝ → ℤ^d` consists of cyclic paths and is adapted to the
filtration `f` (indexed by `ℝ≥0`).  The same framework covers the regenerated walk with its
filtration, and (taking `Ω` the path space with the natural filtration) the measurability of the
functionals on the space of cyclic paths (measurability (d)).

* `entranceTime_le_iff`: `ξ_A(w) ≤ t` iff `w t ∈ A` or `w q ∈ A` for a rational `q ∈ [0, t)`.
* `AdaptedCyclic.isStoppingTime_entrance`: `ξ_A` is a stopping time.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Paper

open ElboimSly

variable {d : ℕ}

theorem entranceTime_eq_top_of_empty {w : ℝ → Fin d → ℤ} {A : Set (Fin d → ℤ)}
    (h : ∀ s : ℝ, 0 ≤ s → w s ∉ A) : entranceTime w A = ⊤ :=
  le_antisymm le_top (le_iInf₂ fun s hs => (h s hs.1 hs.2).elim)

/-- `ξ_A(w) ≤ t` iff `w t ∈ A` or `w q ∈ A` for a rational `q ∈ [0, t)`. -/
theorem entranceTime_le_iff {w : ℝ → Fin d → ℤ} (hw : IsCyclicPath w) {A : Set (Fin d → ℤ)}
    {t : ℝ} (ht : 0 ≤ t) :
    entranceTime w A ≤ ENNReal.ofReal t ↔
      w t ∈ A ∨ ∃ q : ℚ, 0 ≤ (q : ℝ) ∧ (q : ℝ) < t ∧ w q ∈ A := by
  constructor
  · intro h
    have hne : ∃ s : ℝ, 0 ≤ s ∧ w s ∈ A := by
      by_contra hno
      push Not at hno
      rw [entranceTime_eq_top_of_empty hno] at h
      exact absurd h (by simp)
    obtain ⟨s, hs0, hsA⟩ := hne
    obtain ⟨s'', h0, -, hmem, heq⟩ := exists_entrance_real hw hs0 hsA
    rw [heq] at h
    have hst : s'' ≤ t := (ENNReal.ofReal_le_ofReal_iff ht).1 h
    rcases hst.eq_or_lt with rfl | hlt
    · exact Or.inl hmem
    · right
      obtain ⟨u, hu, hsub⟩ := mem_nhdsGE_iff_exists_Ico_subset.1 (hw.rc s'' h0)
      obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show s'' < min t u from
        lt_min hlt (mem_Ioi.1 hu))
      have hqu : w q = w s'' := hsub ⟨hq1.le, lt_of_lt_of_le hq2 (min_le_right _ _)⟩
      exact ⟨q, by linarith, lt_of_lt_of_le hq2 (min_le_left _ _), hqu ▸ hmem⟩
  · rintro (h | ⟨q, hq0, hqt, hq⟩)
    · exact entranceTime_le_of_mem ht h
    · exact (entranceTime_le_of_mem hq0 hq).trans (ENNReal.ofReal_le_ofReal hqt.le)

variable {Ω : Type*} {m : MeasurableSpace Ω}

/-- `w` is a family of cyclic paths adapted to the filtration `f`. -/
structure AdaptedCyclic (f : Filtration ℝ≥0 m) (w : Ω → ℝ → Fin d → ℤ) : Prop where
  path : ∀ ω, IsCyclicPath (w ω)
  adapted : ∀ s : ℝ≥0, Measurable[f s] (fun ω => w ω (s : ℝ))

variable {f : Filtration ℝ≥0 m} {w : Ω → ℝ → Fin d → ℤ}

theorem AdaptedCyclic.measurable_at (h : AdaptedCyclic f w) {s : ℝ} (hs : 0 ≤ s) {t : ℝ≥0}
    (hst : s ≤ t) : Measurable[f t] (fun ω => w ω s) := by
  have h1 := h.adapted s.toNNReal
  rw [Real.coe_toNNReal s hs] at h1
  exact h1.mono (f.mono (by rw [← NNReal.coe_le_coe, Real.coe_toNNReal s hs]; exact hst)) le_rfl

theorem AdaptedCyclic.measurableSet_mem (h : AdaptedCyclic f w) {s : ℝ} (hs : 0 ≤ s) {t : ℝ≥0}
    (hst : s ≤ t) (A : Set (Fin d → ℤ)) : MeasurableSet[f t] {ω | w ω s ∈ A} :=
  (h.measurable_at hs hst) (A.to_countable.measurableSet)

/-- Measurability (a): `ξ_A(W)` is a stopping time. -/
theorem AdaptedCyclic.isStoppingTime_entrance (h : AdaptedCyclic f w) (A : Set (Fin d → ℤ)) :
    IsStoppingTime f (fun ω => entranceTime (w ω) A) := by
  intro i
  have hset : {ω | entranceTime (w ω) A ≤ (i : WithTop ℝ≥0)} =
      {ω | w ω (i : ℝ) ∈ A} ∪ ⋃ q : {q : ℚ // 0 ≤ (q : ℝ) ∧ (q : ℝ) < i},
        {ω | w ω (q.1 : ℝ) ∈ A} := by
    ext ω
    have := entranceTime_le_iff (h.path ω) (A := A) (NNReal.coe_nonneg i)
    simp only [ENNReal.ofReal_coe_nnreal] at this
    simp only [mem_ofPred_eq, mem_union, mem_iUnion]
    rw [show ((i : WithTop ℝ≥0)) = (i : ℝ≥0∞) from rfl, this]
    constructor
    · rintro (h1 | ⟨q, h1, h2, h3⟩)
      · exact Or.inl h1
      · exact Or.inr ⟨⟨q, h1, h2⟩, h3⟩
    · rintro (h1 | ⟨q, h3⟩)
      · exact Or.inl h1
      · exact Or.inr ⟨q.1, q.2.1, q.2.2, h3⟩
  have key : MeasurableSet[f i] ({ω | w ω (i : ℝ) ∈ A} ∪ ⋃ q : {q : ℚ // 0 ≤ (q : ℝ) ∧ (q : ℝ) < i},
        {ω | w ω (q.1 : ℝ) ∈ A}) := by
    refine (h.measurableSet_mem (NNReal.coe_nonneg i) le_rfl A).union
      (MeasurableSet.iUnion fun q => h.measurableSet_mem q.2.1 q.2.2.le A)
  exact (congrArg (MeasurableSet[f i]) hset).mpr key

end ElboimSly.Paper
