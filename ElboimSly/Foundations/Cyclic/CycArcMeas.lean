/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import Mathlib

/-!
# The arc test on the circle

Measurability of record functionals (a), the arc test: `θ ∈ c_δ((α, α'])`.

`circRep c ∈ (0, β]` is the representative of `c ∈ ℝ/βℤ`; it is measurable
(`AddCircle.measurableEquivIoc`). The key equivalence `exists_arc_iff`: some real `r ∈ (α, α']` has
`[r] = c` iff `α + circRep(c - [α]) ≤ α'`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

variable {β : ℝ} [Fact (0 < β)]

/-- The representative in `(0, β]` of a point of the circle. -/
noncomputable def circRep (c : AddCircle β) : ℝ := ((AddCircle.equivIoc β 0 c : Ioc (0 : ℝ) (0 + β)) : ℝ)

theorem measurable_circRep : Measurable (circRep : AddCircle β → ℝ) :=
  measurable_subtype_coe.comp (AddCircle.measurableEquivIoc β 0).measurable

theorem circRep_pos (c : AddCircle β) : 0 < circRep c := (AddCircle.equivIoc β 0 c).2.1

theorem circRep_le (c : AddCircle β) : circRep c ≤ β := by
  have := (AddCircle.equivIoc β 0 c).2.2
  unfold circRep
  simpa using this

theorem coe_circRep (c : AddCircle β) : ((circRep c : ℝ) : AddCircle β) = c :=
  AddCircle.coe_equivIoc

omit [Fact (0 < β)] in
theorem exists_int_of_coe_eq {s t : ℝ} (h : (s : AddCircle β) = (t : AddCircle β)) :
    ∃ n : ℤ, s = t + n * β := by
  have h1 : ((s - t : ℝ) : AddCircle β) = 0 := by
    rw [AddCircle.coe_sub, h, sub_self]
  obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff β).mp h1
  exact ⟨n, by rw [zsmul_eq_mul] at hn; linarith⟩

/-- If `s > 0` and `[s] = c`, then `circRep c ≤ s`. -/
theorem circRep_le_of_coe {c : AddCircle β} {s : ℝ} (hs : 0 < s) (h : (s : AddCircle β) = c) :
    circRep c ≤ s := by
  have h1 : ((s : ℝ) : AddCircle β) = ((circRep c : ℝ) : AddCircle β) := by
    rw [coe_circRep, h]
  obtain ⟨n, hn⟩ := exists_int_of_coe_eq h1
  have hb := circRep_le c
  have hp := circRep_pos c
  have hβ : 0 < β := Fact.out
  have hn0 : 0 ≤ n := by
    by_contra hneg
    push Not at hneg
    have : (n : ℝ) ≤ -1 := by exact_mod_cast (by omega : n ≤ -1)
    nlinarith
  have : (0 : ℝ) ≤ n := by exact_mod_cast hn0
  nlinarith

/-- The arc test: some `r ∈ (α, α']` is congruent to `c` iff `α + circRep (c - [α]) ≤ α'`. -/
theorem exists_arc_iff (c : AddCircle β) (α : ℝ≥0) (α' : ℝ≥0∞) :
    (∃ r : ℝ≥0, α < r ∧ (r : ℝ≥0∞) ≤ α' ∧ (((r : ℝ≥0) : ℝ) : AddCircle β) = c) ↔
      (α : ℝ≥0∞) + ENNReal.ofReal (circRep (c - ((α : ℝ) : AddCircle β))) ≤ α' := by
  have hp := circRep_pos (c - ((α : ℝ) : AddCircle β))
  constructor
  · rintro ⟨r, hr, hra, hrc⟩
    have hrα : (0 : ℝ) < (r : ℝ) - α := by
      have : (α : ℝ) < r := by exact_mod_cast hr
      linarith
    have h1 : (((r : ℝ) - α : ℝ) : AddCircle β) = c - ((α : ℝ) : AddCircle β) := by
      rw [AddCircle.coe_sub, hrc]
    have h2 := circRep_le_of_coe hrα h1
    refine le_trans ?_ hra
    have : (α : ℝ≥0∞) + ENNReal.ofReal (circRep (c - ((α : ℝ) : AddCircle β))) =
        ENNReal.ofReal ((α : ℝ) + circRep (c - ((α : ℝ) : AddCircle β))) := by
      symm
      rw [ENNReal.ofReal_add α.coe_nonneg hp.le, ENNReal.ofReal_coe_nnreal]
    rw [this, ← ENNReal.ofReal_coe_nnreal]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  · intro h
    set t := circRep (c - ((α : ℝ) : AddCircle β)) with ht
    refine ⟨(α : ℝ≥0) + t.toNNReal, ?_, ?_, ?_⟩
    · have : (0 : ℝ≥0) < t.toNNReal := Real.toNNReal_pos.mpr hp
      exact lt_add_of_pos_right _ this
    · refine le_trans (le_of_eq ?_) h
      rw [ENNReal.coe_add]
      congr 1
    · push_cast
      rw [Real.coe_toNNReal _ hp.le, AddCircle.coe_add, ht, coe_circRep]
      abel

end ElboimSly.Cyclic

end
