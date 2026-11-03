/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Step.Lemma78Closing
public import ElboimSly.Paper.Step.Lemma78Order
public import ElboimSly.Paper.Step.ZetaPath
public import Mathlib

/-!
# The three bad events of one excursion succeeds with probability at least frac12 for the fresh walk `W'_i`

One excursion succeeds with probability at least frac12, "Reduction to events of `W'_i`". For a frozen pair `(x, V)` the
events `E_cl`, `E_V`, `E_far` of the regenerated walk `y` are written with the time `s` ranging
over the countable grid `step78Grid` (rational times); for a right-continuous path this is the same
as the event over all times (`exists_grid_rc`), and it makes the events measurable.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Step

open ElboimSly.Paper

variable {d : ℕ}

/-- The rational times. -/
def step78Grid : Set ℝ≥0 := range fun q : ℚ => (q : ℝ).toNNReal

theorem step78Grid_countable : step78Grid.Countable := countable_range _

/-- A right-continuous path takes the same value at some rational time in `[s, b)`. -/
theorem exists_grid_rc {d : ℕ} {y : ℝ≥0 → Fin d → ℤ} (hy : ∀ s, ∀ᶠ u in 𝓝[≥] s, y u = y s)
    {s b : ℝ≥0} (hsb : s < b) : ∃ g ∈ step78Grid, s ≤ g ∧ g < b ∧ y g = y s := by
  obtain ⟨u', hu', hsub⟩ := mem_nhdsGE_iff_exists_Ico_subset.1 (hy s)
  have hm : s < min u' b := lt_min hu' hsb
  have hmR : (s : ℝ) < (min u' b : ℝ≥0) := by exact_mod_cast hm
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hmR
  have hq0 : (0 : ℝ) ≤ q := (NNReal.coe_nonneg s).trans hq1.le
  have hqq : (((q : ℝ).toNNReal : ℝ≥0) : ℝ) = q := Real.coe_toNNReal _ hq0
  have h1 : s ≤ (q : ℝ).toNNReal := by rw [← NNReal.coe_le_coe, hqq]; exact hq1.le
  have h2 : (q : ℝ).toNNReal < min u' b := by rw [← NNReal.coe_lt_coe, hqq]; exact hq2
  refine ⟨(q : ℝ).toNNReal, ⟨q, rfl⟩, h1, h2.trans_le (min_le_right _ _), ?_⟩
  exact hsub ⟨h1, h2.trans_le (min_le_left _ _)⟩

/-- `E_cl`: the walk `y` is at `0` at some `mβ`, `m ≥ 1`, `mβ < 4ⁿ`. -/
def step78Scl (d : ℕ) (β : ℝ) (n : ℕ) : Set (ℝ≥0 → Fin d → ℤ) :=
  {y | ∃ m : ℕ, 1 ≤ m ∧ (m : ℝ) * β < (4 : ℝ) ^ n ∧ y (((m : ℝ) * β).toNNReal) = 0}

/-- `E_V`: `x + y(s)` is within `1` of `V` for some (rational) `s < 4ⁿ`. -/
def step78Sv (n : ℕ) (x : Fin d → ℤ) (V : Set (Fin d → ℤ)) : Set (ℝ≥0 → Fin d → ℤ) :=
  {y | ∃ s ∈ step78Grid, (s : ℝ) < (4 : ℝ) ^ n ∧ ∃ v ∈ V, ‖x + y s - v‖ ≤ 1}

/-- `E_far`: `x + y(s)` is within `1.9ⁿ` of `V` for some (rational) `s ∈ [3.89ⁿ, 4ⁿ)`. -/
def step78Sfar (n : ℕ) (x : Fin d → ℤ) (V : Set (Fin d → ℤ)) : Set (ℝ≥0 → Fin d → ℤ) :=
  {y | ∃ s ∈ step78Grid, (389 / 100 : ℝ) ^ n ≤ s ∧ (s : ℝ) < (4 : ℝ) ^ n ∧
    ∃ v ∈ V, ‖x + y s - v‖ ≤ (19 / 10 : ℝ) ^ n}

/-- The union of the three events. -/
def step78Sbad (d : ℕ) (β : ℝ) (n : ℕ) (x : Fin d → ℤ) (V : Set (Fin d → ℤ)) :
    Set (ℝ≥0 → Fin d → ℤ) :=
  step78Scl d β n ∪ step78Sv n x V ∪ step78Sfar n x V

theorem measurableSet_step78Scl (β : ℝ) (n : ℕ) : MeasurableSet (step78Scl d β n) := by
  have : step78Scl d β n = ⋃ m : ℕ, {y | 1 ≤ m ∧ (m : ℝ) * β < (4 : ℝ) ^ n ∧
      y (((m : ℝ) * β).toNNReal) = 0} := by
    ext y; simp [step78Scl]
  rw [this]
  refine MeasurableSet.iUnion fun m => ?_
  by_cases h : 1 ≤ m ∧ (m : ℝ) * β < (4 : ℝ) ^ n
  · have : {y : ℝ≥0 → Fin d → ℤ | 1 ≤ m ∧ (m : ℝ) * β < (4 : ℝ) ^ n ∧
        y (((m : ℝ) * β).toNNReal) = 0} = {y | y (((m : ℝ) * β).toNNReal) = 0} := by
      ext y; simp [h]
    rw [this]
    exact measurableSet_eq_fun (measurable_pi_apply _) measurable_const
  · have : {y : ℝ≥0 → Fin d → ℤ | 1 ≤ m ∧ (m : ℝ) * β < (4 : ℝ) ^ n ∧
        y (((m : ℝ) * β).toNNReal) = 0} = ∅ := by
      ext y
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
      tauto
    rw [this]
    exact MeasurableSet.empty

theorem measurableSet_step78Sv (n : ℕ) (x : Fin d → ℤ) (V : Set (Fin d → ℤ)) :
    MeasurableSet (step78Sv n x V) := by
  have : step78Sv n x V = ⋃ s ∈ step78Grid, {y | (s : ℝ) < (4 : ℝ) ^ n ∧
      ∃ v ∈ V, ‖x + y s - v‖ ≤ 1} := by
    ext y
    simp only [step78Sv, mem_ofPred_eq, mem_iUnion, exists_prop]
  rw [this]
  refine MeasurableSet.biUnion step78Grid_countable fun s _ => ?_
  by_cases h : (s : ℝ) < (4 : ℝ) ^ n
  · have : {y : ℝ≥0 → Fin d → ℤ | (s : ℝ) < (4 : ℝ) ^ n ∧ ∃ v ∈ V, ‖x + y s - v‖ ≤ 1} =
        (fun y : ℝ≥0 → Fin d → ℤ => y s) ⁻¹' {z | ∃ v ∈ V, ‖x + z - v‖ ≤ 1} := by
      ext y; simp [h]
    rw [this]
    exact (measurable_pi_apply s) (Set.to_countable _).measurableSet
  · have : {y : ℝ≥0 → Fin d → ℤ | (s : ℝ) < (4 : ℝ) ^ n ∧ ∃ v ∈ V, ‖x + y s - v‖ ≤ 1} = ∅ := by
      ext y; simp [h]
    rw [this]
    exact MeasurableSet.empty

theorem measurableSet_step78Sfar (n : ℕ) (x : Fin d → ℤ) (V : Set (Fin d → ℤ)) :
    MeasurableSet (step78Sfar n x V) := by
  have : step78Sfar n x V = ⋃ s ∈ step78Grid, {y | (389 / 100 : ℝ) ^ n ≤ s ∧ (s : ℝ) < (4 : ℝ) ^ n ∧
      ∃ v ∈ V, ‖x + y s - v‖ ≤ (19 / 10 : ℝ) ^ n} := by
    ext y
    simp only [step78Sfar, mem_ofPred_eq, mem_iUnion, exists_prop]
  rw [this]
  refine MeasurableSet.biUnion step78Grid_countable fun s _ => ?_
  by_cases h : (389 / 100 : ℝ) ^ n ≤ s ∧ (s : ℝ) < (4 : ℝ) ^ n
  · have : {y : ℝ≥0 → Fin d → ℤ | (389 / 100 : ℝ) ^ n ≤ s ∧ (s : ℝ) < (4 : ℝ) ^ n ∧
        ∃ v ∈ V, ‖x + y s - v‖ ≤ (19 / 10 : ℝ) ^ n} =
        (fun y : ℝ≥0 → Fin d → ℤ => y s) ⁻¹' {z | ∃ v ∈ V, ‖x + z - v‖ ≤ (19 / 10 : ℝ) ^ n} := by
      ext y; simp [h]
    rw [this]
    exact (measurable_pi_apply s) (Set.to_countable _).measurableSet
  · have : {y : ℝ≥0 → Fin d → ℤ | (389 / 100 : ℝ) ^ n ≤ s ∧ (s : ℝ) < (4 : ℝ) ^ n ∧
        ∃ v ∈ V, ‖x + y s - v‖ ≤ (19 / 10 : ℝ) ^ n} = ∅ := by
      ext y
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
      tauto
    rw [this]
    exact MeasurableSet.empty

theorem measurableSet_step78Sbad (β : ℝ) (n : ℕ) (x : Fin d → ℤ) (V : Set (Fin d → ℤ)) :
    MeasurableSet (step78Sbad d β n x V) :=
  ((measurableSet_step78Scl β n).union (measurableSet_step78Sv n x V)).union
    (measurableSet_step78Sfar n x V)

end ElboimSly.Paper.Step

end
