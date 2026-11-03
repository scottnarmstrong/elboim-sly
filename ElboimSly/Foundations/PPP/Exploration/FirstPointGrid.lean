/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.PPP.Exploration.ProbeCont
public import ElboimSly.Foundations.PPP.Exploration.ProbeMeasDet
public import ElboimSly.Foundations.PPP.Exploration.FirstPointDet
public import ElboimSly.Foundations.PPP.Exploration.PoissonEvents
import Mathlib

/-!
# The grid argument for the first-point law: events and probabilities

First-point law of a deterministic probe, proof of (c).

For a probe `(R, h)`, a grid size `L` and `1 ≤ i ≤ L` we write `s_i = i h / L`, `Δ_i = D(s_i) \ D(s_{i-1})`,
and consider the events on `Measure S`:

* `firstEvent B`: `D(h)` is hit, `V(S) = 1` and `V(B) = 1`;
* `cellEvent B L i`: `D(s_{i-1})` is empty, `Δ_i ∩ B` has one point and `Δ_i \ B` none;
* `cellIndex L i`: `s_{i-1} < ρ ≤ s_i`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal NNReal

namespace ElboimSly

variable {S : Type*} [MeasurableSpace S]

/-- The grid cell `Δ_i = D(s_i) \ D(s_{i-1})`. -/
def gridCell (R : S → ℝ≥0∞) (h : ℝ≥0) (L i : ℕ) : Set S :=
  probeRegion R (gridTime h L i) \ probeRegion R (gridTime h L (i - 1))

/-- `D(s_{i-1})` empty, one point in `Δ_i ∩ B`, none in `Δ_i \ B`. -/
def cellEvent (R : S → ℝ≥0∞) (h : ℝ≥0) (B : Set S) (L i : ℕ) : Set (Measure S) :=
  {ν | ν (probeRegion R (gridTime h L (i - 1))) = 0 ∧ ν (gridCell R h L i ∩ B) = 1 ∧
    ν (gridCell R h L i \ B) = 0}

/-- The first point is in `B`, and `D(ρ)` carries exactly one point. -/
def firstEvent (μ : Measure S) [SigmaFinite μ] (R : S → ℝ≥0∞) (h : ℝ≥0) (B : Set S) :
    Set (Measure S) :=
  {ν | 1 ≤ tau μ ν (probeRegion R h) ∧ probeV μ R h ν Set.univ = 1 ∧ probeV μ R h ν B = 1}

/-- `s_{i-1} < ρ ≤ s_i`. -/
def cellIndex (μ : Measure S) [SigmaFinite μ] (R : S → ℝ≥0∞) (h : ℝ≥0) (L i : ℕ) :
    Set (Measure S) :=
  {ν | (gridTime h L (i - 1) : ℝ≥0∞) < probeRho μ R h ν ∧ probeRho μ R h ν ≤ gridTime h L i}

theorem gridTime_zero (h : ℝ≥0) (L : ℕ) : gridTime h L 0 = 0 := by simp [gridTime]

theorem gridTime_self (h : ℝ≥0) {L : ℕ} (hL : 0 < L) : gridTime h L L = h := by
  unfold gridTime
  have : (L : ℝ≥0) ≠ 0 := by exact_mod_cast hL.ne'
  exact mul_div_cancel_right₀ h this

/-- Every time in `[0, h]` is `0` or lies in a grid cell. -/
theorem exists_grid_index {h : ℝ≥0} {L : ℕ} (hL : 0 < L) {r : ℝ≥0∞} (hr : r ≤ h) :
    r ≤ 0 ∨ ∃ i, 1 ≤ i ∧ i ≤ L ∧ (gridTime h L (i - 1) : ℝ≥0∞) < r ∧
      r ≤ gridTime h L i := by
  classical
  have hex : ∃ i, r ≤ (gridTime h L i : ℝ≥0∞) :=
    ⟨L, by rw [gridTime_self h hL]; exact hr⟩
  let i := Nat.find hex
  have hi : r ≤ (gridTime h L i : ℝ≥0∞) := Nat.find_spec hex
  by_cases h0 : i = 0
  · left
    have : r ≤ (gridTime h L 0 : ℝ≥0∞) := h0 ▸ hi
    rwa [gridTime_zero] at this
  · right
    refine ⟨i, Nat.one_le_iff_ne_zero.2 h0, Nat.find_min' hex (by rw [gridTime_self h hL]; exact hr),
      ?_, hi⟩
    have := Nat.find_min hex (show i - 1 < i by omega)
    exact not_le.1 this

section Events

variable {μ : Measure S} [SigmaFinite μ] {R : S → ℝ≥0∞} {h : ℝ≥0}

theorem measurableSet_firstEvent (hR : Measurable R) {B : Set S} (hB : MeasurableSet B) :
    MeasurableSet (firstEvent μ R h B) := by
  have hV := measurable_probeV μ (h := h) hR
  have h1 : Measurable fun ν : Measure S => tau μ ν (probeRegion R h) :=
    (Measure.measurable_coe (measurableSet_probeRegion hR _)).comp (measurable_tau μ)
  refine (measurableSet_le measurable_const h1).inter
    ((measurableSet_eq_fun ((Measure.measurable_coe MeasurableSet.univ).comp hV)
      measurable_const).inter
      (measurableSet_eq_fun ((Measure.measurable_coe hB).comp hV) measurable_const))

theorem measurableSet_cellIndex (hR : Measurable R) (L i : ℕ) :
    MeasurableSet (cellIndex μ R h L i) :=
  (measurableSet_lt measurable_const (measurable_probeRho μ hR)).inter
    (measurableSet_le (measurable_probeRho μ hR) measurable_const)

theorem pairwiseDisjoint_cellIndex (L : ℕ) :
    Pairwise (Function.onFun Disjoint (cellIndex μ R h L)) := by
  intro i j hij
  rw [Function.onFun, Set.disjoint_left]
  rintro ν ⟨hi1, hi2⟩ ⟨hj1, hj2⟩
  rcases lt_or_gt_of_ne hij with hlt | hlt
  · have : gridTime h L i ≤ gridTime h L (j - 1) := gridTime_mono (by omega)
    have h3 : (gridTime h L i : ℝ≥0∞) ≤ gridTime h L (j - 1) := by exact_mod_cast this
    exact absurd (hj1.trans_le' (hi2.trans h3) |> fun x => x) (lt_irrefl _)
  · have : gridTime h L j ≤ gridTime h L (i - 1) := gridTime_mono (by omega)
    have h3 : (gridTime h L j : ℝ≥0∞) ≤ gridTime h L (i - 1) := by exact_mod_cast this
    exact absurd (hi1.trans_le' (hj2.trans h3) |> fun x => x) (lt_irrefl _)

end Events

end ElboimSly
