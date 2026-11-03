/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycDrivenExists
public import ElboimSly.Foundations.Cyclic.CycDrivenEvents
public import ElboimSly.Foundations.Cyclic.DrivenMain
public import Mathlib

/-!
# The driven walk as a path, and the class condition

The driven walk is a driven world-line, setup. The driven walk `w^x` as a `CPath` of length `∞`, the
walk data `δ = (1, 0, 0, +1)` of `𝒫₁`, and the translation of the class condition
"`r - r' ∈ βℤ_{≥1}`" into equality of clocks and into delay indices.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

variable {I : Type*} [MeasurableSpace I] {ι : I} {d : ℕ} {β : ℝ} [Fact (0 < β)]

/-- The walk data `(ι, 0, 0, +1)`. -/
def regionData {I : Type*} (d : ℕ) (ι : I) : CycData I d := (ι, 0, 0, true)

omit [MeasurableSpace I] [Fact (0 < β)] in
theorem clock_regionData (r : ℝ≥0) :
    (regionData d ι).clock β r = (((r : ℝ)) : AddCircle β) := by
  simp [CycData.clock, regionData, CycData.phase, CycData.sgn, CycData.fwd]

omit [MeasurableSpace I] [Fact (0 < β)] in
theorem clock_eq_of_shift {r' r : ℝ≥0} {k : ℕ} (h : (r : ℝ) = r' + k * β) :
    (regionData d ι).clock β r' = (regionData d ι).clock β r := by
  rw [clock_regionData, clock_regionData]
  have : ((r : ℝ) : AddCircle β) = ((r' : ℝ) : AddCircle β) + ((k * β : ℝ) : AddCircle β) := by
    rw [h, AddCircle.coe_add]
  rw [this]
  have h0 : ((k * β : ℝ) : AddCircle β) = 0 := by
    rw [AddCircle.coe_eq_zero_iff]
    exact ⟨k, by simp⟩
  rw [h0, add_zero]

theorem shift_nnreal {r' r : ℝ≥0} {k : ℕ} :
    (r : ℝ) = r' + k * β ↔ r = r' + k * β.toNNReal := by
  have hβ : 0 < β := Fact.out
  constructor
  · intro h
    apply NNReal.coe_injective
    push_cast
    rw [Real.coe_toNNReal β hβ.le]
    exact h
  · intro h
    have := congrArg (fun z : ℝ≥0 => (z : ℝ)) h
    simp only [NNReal.coe_add, NNReal.coe_mul, NNReal.coe_natCast] at this
    rw [Real.coe_toNNReal β hβ.le] at this
    exact this

/-- The driven walk as a path of length `∞`. -/
noncomputable def drivenCPath {x : ℝ≥0 → Fin d → ℤ} (hx : IsDrivingPath x) (hβ : 0 < β.toNNReal) :
    CPath (Fin d → ℤ) :=
  ⟨⊤, drivenWalk β.toNNReal x, (drivenWalk_wd_a hx hβ).2.1, (drivenWalk_wd_a hx hβ).2.2.2.1,
    fun _ _ h _ => absurd h (by simp)⟩

omit [Fact (0 < β)] in
theorem drivenCPath_left {x : ℝ≥0 → Fin d → ℤ} (hx : IsDrivingPath x) (hβ : 0 < β.toNNReal)
    {r : ℝ≥0} (hr : 0 < r) :
    (drivenCPath hx hβ).left r = leftVal (drivenWalk β.toNNReal x) r := by
  symm
  exact leftVal_eq_of_eventually hr ((drivenCPath hx hβ).eventually_left hr)

end ElboimSly.Cyclic

end
