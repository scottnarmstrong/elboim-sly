/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycDrivenRegionRule
public import Mathlib

/-!
# Cutting a driving path at a regeneration time

The constructions of the regenerated walk (iii): "If `X ∈ cycCF` then `X^{(k)} ∈ cycCF`: differences of jump
times are inherited, and a jump of `X^{(k)}` at `βℤ_{≥1}` is a jump of `X` at
`σ_{k-1} + βℤ_{≥1} ⊆ βℤ_{≥1}`."

`shiftPath f a (s) = f(a + s) - f(a)` is the driving path `X(a + ·) - X(a)`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

variable {d : ℕ}

/-- The path `f(a + ·) - f(a)`. -/
def shiftPath (f : ℝ≥0 → Fin d → ℤ) (a : ℝ≥0) : ℝ≥0 → Fin d → ℤ := fun s => f (a + s) - f a

theorem tendsto_add_nhdsLT (a r : ℝ≥0) :
    Tendsto (fun u : ℝ≥0 => a + u) (𝓝[<] r) (𝓝[<] (a + r)) :=
  tendsto_nhdsWithin_iff.2 ⟨(continuous_const.add continuous_id).continuousAt.tendsto.mono_left
    nhdsWithin_le_nhds, eventually_nhdsWithin_of_forall fun _ hu => add_lt_add_right hu a⟩

theorem tendsto_add_nhdsGE (a r : ℝ≥0) :
    Tendsto (fun u : ℝ≥0 => a + u) (𝓝[≥] r) (𝓝[≥] (a + r)) :=
  tendsto_nhdsWithin_iff.2 ⟨(continuous_const.add continuous_id).continuousAt.tendsto.mono_left
    nhdsWithin_le_nhds, eventually_nhdsWithin_of_forall fun _ hu => add_le_add le_rfl hu⟩

theorem leftVal_shiftPath {f : ℝ≥0 → Fin d → ℤ} (hf : IsRegPath f) (a : ℝ≥0) {r : ℝ≥0}
    (hr : 0 < r) : leftVal (shiftPath f a) r = leftVal f (a + r) - f a := by
  have hr' : 0 < a + r := lt_of_lt_of_le hr le_add_self
  refine leftVal_eq_of_eventually hr ?_
  have h := (tendsto_add_nhdsLT a r).eventually (hf.eventually_leftVal hr')
  filter_upwards [h] with u hu
  simp only [shiftPath]
  rw [hu]

theorem isRegPath_shiftPath {f : ℝ≥0 → Fin d → ℤ} (hf : IsRegPath f) (a : ℝ≥0) :
    IsRegPath (shiftPath f a) where
  rc s := by
    have h := (tendsto_add_nhdsGE a s).eventually (hf.rc (a + s))
    filter_upwards [h] with u hu
    simp only [shiftPath]; rw [hu]
  fin T := by
    refine ((hf.fin (a + T)).preimage (f := fun s : ℝ≥0 => a + s)
      (add_right_injective a).injOn).subset ?_
    rintro s ⟨⟨hs0, hs⟩, hsT⟩
    refine ⟨⟨lt_of_lt_of_le hs0 le_add_self, fun h => hs ?_⟩, add_le_add le_rfl hsT⟩
    have := (tendsto_add_nhdsLT a s).eventually h
    exact this.mono fun u hu => by simp only [shiftPath]; rw [hu]

theorem mem_CDisc_of_shiftPath {f : ℝ≥0 → Fin d → ℤ} (a : ℝ≥0) {s : ℝ≥0}
    (hs : s ∈ CDisc (shiftPath f a)) : a + s ∈ CDisc f := by
  obtain ⟨hs0, hs⟩ := hs
  refine ⟨lt_of_lt_of_le hs0 le_add_self, fun h => hs ?_⟩
  have := (tendsto_add_nhdsLT a s).eventually h
  exact this.mono fun u hu => by simp only [shiftPath]; rw [hu]

theorem isDrivingPath_shiftPath {f : ℝ≥0 → Fin d → ℤ} (hf : IsDrivingPath f) (a : ℝ≥0) :
    IsDrivingPath (shiftPath f a) where
  toIsRegPath := isRegPath_shiftPath hf.toIsRegPath a
  zero := by simp [shiftPath]
  unit s hs := by
    have hs' := mem_CDisc_of_shiftPath a hs
    have := hf.unit _ hs'
    rw [leftVal_shiftPath hf.toIsRegPath a hs.1]
    simp only [shiftPath]
    rw [sub_sub_sub_cancel_right]
    exact this

theorem cycCF_shiftPath {f : ℝ≥0 → Fin d → ℤ} {b : ℝ≥0} (hf : f ∈ CycCF b) (m : ℕ) :
    shiftPath f ((m : ℝ≥0) * b) ∈ CycCF b := by
  obtain ⟨hdr, hi, hno⟩ := hf
  refine ⟨isDrivingPath_shiftPath hdr _, fun s hs s' hs' k hk h => ?_, fun k hk hmem => ?_⟩
  · refine hi _ (mem_CDisc_of_shiftPath _ hs) _ (mem_CDisc_of_shiftPath _ hs') k hk ?_
    rw [h]; ring
  · refine hno (m + k) (by omega) ?_
    have := mem_CDisc_of_shiftPath _ hmem
    convert this using 1
    push_cast; ring

theorem isShiftOf_shiftPath (X : CPath (Fin d → ℤ)) (a : ℝ≥0) :
    IsShiftOf X a (shiftPath X.fn a) := by
  have hreg : IsRegPath X.fn := ⟨X.rc, X.fin⟩
  refine ⟨X.fn a, fun r hr => ⟨?_, ?_⟩⟩
  · rw [CPath.left_eq_leftVal X (lt_of_lt_of_le hr le_add_self), leftVal_shiftPath hreg a hr]
    abel
  · simp [shiftPath]

end ElboimSly.Cyclic

end
