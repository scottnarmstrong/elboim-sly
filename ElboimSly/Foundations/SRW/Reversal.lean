/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.SRW.Iid
public import ElboimSly.Foundations.SRW.Coincidence
public import Mathlib

/-!
# Time reversal: paths

Time reversal (regularity and range statements).

`revPath T γ` is `û ↦ γ(T) - γ((T-u)-)` for `u < T` and `γ(T)` for `u ≥ T`, with the left limit
taken in `ℤ^d` (`Function.leftLim`).  For the walk built from any measure `ν` (good or not),
`revPath T (can ν)` is regular, and under `γ(T-) = γ(T)` the range of `γ` on `[0,T]` equals that of
`γ(T) - revPath T γ`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

namespace ElboimSly
namespace SRW

variable {d : ℕ}

/-- The walk of a measure as a path (indexed by `ℝ≥0`). -/
noncomputable def can (d : ℕ) (ν : Measure (Dir d × ℝ)) : PathSpace d := fun s => walk d ν (s : ℝ)

/-- Time reversal of a path at time `T`. -/
noncomputable def revPath (T : ℝ≥0) (γ : PathSpace d) : PathSpace d :=
  fun u => if u < T then γ T - Function.leftLim γ (T - u) else γ T

theorem leftLim_eq_of_const {γ : PathSpace d} {a r : ℝ≥0} {c : Fin d → ℤ} (h : a < r)
    (hc : ∀ s, a ≤ s → s < r → γ s = c) : Function.leftLim γ r = c := by
  have : (𝓝[<] r).NeBot := nhdsLT_neBot_of_exists_lt ⟨a, h⟩
  refine leftLim_eq_of_tendsto ?_
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [Ioo_mem_nhdsLT h] with s hs using (hc s hs.1.le hs.2).symm

theorem exists_const_left_nn (ν : Measure (Dir d × ℝ)) {t : ℝ≥0} (ht : 0 < t) :
    ∃ a : ℝ≥0, a < t ∧ (∀ s, a ≤ s → s < t → can d ν s = can d ν a) ∧
      (ν ∈ goodSet d → tot ν (Ioo (a : ℝ) t) = 0) := by
  have htr : (0 : ℝ) < t := by exact_mod_cast ht
  obtain ⟨δ, hδ, hδt, hc, hn⟩ := exists_const_left (ν := ν) (t : ℝ) htr
  have ha : (((t : ℝ) - δ).toNNReal : ℝ) = (t : ℝ) - δ := Real.coe_toNNReal _ (by linarith)
  refine ⟨((t : ℝ) - δ).toNNReal, ?_, ?_, ?_⟩
  · rw [← NNReal.coe_lt_coe, ha]; linarith
  · intro s hs1 hs2
    have h1 : ((t : ℝ) - δ) ≤ s := by rw [← ha]; exact_mod_cast hs1
    have h2 : (s : ℝ) < t := by exact_mod_cast hs2
    have := hc s ⟨h1, h2⟩
    simp only [can]
    rw [this, ha]
  · intro hν
    rw [ha]; exact hn hν

/-- Time reversal of the walk has regular paths, for every measure. -/
theorem isRegularPath_revPath_can (ν : Measure (Dir d × ℝ)) (T : ℝ≥0) :
    IsRegularPath (revPath T (can d ν)) := by
  intro u0
  by_cases hu0 : T ≤ u0
  · refine ⟨1, one_pos, fun s hs1 _ => ?_⟩
    simp [revPath, not_lt.2 hu0, not_lt.2 (hu0.trans hs1)]
  · rw [not_le] at hu0
    have ht0 : 0 < T - u0 := tsub_pos_of_lt hu0
    obtain ⟨a, hat, hconst, -⟩ := exists_const_left_nn ν ht0
    refine ⟨T - u0 - a, tsub_pos_of_lt hat, fun s hs1 hs2 => ?_⟩
    have h1 : (s : ℝ) < u0 + ((T : ℝ) - u0 - a) := by
      have := NNReal.coe_lt_coe.2 hs2
      rwa [NNReal.coe_add, NNReal.coe_sub hat.le, NNReal.coe_sub hu0.le] at this
    have ha0 : (0 : ℝ) ≤ a := NNReal.coe_nonneg a
    have hsT : s < T := by
      rw [← NNReal.coe_lt_coe]; linarith
    have hr1 : a < T - s := by
      rw [← NNReal.coe_lt_coe, NNReal.coe_sub hsT.le]; linarith
    have hr2 : T - s ≤ T - u0 := tsub_le_tsub_left hs1 T
    have e1 : Function.leftLim (can d ν) (T - s) = can d ν a :=
      leftLim_eq_of_const hr1 fun x hx1 hx2 => hconst x hx1 (hx2.trans_le hr2)
    have e2 : Function.leftLim (can d ν) (T - u0) = can d ν a :=
      leftLim_eq_of_const hat fun x hx1 hx2 => hconst x hx1 hx2
    simp only [revPath, ite_eq_left hsT, ite_eq_left hu0, e1, e2]

/-- Time reversal (b), deterministic form: if `γ(T-) = γ(T)`, the range of the
walk on `[0,T]` equals the range of `γ(T) - γ̂`. -/
theorem range_revPath_can (ν : Measure (Dir d × ℝ)) {T : ℝ≥0}
    (hc : Function.leftLim (can d ν) T = can d ν T) :
    can d ν '' Icc 0 T = (fun u => can d ν T - revPath T (can d ν) u) '' Icc 0 T := by
  ext y
  constructor
  · rintro ⟨s, ⟨-, hsT⟩, rfl⟩
    rcases hsT.eq_or_lt with rfl | hlt
    · refine ⟨0, ⟨le_rfl, bot_le⟩, ?_⟩
      have hT0 : (0 : ℝ≥0) < s ∨ s = 0 := (bot_le).lt_or_eq.imp id Eq.symm
      rcases hT0 with hT0 | rfl
      · simp only [revPath, ite_eq_left hT0, tsub_zero, hc, sub_sub_cancel]
      · simp only [revPath, lt_irrefl, ite_false, sub_self]
        simp [can, walk_zero]
    · obtain ⟨δ, hδ, hconst⟩ := exists_const_right (ν := ν) (s : ℝ) s.2
      set r : ℝ≥0 := min (s + δ.toNNReal) T with hr
      have hsr : s < r := lt_min (lt_add_of_pos_right s (Real.toNNReal_pos.2 hδ)) hlt
      have hrT : r ≤ T := min_le_right _ _
      have hr0 : 0 < r := lt_of_le_of_lt (bot_le) hsr
      have hu : T - r < T := tsub_lt_self (hr0.trans_le hrT) hr0
      have hTu : T - (T - r) = r := tsub_tsub_cancel_of_le hrT
      have e : Function.leftLim (can d ν) r = can d ν s := by
        refine leftLim_eq_of_const hsr fun x hx1 hx2 => ?_
        have h2 : x < s + δ.toNNReal := hx2.trans_le (min_le_left _ _)
        have h2' : (x : ℝ) < s + δ := by
          have := NNReal.coe_lt_coe.2 h2
          rwa [NNReal.coe_add, Real.coe_toNNReal _ hδ.le] at this
        exact hconst x ⟨by exact_mod_cast hx1, h2'⟩
      refine ⟨T - r, ⟨bot_le, hu.le⟩, ?_⟩
      simp only [revPath, ite_eq_left hu, hTu, e, sub_sub_cancel]
  · rintro ⟨u, ⟨-, huT⟩, rfl⟩
    by_cases hu : u < T
    · have hpos : 0 < T - u := tsub_pos_of_lt hu
      obtain ⟨a, hat, hconst, -⟩ := exists_const_left_nn ν hpos
      refine ⟨a, ⟨bot_le, (hat.trans_le tsub_le_self).le⟩, ?_⟩
      simp only [revPath, ite_eq_left hu, sub_sub_cancel]
      exact (leftLim_eq_of_const hat fun x hx1 hx2 => hconst x hx1 hx2).symm
    · refine ⟨0, ⟨le_rfl, bot_le⟩, ?_⟩
      simp [revPath, hu, can, walk_zero]

end SRW
end ElboimSly
