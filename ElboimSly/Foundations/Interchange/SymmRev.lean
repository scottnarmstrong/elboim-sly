/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Interchange.SymmCov
import Mathlib

/-!
# Covariance of trajectories under time reflection

Covariance of trajectories(c).

The time reversal of the forward trajectory of `ν` from `(x, a)` is the backward trajectory of
`ϱ_*ν` to `(x, -a)`, in the encoding where the reversed path at time `-a - s` is the left limit
`γ(s-)`.

**Deviation from the written proof.** The written proof states (c) without a side condition. At the
start time `a` the forward path ignores a ring at `x` (the swap rule is only imposed at times
`> a`), whereas the backward path to `(x, -a)` for `ϱ_*ν` obeys the swap rule at `-a` itself. So the
statement as written fails if some edge at `x` rings at time `a`; we assume that no such edge
rings. (For all other times the swap rules match exactly.)
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped NNReal

namespace ElboimSly.Interchange

variable {d : ℕ} {β : ℝ} [Fact (0 < β)] {ν : Measure (RingSpace d β)}

open scoped Classical in
/-- The left-limit path `s ↦ γ_{x,a}(a + s -)` (and `x` at `s = 0`). -/
noncomputable def fwdLeft (hν : Good ν) (x : Fin d → ℤ) (a : ℝ) (s : ℝ≥0) : Fin d → ℤ :=
  if h : 0 < s then Classical.choose ((fwdTrajFn_spec hν x a).1.2.1 s h) else x

theorem fwdLeft_isLeftLimit (hν : Good ν) (x : Fin d → ℤ) (a : ℝ) {s : ℝ≥0} (hs : 0 < s) :
    IsLeftLimit (fwdTrajFn hν x a) s (fwdLeft hν x a s) := by
  simp only [fwdLeft, hs, ↓reduceDIte]
  exact Classical.choose_spec ((fwdTrajFn_spec hν x a).1.2.1 s hs)

theorem fwdLeft_zero (hν : Good ν) (x : Fin d → ℤ) (a : ℝ) : fwdLeft hν x a 0 = x := by
  simp [fwdLeft]

theorem eventually_fwdLeft_lt (hν : Good ν) (x : Fin d → ℤ) (a : ℝ) {s : ℝ≥0} (hs : 0 < s) :
    ∃ u0 < s, ∀ u, u0 < u → u < s → fwdLeft hν x a u = fwdLeft hν x a s := by
  obtain ⟨u0, hu0mem, hsub⟩ := (mem_nhdsLT_iff_exists_Ioo_subset' hs).mp
    (fwdLeft_isLeftLimit hν x a hs)
  have hu0 : u0 < s := hu0mem
  refine ⟨u0, hu0, fun u h1 h2 => ?_⟩
  have hu : 0 < u := lt_of_le_of_lt (zero_le : (0 : ℝ≥0) ≤ u0) h1
  refine IsLeftLimit.unique hu (fwdLeft_isLeftLimit hν x a hu) ?_
  filter_upwards [Ioo_mem_nhdsLT h1] with w hw using hsub ⟨hw.1, hw.2.trans h2⟩

theorem eventually_fwdLeft_gt (hν : Good ν) (x : Fin d → ℤ) (a : ℝ) (s : ℝ≥0) :
    ∃ u1 > s, ∀ u, s < u → u < u1 → fwdLeft hν x a u = fwdTrajFn hν x a s := by
  obtain ⟨u1, hu1, hsub⟩ := mem_nhdsGE_iff_exists_Ico_subset.mp ((fwdTrajFn_spec hν x a).1.1 s)
  refine ⟨u1, hu1, fun u h1 h2 => ?_⟩
  have hu : 0 < u := lt_of_le_of_lt (zero_le : (0 : ℝ≥0) ≤ s) h1
  refine IsLeftLimit.unique hu (fwdLeft_isLeftLimit hν x a hu) ?_
  filter_upwards [Ico_mem_nhdsLT h1] with w hw using hsub ⟨hw.1, hw.2.trans h2⟩

/-- Time reversal of the forward trajectory from `(x, a)` is the backward trajectory of the
reflected configuration to `(x, -a)`, provided no edge at `x` rings at time `a`.
Covariance of trajectories(c) (with the side condition explained in the module docstring). -/
theorem bwdTrajFn_reflectMeasure (hν : Good ν) (x : Fin d → ℤ) (a : ℝ)
    (hring : ¬ ∃ e : Edge d, e.Mem x ∧ Rings ν e a) :
    bwdTrajFn (good_reflectMeasure hν) x (-a) = fwdLeft hν x a := by
  symm
  have hγ := (fwdTrajFn_spec hν x a).1
  refine bwdTrajFn_eq (good_reflectMeasure hν) ⟨⟨?_, ?_, ?_, ?_⟩, fwdLeft_zero hν x a⟩
  · intro s
    rcases eq_zero_or_pos s with rfl | hs
    · filter_upwards [self_mem_nhdsWithin (a := (0 : ℝ≥0)) (s := Set.Iic 0)] with u hu
      have hu' : u ≤ 0 := hu
      rw [nonpos_iff_eq_zero.mp hu']
    · obtain ⟨u0, hu0, h⟩ := eventually_fwdLeft_lt hν x a hs
      filter_upwards [Ioc_mem_nhdsLE hu0] with u hu
      rcases eq_or_lt_of_le hu.2 with rfl | hlt
      · rfl
      · exact h u hu.1 hlt
  · intro s
    obtain ⟨u1, hu1, h⟩ := eventually_fwdLeft_gt hν x a s
    exact ⟨_, by filter_upwards [Ioo_mem_nhdsGT hu1] with u hu using h u hu.1 hu.2⟩
  · intro T
    refine (hγ.2.2.1 T).subset ?_
    rintro s ⟨hsT, z, hz, hne⟩
    obtain ⟨u1, hu1, h⟩ := eventually_fwdLeft_gt hν x a s
    have hzγ : z = fwdTrajFn hν x a s := by
      have hz' : IsRightLimit (fwdLeft hν x a) s (fwdTrajFn hν x a s) := by
        filter_upwards [Ioo_mem_nhdsGT hu1] with u hu using h u hu.1 hu.2
      exact IsRightLimit.unique hz hz'
    rcases eq_zero_or_pos s with rfl | hs
    · exact absurd (by rw [hzγ, fwdLeft_zero]; exact (fwdTrajFn_spec hν x a).2.symm ▸ rfl) hne
    · refine ⟨hs, hsT, fwdLeft hν x a s, fwdLeft_isLeftLimit hν x a hs, fun h' => hne ?_⟩
      rw [hzγ]; exact h'.symm
  · intro s z hz
    obtain ⟨u1, hu1, h⟩ := eventually_fwdLeft_gt hν x a s
    have hz' : IsRightLimit (fwdLeft hν x a) s (fwdTrajFn hν x a s) := by
      filter_upwards [Ioo_mem_nhdsGT hu1] with u hu using h u hu.1 hu.2
    rw [IsRightLimit.unique hz hz', swapRule_reflectMeasure_iff]
    rcases eq_zero_or_pos s with rfl | hs
    · rw [fwdLeft_zero, (fwdTrajFn_spec hν x a).2]
      simp only [NNReal.coe_zero, sub_zero, neg_neg]
      refine swapRule_self ?_
      rintro ⟨e, he, hr⟩
      exact hring ⟨e, he, hr⟩
    · refine SwapRule.symm hν ?_
      have := hγ.2.2.2 s hs _ (fwdLeft_isLeftLimit hν x a hs)
      rw [show -(-a - (s : ℝ)) = a + s by ring]
      exact this

end ElboimSly.Interchange
