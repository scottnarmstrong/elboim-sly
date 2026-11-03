/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CPathJump
public import Mathlib

/-!
# Step paths: left values, induction along time, and causal recursion

Infrastructure for the two-particle map and two particles: deterministic properties.  A *step path* is a
right-continuous path `ℝ≥0 → V` with finitely many discontinuities in every bounded interval
(the paths of paths, without a length).

* `IsStepPath.exists_left`: a step path is locally constant to the left of every `r > 0`, and
  `Function.leftLim f r` is that value.
* `real_induction`: induction along time for properties that propagate to the right.
* `exists_unique_stepRec`: the solution of a causal recursion `y r = G r (y (r-))` exists and is
  unique, when `G r` is the identity away from the jumps of a driving step path.
-/

@[expose] public section

open Set Filter Topology Function
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Base

open ElboimSly.Cyclic

variable {V : Type*}

/-- A step path: right-continuous, with finitely many discontinuities in bounded intervals. -/
structure IsStepPath (f : ℝ≥0 → V) : Prop where
  rc : ∀ s, ∀ᶠ u in 𝓝[≥] s, f u = f s
  fin : ∀ T : ℝ≥0, (CDisc f ∩ Iic T).Finite

theorem IsStepPath.exists_left_gap {f : ℝ≥0 → V} (hf : IsStepPath f) {c : ℝ≥0} (hc : 0 < c) :
    ∃ t, t < c ∧ ∀ r ∈ CDisc f, t < r → r < c → False := by
  classical
  have hF : (CDisc f ∩ Iio c).Finite := (hf.fin c).subset (fun r hr => ⟨hr.1, hr.2.le⟩)
  by_cases hne : (CDisc f ∩ Iio c).Nonempty
  · refine ⟨hF.toFinset.max' (by simpa using hne), ?_, fun r hr h1 h2 => ?_⟩
    · have := hF.toFinset.max'_mem (by simpa using hne)
      simp
    · have hrF : r ∈ hF.toFinset := by simpa using ⟨hr, h2⟩
      exact absurd (hF.toFinset.le_max' r hrF) (not_le.mpr h1)
  · exact ⟨0, hc, fun r hr _ h2 => hne ⟨r, hr, h2⟩⟩

theorem IsStepPath.const_between {f : ℝ≥0 → V} (hf : IsStepPath f) {t r u v : ℝ≥0}
    (ht : ∀ s ∈ CDisc f, t < s → s < r → False) (htu : t < u) (huv : u ≤ v) (hvr : v < r) :
    f v = f u :=
  const_of_no_disc hf.rc huv (fun s hs hd => ht s hd (htu.trans_le hs.1.le) (hs.2.trans_lt hvr))
    v ⟨huv, le_rfl⟩

/-- A step path is eventually constant to the left of every `r > 0`. -/
theorem IsStepPath.eventually_left_const {f : ℝ≥0 → V} (hf : IsStepPath f) {r : ℝ≥0}
    (hr : 0 < r) : ∃ c, ∀ᶠ u in 𝓝[<] r, f u = c := by
  obtain ⟨t, htr, ht⟩ := hf.exists_left_gap hr
  obtain ⟨m, hm1, hm2⟩ := exists_between htr
  refine ⟨f m, ?_⟩
  filter_upwards [Ioo_mem_nhdsLT htr] with u hu
  rcases le_total u m with h | h
  · exact (hf.const_between ht hu.1 h hm2).symm
  · exact hf.const_between ht hm1 h hu.2

theorem IsStepPath.leftLim_eq [TopologicalSpace V] [T2Space V] {f : ℝ≥0 → V} {r : ℝ≥0}
    (hr : 0 < r) {c : V} (h : ∀ᶠ u in 𝓝[<] r, f u = c) : leftLim f r = c := by
  have : (𝓝[<] r).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, hr⟩
  exact leftLim_eq_of_tendsto (tendsto_const_nhds.congr' (h.mono fun u hu => hu.symm))

theorem IsStepPath.mem_CDisc_iff [TopologicalSpace V] [T2Space V] {f : ℝ≥0 → V}
    (hf : IsStepPath f) {r : ℝ≥0} (hr : 0 < r) : r ∈ CDisc f ↔ leftLim f r ≠ f r := by
  obtain ⟨c, hc⟩ := hf.eventually_left_const hr
  have hll := IsStepPath.leftLim_eq hr hc
  have : (𝓝[<] r).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, hr⟩
  rw [hll]
  constructor
  · intro hd heq
    exact hd.2 (heq ▸ hc)
  · intro hne
    refine ⟨hr, fun h => hne ?_⟩
    obtain ⟨u, hu1, hu2⟩ := (hc.and h).exists
    rw [← hu1, hu2]

theorem IsStepPath.eventually_left_leftLim [TopologicalSpace V] [T2Space V] {f : ℝ≥0 → V}
    (hf : IsStepPath f) {r : ℝ≥0} (hr : 0 < r) : ∀ᶠ u in 𝓝[<] r, f u = leftLim f r := by
  obtain ⟨c, hc⟩ := hf.eventually_left_const hr
  rwa [IsStepPath.leftLim_eq hr hc]

/-- Induction along time: a property that holds at `0`, holds at `r` when it holds just before
`r`, and propagates to the right, holds always. -/
theorem real_induction {Q : ℝ≥0 → Prop} (h0 : Q 0)
    (hl : ∀ r, 0 < r → (∀ᶠ u in 𝓝[<] r, Q u) → Q r)
    (hr : ∀ r, Q r → ∀ᶠ u in 𝓝[≥] r, Q u) : ∀ s, Q s := by
  by_contra hcon
  push Not at hcon
  set B : Set ℝ≥0 := {s | ¬ Q s} with hB
  have hBne : B.Nonempty := hcon
  set m := sInf B with hm
  have hbelow : ∀ u, u < m → Q u := by
    intro u hu
    by_contra hnu
    exact absurd (csInf_le (OrderBot.bddBelow B) hnu) (not_le.mpr hu)
  have hQm : Q m := by
    rcases eq_or_ne m 0 with h | h
    · rw [h]; exact h0
    · have hpos : 0 < m := pos_iff_ne_zero.mpr h
      refine hl m hpos ?_
      filter_upwards [self_mem_nhdsWithin] with u hu using hbelow u hu
  obtain ⟨ε, hε, hsub⟩ := mem_nhdsGE_iff_exists_Ico_subset.mp (hr m hQm)
  obtain ⟨u, huB, hu⟩ := exists_lt_of_csInf_lt hBne (show sInf B < ε by
    rw [← hm]; exact hε)
  have hmu : m ≤ u := csInf_le (OrderBot.bddBelow B) huB
  exact huB (hsub ⟨hmu, hu⟩)

end ElboimSly.Paper.Base
