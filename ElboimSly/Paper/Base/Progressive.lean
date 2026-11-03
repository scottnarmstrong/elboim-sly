/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CPathJump
public import Mathlib

/-!
# Right-continuous adapted processes with countable values are progressive

Supports hitting times of adapted step processes: Mathlib's `MeasureTheory.measurable_stoppedValue` then gives the
`ℱ_τ`-measurability of `Y(τ)`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Base

open ElboimSly.Cyclic

/-- Right-continuity gives a plateau to the right which dyadic upper approximations
eventually stay in. -/
theorem exists_plateau {V : Type*} {g : ℝ≥0 → V} (hrc : ∀ s, ∀ᶠ u in 𝓝[≥] s, g u = g s)
    (x : ℝ≥0) : ∃ m0 : ℕ, ∀ m, m0 ≤ m → ∀ u, x ≤ u → u ≤ dyUp m x → g u = g x := by
  obtain ⟨u', hu', hsub⟩ := mem_nhdsGE_iff_exists_Ico_subset.mp (hrc x)
  have hT : Tendsto (fun m : ℕ => ((1 / 2 : ℝ≥0)) ^ m) atTop (𝓝 0) :=
    NNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (by
      rw [one_div]; exact inv_lt_one_of_one_lt₀ (by norm_num))
  have hpos : (0 : ℝ≥0) < u' - x := tsub_pos_of_lt hu'
  obtain ⟨m0, hm0⟩ := (hT.eventually_lt_const hpos).exists_forall_of_atTop
  refine ⟨m0, fun m' hm' u hxu hud => ?_⟩
  have h2 := dyUp_lt m' x
  have h3 : dyUp m' x < u' := by
    refine h2.trans_le ?_
    have := hm0 m' hm'
    calc x + (1 / 2) ^ m' ≤ x + (u' - x) := by gcongr
      _ = u' := add_tsub_cancel_of_le hu'.le
  exact hsub ⟨hxu, lt_of_le_of_lt hud h3⟩

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {V : Type*}

/-- A right-continuous adapted process with values in a countable discrete space is
strongly progressive. -/
theorem isStronglyProgressive_of_rc [TopologicalSpace V] [TopologicalSpace.PseudoMetrizableSpace V]
    [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V] [Countable V]
    [MeasurableSingletonClass V] (f : Filtration ℝ≥0 mΩ) (Y : ℝ≥0 → Ω → V)
    (hY : ∀ t, Measurable[f t] (Y t)) (hrc : ∀ ω t, ∀ᶠ u in 𝓝[≥] t, Y u ω = Y t ω) :
    IsStronglyProgressive f Y := by
  intro i
  let : MeasurableSpace Ω := f i
  refine Measurable.stronglyMeasurable ?_
  have hg : ∀ m : ℕ, Measurable fun p : Set.Iic i × Ω =>
      Y (min i (dyUp m p.1)) p.2 := by
    intro m
    have h1 : Measurable fun p : Set.Iic i × Ω => (⌈(p.1 : ℝ≥0) * 2 ^ m⌉₊, p.2) :=
      (Nat.measurable_ceil.comp ((measurable_subtype_coe.comp measurable_fst).mul_const _)).prodMk
        measurable_snd
    have hmk : ∀ k : ℕ, Measurable fun ω : Ω => Y (min i ((k : ℝ≥0) / 2 ^ m)) ω :=
      fun k => (hY (min i ((k : ℝ≥0) / 2 ^ m))).mono (f.mono (min_le_left _ _)) le_rfl
    have h2 : Measurable fun q : ℕ × Ω => Y (min i ((q.1 : ℝ≥0) / 2 ^ m)) q.2 :=
      measurable_from_prod_countable_right (f := fun q : ℕ × Ω =>
        Y (min i ((q.1 : ℝ≥0) / 2 ^ m)) q.2) hmk
    have h3 := h2.comp h1
    unfold dyUp
    exact h3
  refine measurable_to_countable' fun v => ?_
  have : (fun p : Set.Iic i × Ω => Y p.1 p.2) ⁻¹' {v} =
      ⋃ M : ℕ, ⋂ m : ℕ, ⋂ (_ : M ≤ m), (fun p : Set.Iic i × Ω => Y (min i (dyUp m p.1)) p.2) ⁻¹' {v} := by
    ext p
    simp only [mem_preimage, mem_singleton_iff, mem_iUnion, mem_iInter]
    obtain ⟨m0, hm0⟩ := exists_plateau (hrc p.2) (p.1 : ℝ≥0)
    have key : ∀ m, m0 ≤ m → Y (min i (dyUp m p.1)) p.2 = Y p.1 p.2 := fun m hm =>
      hm0 m hm _ (le_min p.1.2 (le_dyUp m _)) ((min_le_right _ _))
    constructor
    · intro hv
      exact ⟨m0, fun m hm => (key m hm).trans hv⟩
    · rintro ⟨M, hM⟩
      rw [← key (max M m0) (le_max_right _ _)]
      exact hM _ (le_max_left _ _)
  rw [this]
  exact MeasurableSet.iUnion fun M => MeasurableSet.iInter fun m => MeasurableSet.iInter fun _ =>
    hg m (measurableSet_singleton v)

end ElboimSly.Paper.Base
