/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.PPP.Exploration.ThmA
import Mathlib

/-!
# Sequential first-point exploration: pointwise identities for one step

Sequential first-point exploration, Step 2.

For a history `η` and `o = St_{k,η}(ν)` we have `Z_{k+1}(η, o) = Z_k(η) ∪ D_k(η, ρ)`, and the
unexplored part of `ν` after the step is a function of the unexplored part before, and also of the
renewed configuration.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal NNReal

namespace ElboimSly

variable {S : Type*} [MeasurableSpace S] {U : Type*} [MeasurableSpace U] {μ : Measure S}
  [SigmaFinite μ] (sch : ExplScheme μ U)

namespace ExplScheme

/-- The unexplored part `τ(ν)|_{S ∖ Z_k(η)}`. -/
noncomputable def unexpl (k : ℕ) (η : Hist U S k) (ν : Measure S) : Measure S :=
  (tau μ ν).restrict (sch.Z k η)ᶜ

theorem measurable_unexpl (k : ℕ) :
    Measurable fun p : Hist U S k × Measure S => sch.unexpl k p.1 p.2 :=
  sch.measurable_restrict_Zc k

omit [SigmaFinite μ] in
theorem measurableSet_Zη (k : ℕ) (η : Hist U S k) : MeasurableSet (sch.Z k η) :=
  measurable_prodMk_left (sch.measurableSet_Z k)

theorem Z_snoc_stepAt (k : ℕ) (η : Hist U S k) (ν : Measure S) :
    sch.Z (k + 1) (η.snoc (sch.stepAt k η ν)) =
      sch.Z k η ∪ probeRegion (sch.Rt k η) (sch.stepAt k η ν).1 := by
  have hρ : min (sch.stepAt k η ν).1 (sch.h k η) = (sch.stepAt k η ν).1 :=
    min_eq_left (sch.stepAt_fst_le _ _ _)
  simp only [Z, Hist.init_snoc, Hist.last_snoc, hρ]
  ext y
  simp only [Set.mem_union, Set.mem_ofPred_eq, probeRegion]
  constructor
  · rintro (h | ⟨h1, h2⟩)
    · exact Or.inl h
    · exact Or.inr (by rw [sch.Rt_of_notMem h1]; exact h2)
  · rintro (h | h)
    · exact Or.inl h
    · by_cases hy : y ∈ sch.Z k η
      · exact Or.inl hy
      · exact Or.inr ⟨hy, by rwa [sch.Rt_of_notMem hy] at h⟩

omit [SigmaFinite μ] in
theorem Z_subset_snoc (k : ℕ) (η : Hist U S k) (o : Outcome S) :
    sch.Z k η ⊆ sch.Z (k + 1) (η.snoc o) := by
  simp only [Z, Hist.init_snoc]
  exact Set.subset_union_left

theorem stepAt_unexpl (k : ℕ) (η : Hist U S k) (ν : Measure S) :
    sch.stepAt k η (sch.unexpl k η ν) = sch.stepAt k η ν := by
  symm
  unfold stepAt
  refine probeStep_congr ((sch.isProbe_Rt k η).measurable) ?_
  have hlf : sch.unexpl k η ν ∈ lfSet μ := restrict_mem_lfSet (tau_mem_lfSet μ ν) _
  rw [tau_of_mem μ hlf]
  unfold unexpl
  rw [Measure.restrict_restrict (measurableSet_probeRegion (sch.isProbe_Rt k η).measurable _),
    Set.inter_eq_left.2]
  exact fun x hx hxZ => (sch.disjoint_region_Z k η).le_bot ⟨hx, hxZ⟩ |>.elim

theorem unexpl_snoc_unexpl (k : ℕ) (η : Hist U S k) (ν : Measure S) (o : Outcome S) :
    sch.unexpl (k + 1) (η.snoc o) ν = (sch.unexpl k η ν).restrict (sch.Z (k + 1) (η.snoc o))ᶜ := by
  unfold unexpl
  have hsub : (sch.Z (k + 1) (η.snoc o))ᶜ ⊆ (sch.Z k η)ᶜ :=
    Set.compl_subset_compl.2 (sch.Z_subset_snoc k η o)
  rw [Measure.restrict_restrict (sch.measurableSet_Zη (k + 1) (η.snoc o)).compl,
    Set.inter_eq_left.2 hsub]

end ExplScheme

end ElboimSly
