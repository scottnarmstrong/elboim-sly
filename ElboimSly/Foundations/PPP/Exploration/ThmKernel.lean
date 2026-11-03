/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.PPP.Exploration.ThmStep
import Mathlib

/-!
# Sequential first-point exploration: one step at a fixed history

Sequential first-point exploration, Step 2 (the integral over `W` at a fixed history `η`), using the
one-step lemma the unexplored part after one step for the masked probe.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal NNReal

namespace ElboimSly

variable {S : Type*} [MeasurableSpace S] {U : Type*} [MeasurableSpace U] {μ : Measure S}
  [SigmaFinite μ] (sch : ExplScheme μ U) {W : Measure (Measure S)}

theorem lfSet_add {ν₁ ν₂ : Measure S} (h₁ : ν₁ ∈ lfSet μ) (h₂ : ν₂ ∈ lfSet μ) :
    ν₁ + ν₂ ∈ lfSet μ := fun k => by
  rw [Measure.add_apply]
  exact ENNReal.add_lt_top.2 ⟨h₁ k, h₂ k⟩

theorem probeRenew_mem_lfSet {R : S → ℝ≥0∞} {h : ℝ≥0} (ν ν₂ : Measure S) :
    probeRenew μ R h ν ν₂ ∈ lfSet μ :=
  lfSet_add (restrict_mem_lfSet (tau_mem_lfSet μ ν) _) (restrict_mem_lfSet (tau_mem_lfSet μ ν₂) _)

namespace ExplScheme

/-- The kernel `K_{k,η}` of the masked `k`-th probe. -/
noncomputable def kernelAt (k : ℕ) (η : Hist U S k) : Measure (Outcome S) :=
  probeKernel μ (sch.Rt k η) (sch.h k η)

theorem unexpl_snoc_renew (k : ℕ) (η : Hist U S k) (ν ν₂ : Measure S) :
    sch.unexpl (k + 1) (η.snoc (sch.stepAt k η ν)) ν =
      sch.unexpl (k + 1) (η.snoc (sch.stepAt k η ν))
        (probeRenew μ (sch.Rt k η) (sch.h k η) ν ν₂) := by
  unfold unexpl
  rw [tau_of_mem μ (probeRenew_mem_lfSet ν ν₂), Z_snoc_stepAt]
  set D := probeRegion (sch.Rt k η) (sch.stepAt k η ν).1 with hD
  have hDm : MeasurableSet D := measurableSet_probeRegion (sch.isProbe_Rt k η).measurable _
  have hZm := sch.measurableSet_Zη k η
  unfold probeRenew
  have hρ : probeRho μ (sch.Rt k η) (sch.h k η) ν = (sch.stepAt k η ν).1 := rfl
  rw [hρ, ← hD, Measure.restrict_add]
  have hWm : MeasurableSet (sch.Z k η ∪ D)ᶜ := (hZm.union hDm).compl
  rw [Measure.restrict_restrict hWm, Measure.restrict_restrict hWm,
    Set.inter_eq_left.2 (show (sch.Z k η ∪ D)ᶜ ⊆ Dᶜ from
      Set.compl_subset_compl.2 Set.subset_union_right),
    Set.disjoint_iff_inter_eq_empty.1 (show Disjoint (sch.Z k η ∪ D)ᶜ D from
      disjoint_compl_left_iff.2 Set.subset_union_right), Measure.restrict_empty, add_zero]

theorem measurable_unexpl_snoc (k : ℕ) (η : Hist U S k) :
    Measurable fun q : Outcome S × Measure S => sch.unexpl (k + 1) (η.snoc q.1) q.2 :=
  (sch.measurable_unexpl (k + 1)).comp
    (((Hist.measurable_snoc k).comp (measurable_const.prodMk measurable_fst)).prodMk
      measurable_snd)

/-- Sequential first-point exploration, Step 2: the integral over `W` at a fixed history, by the
one-step lemma. -/
theorem lintegral_step_unexpl (hW : IsPPPLaw μ W) (k : ℕ) (η : Hist U S k)
    {G : Hist U S (k + 1) × Measure S → ℝ≥0∞} (hG : Measurable G) :
    ∫⁻ ν, G (η.snoc (sch.stepAt k η ν), sch.unexpl (k + 1) (η.snoc (sch.stepAt k η ν)) ν) ∂W =
      ∫⁻ o, ∫⁻ m, G (η.snoc o, sch.unexpl (k + 1) (η.snoc o) m) ∂W ∂(sch.kernelAt k η) := by
  have := hW.isProbabilityMeasure
  have hP := sch.isProbe_Rt k η
  let Γ : Outcome S × Measure S → ℝ≥0∞ := fun q => G (η.snoc q.1, sch.unexpl (k + 1) (η.snoc q.1) q.2)
  have hΓ : Measurable Γ :=
    hG.comp (((Hist.measurable_snoc k).comp (measurable_const.prodMk measurable_fst)).prodMk
      (sch.measurable_unexpl_snoc k η))
  have hstep := measurable_probeStep μ (h := sch.h k η) hP.measurable
  have hren := measurable_probeRenew μ (h := sch.h k η) hP.measurable
  have hmeas : Measurable fun p : Measure S × Measure S =>
      (probeStep μ (sch.Rt k η) (sch.h k η) p.1,
        probeRenew μ (sch.Rt k η) (sch.h k η) p.1 p.2) :=
    (hstep.comp measurable_fst).prodMk hren
  have e1 : ∫⁻ ν, G (η.snoc (sch.stepAt k η ν), sch.unexpl (k + 1) (η.snoc (sch.stepAt k η ν)) ν) ∂W =
      ∫⁻ p, Γ (probeStep μ (sch.Rt k η) (sch.h k η) p.1,
        probeRenew μ (sch.Rt k η) (sch.h k η) p.1 p.2) ∂(W.prod W) := by
    have hmΓ : Measurable fun p : Measure S × Measure S =>
        Γ (probeStep μ (sch.Rt k η) (sch.h k η) p.1,
          probeRenew μ (sch.Rt k η) (sch.h k η) p.1 p.2) := hΓ.comp hmeas
    rw [lintegral_prod _ hmΓ.aemeasurable]
    refine lintegral_congr fun ν => ?_
    have : ∀ ν₂ : Measure S, Γ (probeStep μ (sch.Rt k η) (sch.h k η) ν,
        probeRenew μ (sch.Rt k η) (sch.h k η) ν ν₂) =
        G (η.snoc (sch.stepAt k η ν), sch.unexpl (k + 1) (η.snoc (sch.stepAt k η ν)) ν) := by
      intro ν₂
      change G (η.snoc (sch.stepAt k η ν), sch.unexpl (k + 1) (η.snoc (sch.stepAt k η ν))
        (probeRenew μ (sch.Rt k η) (sch.h k η) ν ν₂)) = _
      rw [← sch.unexpl_snoc_renew k η ν ν₂]
    simp [this]
  rw [e1, ← lintegral_map hΓ hmeas, oneStep_law hW hP, lintegral_prod _ hΓ.aemeasurable]
  rfl

end ExplScheme

end ElboimSly
