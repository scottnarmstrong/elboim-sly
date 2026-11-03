/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycHitCoupleRegen
public import ElboimSly.Paper.Avoid.ProcessLaw
public import ElboimSly.Paper.Induction.RelaxedMeasRegen
public import Mathlib

/-!
# ES22 §4: auxiliary facts for ES22 Lemma 2.1

The regenerated walk of a good environment is right-continuous (`IsRCPath`); `avoidPath` of a
good environment is `regW`; the resampled walk `avoidPath (cycNgood M)` is a measurable process
with right-continuous paths, and almost surely equal to `regW M`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Paper

open ElboimSly.Cyclic

variable {d : ℕ} {β : ℝ} [Fact (0 < β)]

/-- The regenerated walk of a good environment is right-continuous on `ℝ≥0`. -/
theorem isRCPath_avoidPath {Ω : Type*} {X : Ω → Measure (CycS ℕ d β)} {ω : Ω}
    (hX : CycGood (X ω)) : IsRCPath (avoidPath X ω) := by
  intro t
  obtain ⟨ε, hε, hc⟩ := regenWalk_rlc (ν := avoidEnv X ω) (fun k => by rw [avoidEnv_eq_cycSlice]; exact hX k) t.2
  rw [Filter.Eventually, mem_nhdsGE_iff_exists_Ico_subset]
  refine ⟨t + ε.toNNReal, ?_, fun s hs => ?_⟩
  · exact lt_add_of_pos_right _ (Real.toNNReal_pos.2 hε)
  · have h1 : (t : ℝ) ≤ s := by exact_mod_cast hs.1
    have h2 : (s : ℝ) < t + ε := by
      have : ((s : ℝ≥0) : ℝ) < ((t + ε.toNNReal : ℝ≥0) : ℝ) := by exact_mod_cast hs.2
      rwa [NNReal.coe_add, Real.coe_toNNReal _ hε.le] at this
    exact hc (s : ℝ) ⟨h1, h2⟩

theorem avoidPath_eq_regW {Ω : Type*} {X : Ω → Measure (CycS ℕ d β)} {ω : Ω}
    (hX : CycGood (X ω)) : avoidPath X ω = regW (X ω) := by
  funext t
  rw [regW_eq_regenWalk hX]
  simp only [avoidPath, avoidWalk, avoidEnv_eq_cycSlice]

theorem measurable_avoidPath_cycNgood {Ω : Type*} [MeasurableSpace Ω]
    {X : Ω → Measure (CycS ℕ d β)} (hX : Measurable X) :
    Measurable (avoidPath (cycNgood X)) := by
  have h : avoidPath (cycNgood X) = fun ω => regW (cycNgood X ω) := by
    funext ω
    exact avoidPath_eq_regW (cycGood_cycNgood X ω)
  rw [h]
  exact measurable_regW.comp (measurable_cycNgood hX)

theorem ae_avoidPath_cycNgood {Ω : Type*} [MeasurableSpace Ω] {Pr : Measure Ω}
    {M : Ω → Measure (CycS ℕ d β)} (hM : IsPoissonPointProcess M (cycIntensity ℕ d β) Pr) :
    ∀ᵐ ω ∂Pr, avoidPath (cycNgood M) ω = regW (M ω) ∧ avoidPath M ω = regW (M ω) := by
  filter_upwards [ae_cycNgood_eq hM, CycSchemeEnv.ae_cycGood' hM] with ω h1 h2
  refine ⟨?_, avoidPath_eq_regW h2⟩
  rw [avoidPath_eq_regW (cycGood_cycNgood M ω)]
  simp only [h1]

/-- Independence transfers along an a.s. equality of the generating maps. -/
theorem indep_comap_congr {Ω Y : Type*} {m : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [MeasurableSpace Y]
    {Pr : Measure Ω} {f g : Ω → Y} (hfg : f =ᵐ[Pr] g)
    (h : Indep m (MeasurableSpace.comap g inferInstance) Pr) :
    Indep m (MeasurableSpace.comap f inferInstance) Pr := by
  refine indep_of_ae_sets h ?_
  rintro A ⟨B, hB, rfl⟩
  exact ⟨g ⁻¹' B, ⟨B, hB, rfl⟩, Filter.eventuallyEqSet_iff.2 (hfg.mono fun ω h => by simp [h])⟩

end ElboimSly.Paper

end
