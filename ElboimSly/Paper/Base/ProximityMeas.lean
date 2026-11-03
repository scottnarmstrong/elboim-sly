/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Base.ProximityDefs
public import ElboimSly.Paper.Base.RegularB
public import Mathlib

/-!
# The proximity time is a random variable

Proximity times of an independent walk ("Then `|U|` is a random variable"), via regular functionals of pairs of paths (a, b).

For `L ≤ T`, the Lebesgue measure of `baseProxSet` equals `Φ(γ)` for the regular pair of paths
`γ = (a + X₁, b + X₂)`, and `Φ` is measurable on `Π_T`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Paper

open ElboimSly.SRW ElboimSly.Paper.Base ElboimSly.Cyclic

variable {d : ℕ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {Ñ : Ω → Measure ((Dir d × Fin 2) × ℝ)}

theorem isStepPath_stop {V : Type*} {f : ℝ≥0 → V} (hf : IsStepPath f) (T : ℝ≥0) :
    IsStepPath fun u => f (min u T) := by
  refine ⟨fun s => ?_, fun S => ?_⟩
  · rcases lt_or_ge s T with hs | hs
    · filter_upwards [hf.rc s, Ico_mem_nhdsGE hs] with u hu hu'
      simp only [min_eq_left hu'.2.le, min_eq_left hs.le] at hu ⊢
      exact hu
    · filter_upwards [self_mem_nhdsWithin] with u hu
      simp only [min_eq_right (hs.trans hu), min_eq_right hs]
  · refine (hf.fin (max S T)).subset fun r hr => ?_
    obtain ⟨⟨hr0, hr1⟩, hr2⟩ := hr
    have hrT : r ≤ T := by
      by_contra hrT
      push Not at hrT
      refine hr1 ?_
      filter_upwards [Ioo_mem_nhdsLT hrT] with u hu
      simp only [min_eq_right hu.1.le, min_eq_right hrT.le]
    refine ⟨⟨hr0, fun hc => hr1 ?_⟩, hr2.trans (le_max_left _ _)⟩
    filter_upwards [hc, self_mem_nhdsWithin] with u hu hu'
    simp only [min_eq_left (hu'.out.le.trans hrT), min_eq_left hrT]
    exact hu

/-- The pair of paths `γ(ω) = (a + X₁, b + X₂)` in `Π_T`. -/
noncomputable def proxPaths (Ñ : Ω → Measure ((Dir d × Fin 2) × ℝ)) (a b : Fin d → ℤ) (T : ℝ≥0)
    (ω : Ω) : PathsOn d 2 T :=
  fun s => ![a + drvX Ñ 0 ω s.1, b + drvX Ñ 1 ω s.1]

omit [MeasurableSpace Ω] in
theorem extT_proxPaths_zero (a b : Fin d → ℤ) (T : ℝ≥0) (ω : Ω) (u : ℝ≥0) :
    extT T (proxPaths Ñ a b T ω) 0 u = a + drvX Ñ 0 ω (min u T) := rfl

omit [MeasurableSpace Ω] in
theorem extT_proxPaths_one (a b : Fin d → ℤ) (T : ℝ≥0) (ω : Ω) (u : ℝ≥0) :
    extT T (proxPaths Ñ a b T ω) 1 u = b + drvX Ñ 1 ω (min u T) := rfl

omit [MeasurableSpace Ω] in
theorem isRegularPaths_proxPaths (a b : Fin d → ℤ) (T : ℝ≥0) (ω : Ω) :
    IsRegularPaths T (proxPaths Ñ a b T ω) := by
  intro i
  fin_cases i
  · have hs := (drivers_isDrivingPath (Ñ := Ñ) 0 ω).step
    have hs' : IsStepPath fun u => a + drvX Ñ 0 ω u := by
      refine ⟨fun s => ?_, fun S => ?_⟩
      · filter_upwards [hs.rc s] with u hu; simp only [hu]
      · exact (hs.fin S).subset fun r hr =>
          ⟨⟨hr.1.1, fun hc => hr.1.2 (hc.mono fun u hu => by simp only [hu])⟩, hr.2⟩
    exact isStepPath_stop hs' T
  · have hs := (drivers_isDrivingPath (Ñ := Ñ) 1 ω).step
    have hs' : IsStepPath fun u => b + drvX Ñ 1 ω u := by
      refine ⟨fun s => ?_, fun S => ?_⟩
      · filter_upwards [hs.rc s] with u hu; simp only [hu]
      · exact (hs.fin S).subset fun r hr =>
          ⟨⟨hr.1.1, fun hc => hr.1.2 (hc.mono fun u hu => by simp only [hu])⟩, hr.2⟩
    exact isStepPath_stop hs' T

theorem measurable_proxPaths (h : IsPoissonPointProcess Ñ (clockIntensity (Dir d × Fin 2)) P)
    (a b : Fin d → ℤ) (T : ℝ≥0) : Measurable (proxPaths Ñ a b T) := by
  refine measurable_pi_iff.2 fun s => measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun k => ?_
  fin_cases i
  · have := (measurable_pi_apply k).comp ((measurable_pi_apply s.1).comp (measurable_drvX h 0))
    simpa [proxPaths] using this.const_add (a k)
  · have := (measurable_pi_apply k).comp ((measurable_pi_apply s.1).comp (measurable_drvX h 1))
    simpa [proxPaths] using this.const_add (b k)

omit [MeasurableSpace Ω] in
theorem lebSet_proxPaths (a b : Fin d → ℤ) {T L : ℝ≥0} (hL : L ≤ T) (ρ : ℝ) (ω : Ω) :
    lebSet T L ρ 0 1 (proxPaths Ñ a b T ω) = baseProxSet Ñ a b T L ρ ω := by
  ext x
  simp only [lebSet, baseProxSet, mem_ofPred_eq, extT_proxPaths_zero, extT_proxPaths_one]
  constructor
  · rintro ⟨hx0, hxT, y, hy0, hyL, hy⟩
    have hxT' : x.toNNReal ≤ T := Real.toNNReal_le_iff_le_coe.2 hxT
    refine ⟨hx0, hxT, y.toNNReal, Real.toNNReal_le_iff_le_coe.2 hyL, ?_⟩
    have hyT : y.toNNReal ≤ T := (Real.toNNReal_le_iff_le_coe.2 hyL).trans hL
    rw [min_eq_left hxT', min_eq_left hyT] at hy
    simpa [add_sub_add_left_eq_sub] using hy
  · rintro ⟨hx0, hxT, y, hyL, hy⟩
    have hxT' : x.toNNReal ≤ T := Real.toNNReal_le_iff_le_coe.2 hxT
    refine ⟨hx0, hxT, y, y.2, hyL, ?_⟩
    rw [Real.toNNReal_coe, min_eq_left (hyL.trans hL), min_eq_left hxT']
    simpa [add_sub_add_left_eq_sub] using hy

end ElboimSly.Paper
