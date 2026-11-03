/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycSchemeMeas3
public import Mathlib

/-!
# The environment scheme as an `ExplScheme`

The environment scheme of a plan; The environment scheme (a), first sentence: "the environment scheme of a plan
defines an exploration scheme on `(𝒮, μ)`" (the explored-region identity `Z_j(η) = R(ρ_j(η))` is
*not* proved here).

* `cycScheme P sc U`: the scheme, `R k η = probeR (stateAt k η)`, `h k η = hOf (stateAt k η)`;
* `cycScheme_Rt`: the masked probe is the cyclic segment probe with mask `Z_k(η)`;
* `cycSegR_mask`, `map_cycEquiv_restrict`: how masks and restrictions transport along `cycEquiv`.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

variable {I : Type*} [MeasurableSpace I] [MeasurableSingletonClass I] [Countable I] {d : ℕ}
  {β : ℝ} [Fact (0 < β)]

/-- The environment scheme (a): the environment scheme of a plan is an exploration scheme on
`(𝒮, μ)`, for every plan, global horizon `s_∘` and auxiliary space `U`. -/
noncomputable def cycScheme (P : CycPlan I d β) (sc : ℝ≥0∞) (U : Type*) [MeasurableSpace U] :
    ExplScheme (cycIntensity I d β) U where
  R k η := CycScheme.probeR P sc (CycScheme.stateAt P sc k η)
  h k η := CycScheme.hOf P sc (CycScheme.stateAt P sc k η)
  measurable_R k :=
    (CycScheme.measurable_probeR P sc).comp
      (((CycScheme.measurable_stateAt P sc k).comp measurable_fst).prodMk measurable_snd)
  measurable_h k := (measurable_hOf (P := P) (sc := sc) (CycScheme.measurable_stateAt P sc k))
  isProbe _k _η :=
    isProbe_cycSegR _ _ _ (fun e => (CycScheme.cur P _).frontS_cases e) _
      (CycScheme.hOf_le_beta P sc _) MeasurableSet.empty

variable {P : CycPlan I d β} {sc : ℝ≥0∞} {U : Type*} [MeasurableSpace U]

open scoped Classical in
omit [MeasurableSingletonClass I] [Countable I] [Fact (0 < β)] in
/-- A mask on `cycS` is a mask on `E × X`: the cyclic segment probe with mask `Z`. -/
theorem cycSegR_mask (A : Finset (I × Edge d)) (x : I × Edge d → ℝ → AddCircle β)
    (sinv : I × Edge d → AddCircle β → ℝ) (h : ℝ≥0) (Z : Set (CycS I d β)) (s : CycS I d β) :
    cycSegR A x sinv h Z s = if s ∈ Z then ⊤ else cycSegR A x sinv h ∅ s := by
  classical
  unfold cycSegR segR
  by_cases hs : s ∈ Z
  · have : cycEquiv s ∈ (cycEquiv (I := I) (d := d) (β := β)).symm ⁻¹' Z := by
      simp [hs]
    simp [hs]
  · have h1 : cycEquiv s ∉ (cycEquiv (I := I) (d := d) (β := β)).symm ⁻¹' Z := by
      simp [hs]
    simp [hs]

/-- The environment scheme (a), last sentence (the form): the masked probe of step `k` is
the cyclic segment probe with mask `Z_k(η)`. -/
theorem cycScheme_Rt (k : ℕ) (η : Hist U (CycS I d β) k) :
    (cycScheme P sc U).Rt k η = cycSegR (CycScheme.probeA P (CycScheme.stateAt P sc k η))
      (circX (CycScheme.cur P (CycScheme.stateAt P sc k η)).frontT
        (CycScheme.cur P (CycScheme.stateAt P sc k η)).frontS)
      (circS (CycScheme.cur P (CycScheme.stateAt P sc k η)).frontT
        (CycScheme.cur P (CycScheme.stateAt P sc k η)).frontS)
      (CycScheme.hOf P sc (CycScheme.stateAt P sc k η)) ((cycScheme P sc U).Z k η) := by
  classical
  funext s
  rw [cycSegR_mask]
  by_cases hz : s ∈ (cycScheme P sc U).Z k η
  · rw [(cycScheme P sc U).Rt_of_mem hz, ite_eq_left hz]
  · rw [(cycScheme P sc U).Rt_of_notMem hz, ite_eq_right hz]
    rfl

omit [MeasurableSingletonClass I] [Countable I] in
omit [Fact (0 < β)] in
/-- Restrictions transport along `cycEquiv`. -/
theorem map_cycEquiv_restrict (ν : Measure (CycS I d β)) (Z : Set (CycS I d β))
    (hZ : MeasurableSet Z) :
    (ν.restrict Z).map cycEquiv = (ν.map cycEquiv).restrict
      ((cycEquiv (I := I) (d := d) (β := β)).symm ⁻¹' Z) :=
  by
  rw [Measure.restrict_map cycEquiv.measurable (measurableSet_cycMask hZ)]
  have : (cycEquiv (I := I) (d := d) (β := β)) ⁻¹'
      ((cycEquiv (I := I) (d := d) (β := β)).symm ⁻¹' Z) = Z := by
    ext s; simp
  rw [this]

end ElboimSly.Cyclic

end
