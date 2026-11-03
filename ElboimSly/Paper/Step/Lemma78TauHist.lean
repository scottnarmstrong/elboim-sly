/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Step.Lemma78CoupleZeta
public import ElboimSly.Paper.Step.Lemma78TauSurr
public import ElboimSly.Paper.Step.CfAe
public import Mathlib

/-!
# The frozen history of `W₂` at a stopping time `Z` of `(ℱ⁺_t)`

One excursion succeeds with probability at least frac12 ("The history"), the space of frozen histories (b), paths (c).
For a `(ℱ⁺_t)`-stopping time `Z`:

* `step78_ms_le`: `ℱ⁺_Z ≤ ℱ_{t'_n + Z}` (they are equal, only `≤` is needed);
* `step78_measurable_stopReal`: `Z` (as a real) is `ℱ⁺_Z`-measurable;
* `step78_measurable_hist`: the history `(ω, s) ↦ W₂((max s 0) ∧ Z)` is `ℱ⁺_Z ⊗ ℬ`-measurable
  (`measurable_stoppedPath` applied to `W₂` as a `CPath`);
* `step78_isRCPath_hist`: the history is a right-continuous path.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Step

open ElboimSly ElboimSly.Cyclic ElboimSly.Paper

set_option linter.unusedSectionVars false

variable {d : ℕ} {β : ℝ} [Fact (0 < β)] (u : Fin d → ℤ) (q : ℝ) (Tn : ℝ≥0)
  {Ω : Type*} (𝒢₀ : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] {Pr : Measure Ω}
  {N : Ω → Measure (CycS Unit d β)}
  (hN : IsPoissonPointProcess N (cycIntensity Unit d β) Pr) (h𝒢 : 𝒢₀ ≤ mΩ)

/-- `ℱ⁺_Z ≤ ℱ_{t'_n + Z}`. -/
theorem step78_ms_le {Z : Ω → WithTop ℝ≥0} (hZ : IsStoppingTime (step78Filt u q Tn 𝒢₀ hN h𝒢) Z) :
    hZ.measurableSpace ≤ (step78_isStoppingTime_T u q Tn 𝒢₀ hN h𝒢 hZ).measurableSpace := by
  intro A hA
  rw [IsStoppingTime.measurableSet] at hA ⊢
  refine ⟨?_, fun s => ?_⟩
  · have hle : (⨆ t, step78Filt u q Tn 𝒢₀ hN h𝒢 t) ≤
        ⨆ t, cycMultiFilt (step78Plan d β u q Tn) 𝒢₀ hN.measurable h𝒢 Pr t :=
      iSup_le fun t => le_iSup_of_le (Tn + t) le_rfl
    exact hle _ hA.1
  · by_cases hs : Tn ≤ s
    · have e : A ∩ {ω | step78T Tn Z ω ≤ (s : WithTop ℝ≥0)} =
          A ∩ {ω | Z ω ≤ ((s - Tn : ℝ≥0) : WithTop ℝ≥0)} := by
        ext ω
        simp only [mem_inter_iff, mem_ofPred_eq, step78T]
        refine and_congr_right fun _ => ?_
        cases hz : Z ω with
        | top =>
          rw [WithTop.add_top]
          exact ⟨fun h => absurd h (WithTop.not_top_le_coe _),
            fun h => absurd h (WithTop.not_top_le_coe _)⟩
        | coe a =>
          rw [← WithTop.coe_add, WithTop.coe_le_coe, WithTop.coe_le_coe, le_tsub_iff_left hs]
      rw [e]
      have h := hA.2 (s - Tn)
      exact (cycMultiFilt (step78Plan d β u q Tn) 𝒢₀ hN.measurable h𝒢 Pr).mono
        (le_of_eq (add_tsub_cancel_of_le hs)) _ h
    · have e : A ∩ {ω | step78T Tn Z ω ≤ (s : WithTop ℝ≥0)} = ∅ := by
        ext ω
        simp only [mem_inter_iff, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and, not_le]
        intro _
        refine lt_of_lt_of_le ?_ (le_add_of_nonneg_right bot_le)
        exact WithTop.coe_lt_coe.2 (not_le.1 hs)
      rw [e]
      exact @MeasurableSet.empty _
        (cycMultiFilt (step78Plan d β u q Tn) 𝒢₀ hN.measurable h𝒢 Pr s)

/-- `W₂` as a `CPath` (on good environments, regular by `step78_isRegPath_cycWalk`). -/
noncomputable def step78Wcp (N : Ω → Measure (CycS Unit d β)) (ω : Ω) : CPath (Fin d → ℤ) :=
  regCPath (fun s : ℝ≥0 => cycWalk (cycSlice () (cycNgood N ω)) u q (s : ℝ))
    (step78_isRegPath_cycWalk (ν := cycNgood N ω) (cycGood_cycNgood N ω) u q Tn)

/-- `Z` (as a real number, `0` on `{Z = ∞}`) is `ℱ⁺_Z`-measurable. -/
theorem step78_measurable_stopReal {Z : Ω → WithTop ℝ≥0}
    (hZ : IsStoppingTime (step78Filt u q Tn 𝒢₀ hN h𝒢) Z) :
    Measurable[hZ.measurableSpace] (fun ω => ((ElboimSly.SRW.stopReal Z ω : ℝ≥0) : ℝ)) :=
  (measurable_stopReal_stop hZ).coe_nnreal_real

/-- The stopped `CPath` of `W₂` is `ℱ⁺_Z`-measurable (paths (c)). -/
theorem step78_measurable_Wcp_stop {Z : Ω → WithTop ℝ≥0}
    (hZ : IsStoppingTime (step78Filt u q Tn 𝒢₀ hN h𝒢) Z) :
    Measurable[hZ.measurableSpace]
      (fun ω => (step78Wcp u q Tn N ω).stop (ElboimSly.SRW.stopReal Z ω)) :=
  measurable_stoppedPath (f := step78Filt u q Tn 𝒢₀ hN h𝒢) (step78Wcp u q Tn N)
    (fun s => step78_measurable_walk2 u q Tn 𝒢₀ hN h𝒢 s) hZ

/-- **History** (the space of frozen histories (b)): `(ω, s) ↦ W₂((max s 0) ∧ Z)` is `ℱ⁺_Z ⊗ ℬ`-measurable. -/
theorem step78_measurable_hist (n : ℕ) (ρ : ℝ) {Z : Ω → WithTop ℝ≥0}
    (hZ : IsStoppingTime (step78Filt u q Tn 𝒢₀ hN h𝒢) Z) :
    Measurable[hZ.measurableSpace.prod inferInstance] fun p : Ω × ℝ =>
      (step78SliceData (cycNgood N) u q Tn n ρ).path p.1
        (min ((fun _ => (0 : ℝ)) p.1 + max p.2 0) ((ElboimSly.SRW.stopReal Z p.1 : ℝ≥0) : ℝ)) := by
  have hsp := step78_measurable_Wcp_stop u q Tn 𝒢₀ hN h𝒢 hZ
  have hg : Measurable[hZ.measurableSpace.prod inferInstance] fun p : Ω × ℝ =>
      (max p.2 0).toNNReal :=
    Measurable.real_toNNReal ((@measurable_snd Ω ℝ hZ.measurableSpace _).max measurable_const)
  have hP : Measurable[hZ.measurableSpace.prod inferInstance] fun p : Ω × ℝ =>
      (step78Wcp u q Tn N p.1).stop (ElboimSly.SRW.stopReal Z p.1) :=
    @Measurable.comp _ _ _ (hZ.measurableSpace.prod inferInstance) _ _ _ _ hsp
      (@measurable_fst Ω ℝ hZ.measurableSpace _)
  have h := @measurable_fn_at (Fin d → ℤ) _ _ _ (Ω × ℝ) (hZ.measurableSpace.prod inferInstance)
    _ hP _ hg
  have e : (fun p : Ω × ℝ => (step78SliceData (cycNgood N) u q Tn n ρ).path p.1
        (min ((fun _ => (0 : ℝ)) p.1 + max p.2 0) ((ElboimSly.SRW.stopReal Z p.1 : ℝ≥0) : ℝ))) =
      fun p => ((step78Wcp u q Tn N p.1).stop (ElboimSly.SRW.stopReal Z p.1)).fn
        (max p.2 0).toNNReal := by
    funext p
    show cycWalk (cycSlice () (cycNgood N p.1)) u q
        (((min (0 + max p.2 0) ((ElboimSly.SRW.stopReal Z p.1 : ℝ≥0) : ℝ)).toNNReal : ℝ≥0) : ℝ) =
      cycWalk (cycSlice () (cycNgood N p.1)) u q
        ((min (max p.2 0).toNNReal (ElboimSly.SRW.stopReal Z p.1) : ℝ≥0) : ℝ)
    congr 2
    rw [zero_add, Monotone.map_min (f := Real.toNNReal) (fun _ _ h => Real.toNNReal_mono h),
      Real.toNNReal_coe]
  rw [e]
  exact h

/-- The history is a right-continuous path. -/
theorem step78_isRCPath_hist (n : ℕ) (ρ : ℝ) (Z : Ω → WithTop ℝ≥0) (ω : Ω) :
    IsRCPath (fun s : ℝ≥0 => (step78SliceData (cycNgood N) u q Tn n ρ).path ω
      (min ((fun _ => (0 : ℝ)) ω + (s : ℝ)) ((ElboimSly.SRW.stopReal Z ω : ℝ≥0) : ℝ))) := by
  have e : (fun s : ℝ≥0 => (step78SliceData (cycNgood N) u q Tn n ρ).path ω
      (min ((fun _ => (0 : ℝ)) ω + (s : ℝ)) ((ElboimSly.SRW.stopReal Z ω : ℝ≥0) : ℝ))) =
      ((step78Wcp u q Tn N ω).stop (ElboimSly.SRW.stopReal Z ω)).fn := by
    funext s
    show cycWalk (cycSlice () (cycNgood N ω)) u q
        (((min (0 + (s : ℝ)) ((ElboimSly.SRW.stopReal Z ω : ℝ≥0) : ℝ)).toNNReal : ℝ≥0) : ℝ) =
      cycWalk (cycSlice () (cycNgood N ω)) u q
        ((min s (ElboimSly.SRW.stopReal Z ω) : ℝ≥0) : ℝ)
    congr 2
    rw [zero_add, Monotone.map_min (f := Real.toNNReal) (fun _ _ h => Real.toNNReal_mono h),
      Real.toNNReal_coe, Real.toNNReal_coe]
  rw [e]
  exact fun t => ((step78Wcp u q Tn N ω).stop (ElboimSly.SRW.stopReal Z ω)).rc t

end ElboimSly.Paper.Step

end
