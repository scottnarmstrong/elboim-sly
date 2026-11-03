/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Escape.Es55PWCore
public import ElboimSly.Paper.Escape.Es55JumpProof
public import ElboimSly.Foundations.Interchange.SymmRev
public import Mathlib

/-!
# Step 1 of ES22 Lemma 5.5: the backward entry is the backward trajectory

ES22 Lemma 5.5, Step 1, "Conclusion of Step 1" (reading the driven rules; scope(3)).

For a good environment `ν` and a point `p` such that no edge at `p` rings at the cyclic time `β'`
in the first slice `μ = ν^0`, the backward environment path `P^ν_{(0,p,β',-1)}` satisfies

* `pwc_bwd_left`: `η^μ_{p,β'}(β' - s) = P(s-)` for `s > 0`;
* `pwc_bwd_eventually`: `η^μ_{p,β'}(τ) = P(r)` for `τ` slightly below `β' - r`.

Also `pwc_ae_noRings`: a.s. no edge at a point rings at a fixed time in the first slice.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Escape

open ElboimSly ElboimSly.Cyclic ElboimSly.Interchange ElboimSly.Paper

set_option linter.unusedSectionVars false

section bwd

variable {k : ℕ} {β : ℝ} [Fact (0 < β)]

theorem pwc_reflect_reflect (μ : Measure (RingSpace k β)) :
    reflectMeasure β (reflectMeasure β μ) = μ := by
  unfold reflectMeasure ringPush
  rw [Measure.map_map (ringMapEquiv _ _).measurable (ringMapEquiv _ _).measurable]
  have : (⇑(ringMapEquiv (Equiv.refl (Edge k)) (MeasurableEquiv.neg (AddCircle β))) ∘
      ⇑(ringMapEquiv (Equiv.refl (Edge k)) (MeasurableEquiv.neg (AddCircle β)))) = id := by
    funext x
    simp [ringMapEquiv_apply]
  rw [this, Measure.map_id]

/-- The backward trajectory of `μ` is the left-limit path of the forward trajectory of the
reflected configuration, when no edge at `p` rings at `β'`. -/
theorem pwc_bwdTrajFn_eq {μ : Measure (RingSpace k β)} (hμ : Good μ) (p : Fin k → ℤ) (β' : ℝ)
    (hring : ¬ ∃ e : Edge k, e.Mem p ∧ Rings μ e β') :
    bwdTrajFn hμ p β' = fwdLeft (good_reflectMeasure hμ) p (-β') := by
  have hring' : ¬ ∃ e : Edge k, e.Mem p ∧ Rings (reflectMeasure β μ) e (-β') := by
    rintro ⟨e, he, hr⟩
    exact hring ⟨e, he, by simpa [rings_reflectMeasure] using hr⟩
  have h := bwdTrajFn_reflectMeasure (good_reflectMeasure hμ) p (-β') hring'
  rw [neg_neg] at h
  have hconv : ∀ η, IsBackwardTrajectory (reflectMeasure β (reflectMeasure β μ)) p β' η →
      IsBackwardTrajectory μ p β' η := fun η hη => by rwa [pwc_reflect_reflect] at hη
  have hspec := hconv _ (bwdTrajFn_spec (good_reflectMeasure (good_reflectMeasure hμ)) p β')
  rw [← h]
  exact (bwdTrajFn_eq hμ hspec).symm.trans rfl

variable {ν : Measure (CycS ℕ k β)}

theorem pwc_envFn_back (hμ : Good (cycSlice 0 ν)) (p : Fin k → ℤ) (β' : ℝ) :
    envFn ν ((0 : ℕ), p, β', false) = fwdTrajFn (good_reflectMeasure hμ) p (-β') := by
  have h := envFn_spec (ν := ν) (δ := ((0 : ℕ), p, β', false)) hμ
  have e1 : envMeasure ν ((0 : ℕ), p, β', false) = reflectMeasure β (cycSlice 0 ν) := by
    simp [envMeasure, CycData.fwd, CycData.copy]
  have e2 : CycData.sgn (((0 : ℕ), p, β', false) : CycData ℕ k) *
      CycData.phase (((0 : ℕ), p, β', false) : CycData ℕ k) = -β' := by
    simp [CycData.sgn, CycData.fwd, CycData.phase]
  have e3 : CycData.start (((0 : ℕ), p, β', false) : CycData ℕ k) = p := rfl
  rw [e1, e2, e3] at h
  exact fwdTrajFn_eq (good_reflectMeasure hμ) h

/-- `η^μ_{p,β'}(β' - s) = P(s-)` for the backward environment path `P` and `s > 0`. -/
theorem pwc_bwd_left (hν : CycGood ν) (p : Fin k → ℤ) (β' : ℝ)
    (hring : ¬ ∃ e : Edge k, e.Mem p ∧ Rings (cycSlice 0 ν) e β') {s : ℝ≥0} (hs : 0 < s) :
    bwdTraj (hν 0) p β' (β' - s) = (envPath ν ((0 : ℕ), p, β', false)).1.left s := by
  have hgood : Good (cycSlice (CycData.copy (((0 : ℕ), p, β', false) : CycData ℕ k)) ν) := hν 0
  obtain ⟨-, hfn⟩ := envPath_len (ν := ν) (δ := ((0 : ℕ), p, β', false)) hgood
  have h1 : bwdTraj (hν 0) p β' (β' - s) = bwdTrajFn (hν 0) p β' s := by
    simp [bwdTraj, bwdReal]
  rw [h1, pwc_bwdTrajFn_eq (hν 0) p β' hring]
  have hL : IsLeftLimit (envFn ν ((0 : ℕ), p, β', false)) s
      ((envPath ν ((0 : ℕ), p, β', false)).1.left s) := by
    rw [← hfn]; exact (envPath ν ((0 : ℕ), p, β', false)).1.eventually_left hs
  rw [pwc_envFn_back (hν 0)] at hL
  exact IsLeftLimit.unique hs (fwdLeft_isLeftLimit _ p (-β') hs) hL

/-- Just below the time `β' - r`, the backward trajectory equals `P(r)`. -/
theorem pwc_bwd_eventually (hν : CycGood ν) (p : Fin k → ℤ) (β' : ℝ)
    (hring : ¬ ∃ e : Edge k, e.Mem p ∧ Rings (cycSlice 0 ν) e β') (r : ℝ≥0) :
    ∃ a0 < β' - r, ∀ τ ∈ Ioo a0 (β' - r),
      bwdTraj (hν 0) p β' τ = (envPath ν ((0 : ℕ), p, β', false)).1.fn r := by
  set P := (envPath ν ((0 : ℕ), p, β', false)).1 with hP
  obtain ⟨u1, hu1, hsub⟩ := mem_nhdsGE_iff_exists_Ico_subset.1 (P.rc r)
  refine ⟨β' - u1, by have : (r : ℝ) < u1 := by exact_mod_cast hu1
                      linarith, fun τ hτ => ?_⟩
  have hs : (0 : ℝ) < β' - τ := by linarith [hτ.2, r.2]
  have hτr : (r : ℝ) < β' - τ := by linarith [hτ.2]
  have hτu : β' - τ < u1 := by linarith [hτ.1]
  set s : ℝ≥0 := (β' - τ).toNNReal with hsdef
  have hsR : (s : ℝ) = β' - τ := Real.coe_toNNReal _ hs.le
  have hrs : r < s := by
    rw [← NNReal.coe_lt_coe, hsR]; exact hτr
  have hsu : s < u1 := by
    rw [← NNReal.coe_lt_coe, hsR]; exact hτu
  have hs0 : 0 < s := lt_of_le_of_lt (zero_le : (0 : ℝ≥0) ≤ r) hrs
  have := pwc_bwd_left hν p β' hring hs0
  rw [hsR, show β' - (β' - τ) = τ by ring] at this
  rw [this]
  refine P.left_eq_of_eventually hs0 ?_
  filter_upwards [Ico_mem_nhdsLT hrs] with u hu
  exact hsub ⟨hu.1, hu.2.trans hsu⟩

end bwd

section ae

variable {d : ℕ} {β : ℝ} [Fact (0 < β)]

/-- A.s. no edge at a point rings at a fixed time in the first slice of a Poisson environment. -/
theorem pwc_ae_noRings {Ω : Type} [MeasurableSpace Ω] {Pr : Measure Ω}
    {N : Ω → Measure (CycS ℕ d β)} (hN : IsPoissonPointProcess N (cycIntensity ℕ d β) Pr)
    (p : Fin d → ℤ) (t : ℝ) :
    ∀ᵐ ω ∂Pr, ¬ ∃ e : Edge d, e.Mem p ∧ Rings (cycSlice 0 (N ω)) e t := by
  filter_upwards [ae_noRings (Pr := Pr) (N'' := N) hN t] with ω h
  rintro ⟨e, -, he⟩
  exact h 0 e he

end ae

end ElboimSly.Paper.Escape
