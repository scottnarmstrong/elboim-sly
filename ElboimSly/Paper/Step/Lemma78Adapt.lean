/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Step.Lemma78Read
public import ElboimSly.Paper.Step.Lemma78Regular
public import ElboimSly.Paper.Step.Lemma78Closing
public import ElboimSly.Paper.Step.Lemma78CoupleCond
public import ElboimSly.Foundations.Cyclic.CycMultiMain
public import ElboimSly.Foundations.Cyclic.CycMultiRecStop
public import ElboimSly.Foundations.Cyclic.CPathStop
public import Mathlib

/-!
# The filtration `(ℱ⁺_t)` of Lemma 7.8 and the frame of the second walk

Setting of Lemma 7.8 (Exploration), measurability.
`ℱ⁺_t := ℱ^{𝔭₈}_{t'_n + t}` (`step78Filt`). The second walk `W₂ = W^{cycNgood N}_{u,q}` and the set
`V = W₁([0,t'_n])` form a `Step78Frame` for it (`step78_frame`), and `W₂` has the closing property
(`step78_closing`). Hence `ζ_i`, `ζ'_i` are `(ℱ⁺_t)`-stopping times, and `t'_n + ζ` is a stopping
time of the unshifted exploration filtration (`step78_isStoppingTime_T`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Step

open ElboimSly ElboimSly.Cyclic ElboimSly.Paper

set_option linter.unusedSectionVars false

variable {d : ℕ} {β : ℝ} [Fact (0 < β)] (u : Fin d → ℤ) (q : ℝ) (Tn : ℝ≥0)
  {Ω : Type*} (𝒢₀ : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] {Pr : Measure Ω}
  {N : Ω → Measure (CycS Unit d β)}
  (hN : IsPoissonPointProcess N (cycIntensity Unit d β) Pr) (h𝒢 : 𝒢₀ ≤ mΩ)

/-- `ℱ⁺_t := ℱ^{𝔭₈}_{t'_n + t}`. -/
noncomputable def step78Filt : Filtration ℝ≥0 mΩ where
  seq t := cycMultiFilt (step78Plan d β u q Tn) 𝒢₀ hN.measurable h𝒢 Pr (Tn + t)
  mono' a b hab := (cycMultiFilt (step78Plan d β u q Tn) 𝒢₀ hN.measurable h𝒢 Pr).mono
    (by gcongr)
  le' t := (cycMultiFilt (step78Plan d β u q Tn) 𝒢₀ hN.measurable h𝒢 Pr).le _

/-- `W₂(t)` is `ℱ⁺_t`-measurable. -/
theorem step78_measurable_walk2 (t : ℝ≥0) :
    Measurable[step78Filt u q Tn 𝒢₀ hN h𝒢 t]
      (fun ω => ElboimSly.cycWalk (cycSlice () (cycNgood N ω)) u q (t : ℝ)) := by
  have hm := measurable_trunc_multiFilt (step78Plan d β u q Tn) 𝒢₀ h𝒢 Pr
    (measurable_envFinal_cycNgood (step78Plan d β u q Tn) hN.measurable) (Tn + t)
  have hg : Measurable fun ρ : CycRec Unit d =>
      (ρ.coord (step78Plan d β u q Tn).junk 1).path.fn t :=
    measurable_fn_at (fun ρ : CycRec Unit d => (ρ.coord (step78Plan d β u q Tn).junk 1).path)
      (measurable_entry_path.comp (CycRec.measurable_coord _ 1)) (fun _ => t) measurable_const
  have e : (fun ω => ElboimSly.cycWalk (cycSlice () (cycNgood N ω)) u q (t : ℝ)) =
      fun ω => (fun ρ : CycRec Unit d => (ρ.coord (step78Plan d β u q Tn).junk 1).path.fn t)
        (CycRec.trunc (Tn + t) ((step78Plan d β u q Tn).envFinal (cycNgood N ω))) := by
    funext ω
    exact (step78_trunc_coord_one u q Tn (cycGood_cycNgood N ω) _ t).symm
  rw [e]
  exact hg.comp hm

/-- `W₁(s)`, `s ≤ t'_n`, is `ℱ_{t'_n}`-measurable. -/
theorem step78_measurable_walk1 {s : ℝ≥0} (hs : s ≤ Tn) :
    Measurable[cycMultiFilt (step78Plan d β u q Tn) 𝒢₀ hN.measurable h𝒢 Pr Tn]
      (fun ω => ElboimSly.cycWalk (cycSlice () (cycNgood N ω)) 0 0 (s : ℝ)) := by
  have hm := measurable_trunc_multiFilt (step78Plan d β u q Tn) 𝒢₀ h𝒢 Pr
    (measurable_envFinal_cycNgood (step78Plan d β u q Tn) hN.measurable) Tn
  have hg : Measurable fun ρ : CycRec Unit d =>
      (ρ.coord (step78Plan d β u q Tn).junk 0).path.fn s :=
    measurable_fn_at (fun ρ : CycRec Unit d => (ρ.coord (step78Plan d β u q Tn).junk 0).path)
      (measurable_entry_path.comp (CycRec.measurable_coord _ 0)) (fun _ => s) measurable_const
  have e : (fun ω => ElboimSly.cycWalk (cycSlice () (cycNgood N ω)) 0 0 (s : ℝ)) =
      fun ω => (fun ρ : CycRec Unit d => (ρ.coord (step78Plan d β u q Tn).junk 0).path.fn s)
        (CycRec.trunc Tn ((step78Plan d β u q Tn).envFinal (cycNgood N ω))) := by
    funext ω
    exact (step78_trunc_coord_zero u q Tn (cycGood_cycNgood N ω) _ hs).symm
  rw [e]
  exact hg.comp hm

/-- `{x ∈ V}` is `ℱ⁺_0`-measurable, where `V = W₁([0, t'_n])`. -/
theorem step78_measurableSet_V (x : Fin d → ℤ) :
    MeasurableSet[step78Filt u q Tn 𝒢₀ hN h𝒢 0]
      {ω | x ∈ ElboimSly.cycWalk (cycSlice () (cycNgood N ω)) 0 0 '' Icc (0 : ℝ) (Tn : ℝ)} := by
  classical
  set C : Set ℝ≥0 := {s | s ≤ Tn ∧ (s = Tn ∨ ∃ r : ℚ, s = (r : ℝ).toNNReal)} with hC
  have hCc : C.Countable := by
    refine ((Set.countable_singleton Tn).union (Set.countable_range
      (fun r : ℚ => (r : ℝ).toNNReal))).mono ?_
    rintro s ⟨-, h | ⟨r, hr⟩⟩
    · exact Or.inl h
    · exact Or.inr ⟨r, hr.symm⟩
  have hset : {ω | x ∈ ElboimSly.cycWalk (cycSlice () (cycNgood N ω)) 0 0 '' Icc (0 : ℝ) (Tn : ℝ)} =
      ⋃ s ∈ C, {ω | ElboimSly.cycWalk (cycSlice () (cycNgood N ω)) 0 0 (s : ℝ) = x} := by
    ext ω
    simp only [mem_ofPred_eq, mem_image, mem_Icc, mem_iUnion, exists_prop]
    constructor
    · rintro ⟨y, ⟨hy0, hyT⟩, rfl⟩
      have hs'T : y.toNNReal ≤ Tn := Real.toNNReal_le_iff_le_coe.2 hyT
      have hyy : ((y.toNNReal : ℝ≥0) : ℝ) = y := Real.coe_toNNReal _ hy0
      rcases hs'T.eq_or_lt with heq | hlt
      · exact ⟨y.toNNReal, ⟨hs'T, Or.inl heq⟩, by rw [hyy]⟩
      · have hrc := (step78_isRegPath_cycWalk (ν := cycNgood N ω) (cycGood_cycNgood N ω) 0 0
          Tn).rc y.toNNReal
        obtain ⟨u', hu', hsub⟩ := mem_nhdsGE_iff_exists_Ico_subset.1 hrc
        obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn (lt_min (show ((y.toNNReal : ℝ≥0) : ℝ) <
          (u' : ℝ) from hu') (show ((y.toNNReal : ℝ≥0) : ℝ) < (Tn : ℝ) from hlt))
        have hr0 : (0 : ℝ) ≤ r := by
          have := hyy ▸ hr1
          linarith [hy0]
        have hrr : (((r : ℝ).toNNReal : ℝ≥0) : ℝ) = r := Real.coe_toNNReal _ hr0
        have hmem : (r : ℝ).toNNReal ∈ Ico y.toNNReal u' := by
          refine ⟨?_, ?_⟩
          · rw [← NNReal.coe_le_coe, hrr]; exact hr1.le
          · rw [← NNReal.coe_lt_coe, hrr]; exact hr2.trans_le (min_le_left _ _)
        refine ⟨(r : ℝ).toNNReal, ⟨?_, Or.inr ⟨r, rfl⟩⟩, ?_⟩
        · rw [← NNReal.coe_le_coe, hrr]; exact hr2.le.trans (min_le_right _ _)
        · have := hsub hmem
          simp only [mem_ofPred_eq] at this
          rw [this, hyy]
    · rintro ⟨s, ⟨hsT, -⟩, hs⟩
      exact ⟨s, ⟨s.2, by exact_mod_cast hsT⟩, hs⟩
  rw [hset]
  refine MeasurableSet.biUnion hCc fun s hs => ?_
  have h1 := step78_measurable_walk1 u q Tn 𝒢₀ hN h𝒢 hs.1
  have h2 : MeasurableSet[cycMultiFilt (step78Plan d β u q Tn) 𝒢₀ hN.measurable h𝒢 Pr Tn]
      {ω | ElboimSly.cycWalk (cycSlice () (cycNgood N ω)) 0 0 (s : ℝ) = x} :=
    h1 (Set.Countable.measurableSet (Set.to_countable ({x} : Set (Fin d → ℤ))))
  exact (cycMultiFilt (step78Plan d β u q Tn) 𝒢₀ hN.measurable h𝒢 Pr).mono
    (le_of_eq (add_zero Tn).symm) _ h2

/-- The frame hypotheses of measurability for the second walk of Lemma 7.8. -/
theorem step78_frame (hd : 1 ≤ d) (hβ : 1 < β) (n : ℕ) (ρ : ℝ) :
    Step78Frame (step78SliceData (cycNgood N) u q Tn n ρ) (step78Filt u q Tn 𝒢₀ hN h𝒢) where
  hd := hd
  hβ := hβ
  hw := fun t => step78_measurable_walk2 u q Tn 𝒢₀ hN h𝒢 t
  hrc := fun ω t =>
    (step78_isRegPath_cycWalk (ν := cycNgood N ω) (cycGood_cycNgood N ω) u q Tn).rc t
  hfin := fun ω => stepEventsFiniteW_of_isRegPath
    (step78_isRegPath_cycWalk (ν := cycNgood N ω) (cycGood_cycNgood N ω) u q Tn)
  hV := fun x => step78_measurableSet_V u q Tn 𝒢₀ hN h𝒢 x

/-- The closing property (closing (b)) of `W₂`. -/
theorem step78_closing (n : ℕ) (ρ : ℝ) :
    Step78Closing (step78SliceData (cycNgood N) u q Tn n ρ) := by
  intro ω k hk hw r hr
  have hβ : 0 < β := Fact.out
  have hkβ : (0 : ℝ) ≤ k * β := by positivity
  have hw' : ElboimSly.cycWalk (cycSlice () (cycNgood N ω)) u q ((k : ℝ) * β) = u := by
    have : ((((k : ℝ) * β).toNNReal : ℝ≥0) : ℝ) = k * β := Real.coe_toNNReal _ hkβ
    have h2 : ElboimSly.cycWalk (cycSlice () (cycNgood N ω)) u q
        ((((k : ℝ) * β).toNNReal : ℝ≥0) : ℝ) = u := hw
    rwa [this] at h2
  rw [step78SliceData_path _ u q Tn n ρ ω (by show (0 : ℝ) ≤ r + k * β; linarith),
    step78SliceData_path _ u q Tn n ρ ω hr]
  exact step78_cycWalk_period ((cycGood_cycNgood N ω) ()) u q hk hw' hr

end ElboimSly.Paper.Step

end
