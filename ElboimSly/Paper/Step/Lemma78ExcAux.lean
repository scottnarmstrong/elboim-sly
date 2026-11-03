/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Step.Lemma78Discharge
public import Mathlib

/-!
# Auxiliary facts

* `step78_freeze_le2`: the freezing lemma (freezing an independent variable) in the form in which
  Plan-level coupling after a stopping time (d) delivers independence: `P(A ∩ M ∩ {Y ∈ Γ}) = P(A ∩ M) ν(Γ)` for
  `A ∈ H`, `Γ` measurable, with `M` a fixed event and no measurability assumption on `Y`.
* `step78_measurableSpace_le`: `ℱ⁺_Z ≤ ℱ_{t'_n + Z}`.
* `step78_visited_finite`: `V = W₁([0,t'_n])` is a finite set for a regular path.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Step

open ElboimSly ElboimSly.Cyclic ElboimSly.Paper

section freeze

variable {Ω E F : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace F]

theorem step78_freeze_le2 (Hs : {m : MeasurableSpace Ω // m ≤ mΩ}) {P : Measure Ω}
    {x : Ω → E} (hc : (range x).Countable)
    (hx : ∀ e, MeasurableSet[Hs.1] {ω | x ω = e}) {Y : Ω → F} (ν : Measure F) (M : Set Ω)
    (hind : ∀ A, MeasurableSet[Hs.1] A → ∀ Γ, MeasurableSet Γ →
      P (A ∩ M ∩ Y ⁻¹' Γ) = P (A ∩ M) * ν Γ)
    {S : E → Set F} (hS : ∀ e, MeasurableSet (S e)) {G : Set Ω} (hG : MeasurableSet[Hs.1] G)
    (hGM : G ⊆ M) {ε : ℝ≥0∞} (hε : ∀ ω ∈ G, ν (S (x ω)) ≤ ε) :
    P (G ∩ {ω | Y ω ∈ S (x ω)}) ≤ ε * P G := by
  have : Countable (range x) := hc.to_subtype
  have hGm : MeasurableSet[mΩ] G := Hs.2 _ hG
  have hxm : ∀ e, MeasurableSet[mΩ] {ω | x ω = e} := fun e => Hs.2 _ (hx e)
  have hdisj : Pairwise (Function.onFun Disjoint fun e : range x => G ∩ {ω | x ω = e}) := by
    intro e e' hne
    refine Set.disjoint_left.2 fun ω h1 h2 => hne ?_
    exact Subtype.ext (h1.2.symm.trans h2.2)
  have hU : G = ⋃ e : range x, G ∩ {ω | x ω = e} := by
    ext ω
    simp only [mem_iUnion, mem_inter_iff, mem_ofPred_eq]
    exact ⟨fun h => ⟨⟨x ω, ω, rfl⟩, h, rfl⟩, fun ⟨_, h, _⟩ => h⟩
  have hU2 : G ∩ {ω | Y ω ∈ S (x ω)} ⊆
      ⋃ e : range x, (G ∩ {ω | x ω = e}) ∩ Y ⁻¹' S e := by
    intro ω ⟨hg, hy⟩
    simp only [mem_iUnion, mem_inter_iff, mem_ofPred_eq, mem_preimage]
    exact ⟨⟨x ω, ω, rfl⟩, ⟨hg, rfl⟩, hy⟩
  have hterm : ∀ e : range x, P ((G ∩ {ω | x ω = e}) ∩ Y ⁻¹' S e) ≤
      ε * P (G ∩ {ω | x ω = e}) := by
    intro e
    have hA : MeasurableSet[Hs.1] (G ∩ {ω | x ω = e}) := hG.inter (hx e)
    have hAM : G ∩ {ω | x ω = e} ∩ M = G ∩ {ω | x ω = e} :=
      inter_eq_left.2 (inter_subset_left.trans hGM)
    have h0 := hind _ hA (S e) (hS e)
    rw [hAM] at h0
    rw [h0, mul_comm]
    by_cases hne : (G ∩ {ω | x ω = e}).Nonempty
    · obtain ⟨ω, hg, hxe⟩ := hne
      have h1 := hε ω hg
      have hxe' : x ω = (e : E) := hxe
      rw [hxe'] at h1
      exact mul_le_mul' h1 le_rfl
    · rw [not_nonempty_iff_eq_empty.1 hne]; simp
  calc P (G ∩ {ω | Y ω ∈ S (x ω)})
      ≤ P (⋃ e : range x, (G ∩ {ω | x ω = e}) ∩ Y ⁻¹' S e) := measure_mono hU2
    _ ≤ ∑' e : range x, P ((G ∩ {ω | x ω = e}) ∩ Y ⁻¹' S e) := measure_iUnion_le _
    _ ≤ ∑' e : range x, ε * P (G ∩ {ω | x ω = e}) := ENNReal.tsum_le_tsum hterm
    _ = ε * ∑' e : range x, P (G ∩ {ω | x ω = e}) := ENNReal.tsum_mul_left
    _ = ε * P G := by
        congr 1
        conv_rhs => rw [hU]
        exact (measure_iUnion hdisj fun e => hGm.inter (hxm e)).symm

end freeze

section stopping

variable {d : ℕ} {β : ℝ} [Fact (0 < β)] (u : Fin d → ℤ) (q : ℝ) (Tn : ℝ≥0)
  {Ω : Type*} (𝒢₀ : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] {Pr : Measure Ω}
  {N : Ω → Measure (CycS Unit d β)}
  (hN : IsPoissonPointProcess N (cycIntensity Unit d β) Pr) (h𝒢 : 𝒢₀ ≤ mΩ)

/-- `ℱ⁺_Z ≤ ℱ_{t'_n + Z}`. -/
theorem step78_measurableSpace_le {Z : Ω → WithTop ℝ≥0}
    (hZ : IsStoppingTime (step78Filt u q Tn 𝒢₀ hN h𝒢) Z) {A : Set Ω}
    (hA : MeasurableSet[hZ.measurableSpace] A) :
    MeasurableSet[(step78_isStoppingTime_T u q Tn 𝒢₀ hN h𝒢 hZ).measurableSpace] A := by
  have hle : (⨆ t, (step78Filt u q Tn 𝒢₀ hN h𝒢) t) ≤
      ⨆ t, (cycMultiFilt (step78Plan d β u q Tn) 𝒢₀ hN.measurable h𝒢 Pr) t :=
    iSup_le fun t => le_iSup (fun t => (cycMultiFilt (step78Plan d β u q Tn) 𝒢₀ hN.measurable h𝒢
      Pr) t) (Tn + t)
  rw [IsStoppingTime.measurableSet] at hA ⊢
  obtain ⟨hA0, hA1⟩ := hA
  refine ⟨hle A hA0, fun s => ?_⟩
  by_cases hs : Tn ≤ s
  · have e : A ∩ {ω | step78T Tn Z ω ≤ (s : WithTop ℝ≥0)} =
        A ∩ {ω | Z ω ≤ ((s - Tn : ℝ≥0) : WithTop ℝ≥0)} := by
      ext ω
      simp only [mem_inter_iff, mem_ofPred_eq, step78T, and_congr_right_iff]
      intro _
      cases hz : Z ω with
      | top =>
        rw [WithTop.add_top]
        exact ⟨fun h => absurd h (WithTop.not_top_le_coe _),
          fun h => absurd h (WithTop.not_top_le_coe _)⟩
      | coe a =>
        rw [← WithTop.coe_add, WithTop.coe_le_coe, WithTop.coe_le_coe, le_tsub_iff_left hs]
    rw [e]
    have h := hA1 (s - Tn)
    exact (cycMultiFilt (step78Plan d β u q Tn) 𝒢₀ hN.measurable h𝒢 Pr).mono
      (le_of_eq (add_tsub_cancel_of_le hs)) _ h
  · have e : A ∩ {ω | step78T Tn Z ω ≤ (s : WithTop ℝ≥0)} = ∅ := by
      ext ω
      simp only [mem_inter_iff, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and, not_le]
      intro _
      refine lt_of_lt_of_le ?_ (le_add_of_nonneg_right bot_le)
      exact WithTop.coe_lt_coe.2 (not_le.1 hs)
    rw [e]
    exact @MeasurableSet.empty _ (cycMultiFilt (step78Plan d β u q Tn) 𝒢₀ hN.measurable h𝒢 Pr s)

end stopping

section visited

variable {d : ℕ}

/-- The values of a regular path on `[0, M]` form a finite set. -/
theorem step78_visited_finite {f : ℝ≥0 → Fin d → ℤ} (hf : IsRegPath f) (M : ℝ≥0) :
    (f '' Iic M).Finite := by
  classical
  set F : Set ℝ≥0 := {0} ∪ (CDisc f ∩ Iic M) with hF
  have hFfin : F.Finite := (Set.finite_singleton _).union (hf.fin M)
  refine (hFfin.image f).subset ?_
  rintro _ ⟨s, hs, rfl⟩
  -- the largest element of `F` below `s`
  have hne : (F ∩ Iic s).Nonempty := ⟨0, Or.inl rfl, mem_Iic.2 bot_le⟩
  have hfin : (F ∩ Iic s).Finite := hFfin.subset inter_subset_left
  set r : ℝ≥0 := hfin.toFinset.max' (by simpa using hne) with hr
  have hrmem : r ∈ F ∩ Iic s := by
    exact (Set.Finite.mem_toFinset hfin).1 (hfin.toFinset.max'_mem (by simpa using hne))
  have hrs : r ≤ s := hrmem.2
  refine ⟨r, hrmem.1, ?_⟩
  symm
  refine eq_of_no_disc hf.rc hrs (fun q hq hqd => ?_)
  have hqF : q ∈ F ∩ Iic s := ⟨Or.inr ⟨hqd, hq.2.trans hs⟩, hq.2⟩
  have : q ≤ r := hfin.toFinset.le_max' q (by simpa using hqF)
  exact absurd hq.1 (not_lt.2 this)

end visited

end ElboimSly.Paper.Step

end
