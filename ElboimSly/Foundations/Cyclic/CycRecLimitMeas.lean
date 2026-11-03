/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycRecLimit
public import ElboimSly.Foundations.Cyclic.CycRegionMeas
public import Mathlib

/-!
# Measurability of record functionals (e): measurability of the limit

Measurability of record functionals (e). For measurable `ρ_j : Θ → CycRec` with `ρ_{j+1}(ϑ)` extending
`ρ_j(ϑ)`, the set `Θ_0` is measurable and the limit record `Φ` is measurable.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

theorem measurable_lim_of_eventually {Θ : Type*} [MeasurableSpace Θ] {d : ℕ} {S : Set Θ}
    {g : ℕ → Θ → (Fin d → ℤ)} (hg : ∀ j, Measurable (g j)) (f : Θ → (Fin d → ℤ))
    (hev : ∀ ϑ ∈ S, ∀ᶠ j in atTop, g j ϑ = f ϑ) : Measurable (S.domRestrict f) := by
  refine measurable_of_tendsto_metrizable' atTop (f := fun j => S.domRestrict (g j))
    (fun j => (hg j).comp measurable_subtype_coe) ?_
  rw [tendsto_pi_nhds]
  intro ϑ
  exact tendsto_nhds_of_eventually_eq (hev ϑ ϑ.2)

variable {I : Type*} [MeasurableSpace I] [MeasurableSingletonClass I] [Countable I] {d : ℕ}
  {Θ : Type*} [MeasurableSpace Θ] {ρ : ℕ → Θ → CycRec I d} (hρ : ∀ j, Measurable (ρ j))
  (junk : CycEntry I d)

include hρ

omit [MeasurableSingletonClass I] [Countable I] in
theorem measurableSet_lt_num (j k : ℕ) : MeasurableSet {ϑ | (k : ℕ∞) < (ρ j ϑ).num} :=
  ((CycRec.measurable_num).comp (hρ j))
    (MeasurableSet.of_discrete (s := {x : ℕ∞ | (k : ℕ∞) < x}))

omit [MeasurableSingletonClass I] [Countable I] in
theorem measurableSet_lt_numLim (k : ℕ) : MeasurableSet {ϑ | (k : ℕ∞) < numLim ρ ϑ} := by
  have : {ϑ | (k : ℕ∞) < numLim ρ ϑ} = ⋃ j, {ϑ | (k : ℕ∞) < (ρ j ϑ).num} := by
    ext ϑ; simp [lt_numLim_iff]
  rw [this]
  exact MeasurableSet.iUnion fun j => measurableSet_lt_num hρ j k

omit [MeasurableSingletonClass I] [Countable I] in
theorem measurable_numLim : Measurable (numLim ρ) := by
  rw [ENat.measurable_iff]
  intro n
  have : numLim ρ ⁻¹' {(n : ℕ∞)} = {ϑ | ¬ (n : ℕ∞) < numLim ρ ϑ} ∩
      ⋂ m ∈ Finset.range n, {ϑ | (m : ℕ∞) < numLim ρ ϑ} := by
    ext ϑ
    simp only [mem_preimage, mem_singleton_iff, mem_inter_iff, mem_ofPred_eq, mem_iInter,
      Finset.mem_range]
    constructor
    · intro h
      refine ⟨by rw [h]; exact lt_irrefl _, fun m hm => ?_⟩
      rw [h]; exact_mod_cast hm
    · rintro ⟨h1, h2⟩
      cases hx : numLim ρ ϑ using ENat.recTopCoe with
      | top => exact absurd (by rw [hx]; exact ENat.natCast_lt_top n) h1
      | coe c =>
        rw [hx] at h1 h2
        have h3 : c ≤ n := by exact_mod_cast not_lt.mp h1
        have h4 : n ≤ c := by
          by_contra hh
          push Not at hh
          exact absurd (h2 c hh) (lt_irrefl _)
        simp [le_antisymm h3 h4]
  rw [this]
  exact (measurableSet_lt_numLim hρ n).compl.inter
    (Finset.measurableSet_biInter _ fun m _ => measurableSet_lt_numLim hρ m)

omit [MeasurableSingletonClass I] [Countable I] in
theorem measurable_firstStage (k : ℕ) : Measurable (firstStage ρ k) := by
  classical
  refine measurable_to_countable' fun n => ?_
  have : firstStage ρ k ⁻¹' {n} =
      ({ϑ | (k : ℕ∞) < numLim ρ ϑ} ∩ {ϑ | (k : ℕ∞) < (ρ n ϑ).num} ∩
        ⋂ m ∈ Finset.range n, {ϑ | (k : ℕ∞) < (ρ m ϑ).num}ᶜ) ∪
      ({ϑ | (k : ℕ∞) < numLim ρ ϑ}ᶜ ∩ {_ϑ | n = 0}) := by
    ext ϑ
    simp only [mem_preimage, mem_singleton_iff, mem_union, mem_inter_iff, mem_ofPred_eq,
      mem_iInter, Finset.mem_range, mem_compl_iff]
    unfold firstStage
    by_cases hex : ∃ j, (k : ℕ∞) < (ρ j ϑ).num
    · rw [dite_eq_left hex]
      have hk : (k : ℕ∞) < numLim ρ ϑ := lt_numLim_iff.mpr hex
      constructor
      · intro h
        left
        refine ⟨⟨hk, ?_⟩, fun m hm => ?_⟩
        · rw [← h]; exact Nat.find_spec hex
        · rw [← h] at hm; exact Nat.find_min hex hm
      · rintro (⟨⟨-, h2⟩, h3⟩ | ⟨h1, -⟩)
        · exact le_antisymm (Nat.find_min' hex h2)
            (by_contra fun hh => h3 _ (not_le.mp hh) (Nat.find_spec hex))
        · exact absurd hk h1
    · rw [dite_eq_right hex]
      have hk : ¬ (k : ℕ∞) < numLim ρ ϑ := fun h => hex (lt_numLim_iff.mp h)
      constructor
      · intro h; right; exact ⟨hk, h.symm⟩
      · rintro (⟨⟨h1, -⟩, -⟩ | ⟨-, h⟩)
        · exact absurd h1 hk
        · exact h.symm
  rw [this]
  refine MeasurableSet.union ?_ ?_
  · exact ((measurableSet_lt_numLim hρ k).inter (measurableSet_lt_num hρ n k)).inter
      (Finset.measurableSet_biInter _ fun m _ => (measurableSet_lt_num hρ m k).compl)
  · exact (measurableSet_lt_numLim hρ k).compl.inter (MeasurableSet.const _)

omit [MeasurableSingletonClass I] [Countable I] in
theorem measurable_stageEntry (k j : ℕ) : Measurable (stageEntry ρ junk k j) := by
  have hF : ∀ n, Measurable fun ϑ => (ρ (max j n) ϑ).coord junk k := fun n =>
    (CycRec.measurable_coord junk k).comp (hρ _)
  have : Measurable fun ϑ => (ρ (max j (firstStage ρ k ϑ)) ϑ).coord junk k := by
    have h2 : Measurable fun q : Θ × ℕ => (ρ (max j q.2) q.1).coord junk k :=
      measurable_from_prod_countable_left hF
    exact h2.comp (measurable_id.prodMk (measurable_firstStage hρ k))
  exact this

omit [MeasurableSingletonClass I] [Countable I] in
theorem measurable_stage_jt (k j a : ℕ) :
    Measurable fun ϑ => (stagePath ρ junk k ϑ j).jt a :=
  (CPath.measurable_jt a).comp (measurable_entry_path.comp (measurable_stageEntry hρ junk k j))

omit [MeasurableSingletonClass I] [Countable I] in
theorem measurable_tau (k a : ℕ) :
    Measurable fun ϑ => CPath.IsChain.tau (stagePath ρ junk k ϑ) a := by
  unfold CPath.IsChain.tau
  exact Measurable.iInf fun j => measurable_stage_jt hρ junk k j a

omit [MeasurableSingletonClass I] [Countable I] in
theorem measurableSet_limGood (k : ℕ) : MeasurableSet {ϑ | LimGood ρ junk k ϑ} := by
  have : {ϑ | LimGood ρ junk k ϑ} = ⋂ M : ℕ, ⋃ a : ℕ,
      {ϑ | (M : ℝ≥0∞) < CPath.IsChain.tau (stagePath ρ junk k ϑ) a} := by
    ext ϑ; simp [LimGood]
  rw [this]
  exact MeasurableSet.iInter fun M => MeasurableSet.iUnion fun a =>
    measurableSet_lt measurable_const (measurable_tau hρ junk k a)

omit [MeasurableSingletonClass I] [Countable I] in
theorem measurableSet_thetaZero : MeasurableSet (thetaZero ρ junk) := by
  have : thetaZero ρ junk = ⋂ k : ℕ, {ϑ | (k : ℕ∞) < numLim ρ ϑ}ᶜ ∪ {ϑ | LimGood ρ junk k ϑ} := by
    ext ϑ; simp [thetaZero, imp_iff_not_or]
  rw [this]
  exact MeasurableSet.iInter fun k => (measurableSet_lt_numLim hρ k).compl.union
    (measurableSet_limGood hρ junk k)

omit [MeasurableSingletonClass I] [Countable I] in
theorem measurable_limEntry (hext : ∀ j ϑ, (ρ j ϑ).Extends (ρ (j + 1) ϑ)) (k : ℕ) :
    Measurable (limEntry junk hext k) := by
  classical
  set S : Set Θ := {ϑ | (k : ℕ∞) < numLim ρ ϑ ∧ LimGood ρ junk k ϑ} with hS
  have hSm : MeasurableSet S := (measurableSet_lt_numLim hρ k).inter (measurableSet_limGood hρ junk k)
  refine measurable_of_restrict_of_restrict_compl hSm ?_ ?_
  swap
  · have : Sᶜ.domRestrict (limEntry junk hext k) = fun _ => junk := by
      funext ϑ
      show limEntry junk hext k ϑ.1 = junk
      unfold limEntry
      exact dite_eq_right ϑ.2
    rw [this]
    exact measurable_const
  · -- the pieces on `S`
    have hd : Measurable fun ϑ : S => (stageEntry ρ junk k 0 ϑ).data :=
      measurable_fst.comp ((measurable_stageEntry hρ junk k 0).comp measurable_subtype_coe)
    have hlen : Measurable fun ϑ : S =>
        (⨆ j, (stagePath ρ junk k ϑ j).len : ℝ≥0∞) := by
      refine Measurable.iSup fun j => ?_
      exact CPath.measurable_len.comp (measurable_entry_path.comp
        ((measurable_stageEntry hρ junk k j).comp measurable_subtype_coe))
    have hfn : ∀ r : ℝ≥0, Measurable fun ϑ : S =>
        CPath.IsChain.limFn (stagePath ρ junk k ϑ) r := by
      intro r
      refine measurable_lim_of_eventually (S := S)
        (g := fun j ϑ => (stagePath ρ junk k ϑ j).fn r)
        (fun j => (CPath.measurable_eval r).comp
          (measurable_entry_path.comp (measurable_stageEntry hρ junk k j)))
        (fun ϑ => CPath.IsChain.limFn (stagePath ρ junk k ϑ) r) ?_
      intro ϑ hϑ
      have hp := stagePath_isChain hext junk ϑ hϑ.1
      obtain ⟨J, hJ⟩ := hp.limFn_spec (LimGood.nnreal junk hϑ.2) r
      filter_upwards [eventually_ge_atTop J] with j hj
      exact (hJ j hj r le_rfl).symm
    have hlim : Measurable fun ϑ : S =>
        (stagePath_isChain hext junk ϑ.1 ϑ.2.1).limPath (LimGood.nnreal junk ϑ.2.2) := by
      refine (CPath.measurable_iff _).mpr ⟨?_, fun r => ?_⟩
      · exact hlen
      · exact hfn r
    have hfun : S.domRestrict (limEntry junk hext k) = fun ϑ : S =>
        ((stageEntry ρ junk k 0 ϑ).data,
          ⟨(stagePath_isChain hext junk ϑ.1 ϑ.2.1).limPath (LimGood.nnreal junk ϑ.2.2),
            unitJumps_limPath (stagePath_isChain hext junk ϑ.1 ϑ.2.1)
              (LimGood.nnreal junk ϑ.2.2) (fun j => (stageEntry ρ junk k j ϑ.1).2.2)⟩) := by
      funext ϑ
      show limEntry junk hext k ϑ.1 = _
      unfold limEntry
      exact dite_eq_left ϑ.2
    rw [hfun]
    exact hd.prodMk (Measurable.subtype_mk hlim)

omit hρ in
open scoped Classical in
omit [MeasurableSingletonClass I] [Countable I] [MeasurableSpace Θ] in
omit [MeasurableSpace I] in
theorem num_recLim (hext : ∀ j ϑ, (ρ j ϑ).Extends (ρ (j + 1) ϑ)) (ϑ : Θ) :
    (recLim junk hext ϑ).num = if ϑ ∈ thetaZero ρ junk then numLim ρ ϑ else 0 := by
  classical
  unfold recLim
  by_cases h : ϑ ∈ thetaZero ρ junk
  · rw [ite_eq_left h, ite_eq_left h]
    by_cases ht : numLim ρ ϑ = ⊤
    · rw [ite_eq_left ht, ht]; rfl
    · rw [ite_eq_right ht]
      simp [CycRec.num, ENat.natCast_toNat ht]
  · rw [ite_eq_right h, ite_eq_right h]
    rfl

omit hρ in
open scoped Classical in
omit [MeasurableSingletonClass I] [Countable I] [MeasurableSpace Θ] in
omit [MeasurableSpace I] in
theorem coord_recLim (hext : ∀ j ϑ, (ρ j ϑ).Extends (ρ (j + 1) ϑ)) (ϑ : Θ) (j : ℕ) :
    (recLim junk hext ϑ).coord junk j =
      if ϑ ∈ thetaZero ρ junk then limEntry junk hext j ϑ else junk := by
  classical
  unfold recLim
  by_cases h : ϑ ∈ thetaZero ρ junk
  · rw [ite_eq_left h, ite_eq_left h]
    by_cases ht : numLim ρ ϑ = ⊤
    · rw [ite_eq_left ht]
      simp [CycRec.coord, CycRec.nth]
    · rw [ite_eq_right ht]
      by_cases hj : j < (numLim ρ ϑ).toNat
      · simp [CycRec.coord, CycRec.nth, hj]
      · have hj' : ¬ (j : ℕ∞) < numLim ρ ϑ := by
          intro hh
          apply hj
          have := ENat.natCast_toNat ht
          rw [← this] at hh
          exact_mod_cast hh
        simp only [CycRec.coord, CycRec.nth, hj, dite_false, Option.getD_none]
        unfold limEntry
        rw [dite_eq_right (fun hh => hj' hh.1)]
  · rw [ite_eq_right h, ite_eq_right h]
    rfl

open scoped Classical in
omit [MeasurableSingletonClass I] [Countable I] in
/-- Measurability of record functionals (e): the limit of growing records is measurable. -/
theorem measurable_recLim (hext : ∀ j ϑ, (ρ j ϑ).Extends (ρ (j + 1) ϑ)) :
    Measurable (recLim junk hext) := by
  classical
  refine measurable_cycRec_of_coords _ junk ?_ fun j => ?_
  · have : (fun ϑ => (recLim junk hext ϑ).num) =
        fun ϑ => if ϑ ∈ thetaZero ρ junk then numLim ρ ϑ else 0 :=
      funext (num_recLim junk hext)
    rw [this]
    exact Measurable.ite (measurableSet_thetaZero hρ junk) (measurable_numLim hρ) measurable_const
  · have : (fun ϑ => (recLim junk hext ϑ).coord junk j) =
        fun ϑ => if ϑ ∈ thetaZero ρ junk then limEntry junk hext j ϑ else junk :=
      funext fun ϑ => coord_recLim junk hext ϑ j
    rw [this]
    exact Measurable.ite (measurableSet_thetaZero hρ junk) (measurable_limEntry hρ junk hext j)
      measurable_const

end ElboimSly.Cyclic

end
