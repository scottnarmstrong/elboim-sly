/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Heavy.GoodLocalLoc
public import ElboimSly.Foundations.Cyclic.CycEvents
public import ElboimSly.Foundations.Cyclic.CycMergeMeas
public import ElboimSly.Foundations.Cyclic.CycJoint
public import ElboimSly.Paper.Induction.RelaxedMeasWrt

/-!
# Measurability of goodness of a block

Goodness is local; independence at distance (a) (ES22 §6).

The set of good configurations `ν` for which the block `ℬ_k(ι)` is good is measurable.  The
conditions (GB1)-(GB3) are measurable functions of the finitely many walks `W^ν_{u,q}`: closing and
`Ω` are events, the relaxed-time measure is measured by Tonelli on the jointly measurable set of
relaxed times, and the supremum in (GB2) and the existential quantifier in (GB3) are countable
(rational times and the endpoint) by right-local constancy of the walks.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Heavy

open ElboimSly ElboimSly.Paper ElboimSly.Cyclic

variable {d : ℕ} {β : ℝ} [Fact (0 < β)]

theorem cycWalk_rlc' {ν : Measure (RingSpace d β)} (hν : Good ν) (u : Fin d → ℤ) (q : ℝ) {r : ℝ}
    (hr : 0 ≤ r) : ∃ ε > 0, ∀ s ∈ Ico r (r + ε), cycWalk ν u q s = cycWalk ν u q r := by
  obtain ⟨b, hb, hsub⟩ := mem_nhdsGE_iff_exists_Ico_subset.1 (cycWalk_rightCont hν u q hr)
  exact ⟨b - r, by simpa using hb, fun s hs => hsub ⟨hs.1, by linarith [hs.2]⟩⟩

/-- A good configuration viewed through the clamped walk `s ↦ W(max s 0)`. -/
noncomputable def clampWalk (u : Fin d → ℤ) (q : ℝ) (ν : GoodSet d β) (s : ℝ) : Fin d → ℤ :=
  cycWalk ν.1 u q (max s 0)

theorem measurable_clampWalk (u : Fin d → ℤ) (q : ℝ) :
    Measurable fun p : GoodSet d β × ℝ => clampWalk u q p.1 p.2 := by
  have := (measurable_cycWalk_joint (β := β) u).comp
    (measurable_fst.prodMk (measurable_const.prodMk (measurable_snd.max measurable_const)) :
      Measurable fun p : GoodSet d β × ℝ => (p.1, q, max p.2 0))
  exact this

theorem clampWalk_rlc (u : Fin d → ℤ) (q : ℝ) (ν : GoodSet d β) (s : ℝ) :
    ∃ ε > 0, ∀ s' ∈ Ico s (s + ε), clampWalk u q ν s' = clampWalk u q ν s := by
  by_cases hs : 0 ≤ s
  · obtain ⟨ε, hε, h⟩ := cycWalk_rlc' ν.2 u q (r := s) hs
    refine ⟨ε, hε, fun s' hs' => ?_⟩
    have h0 : 0 ≤ s' := hs.trans hs'.1
    simp only [clampWalk, max_eq_left h0, max_eq_left hs]
    exact h s' hs'
  · push Not at hs
    refine ⟨-s, by linarith, fun s' hs' => ?_⟩
    simp only [clampWalk, max_eq_right hs.le, max_eq_right (by linarith [hs'.2] : s' ≤ 0)]

theorem measurableSet_closes (u : Fin d → ℤ) (q tk : ℝ) :
    MeasurableSet {ν : GoodSet d β | cycClosesBy ν.1 u q tk} := by
  have := (measurableSet_cycClosesBy (d := d) (β := β) u q tk).preimage
    (measurable_subtype_coe : Measurable fun ν : GoodSet d β => ν.1)
  convert this using 1
  ext ν
  simp [ν.2]

theorem measurableSet_omega (u₁ u₂ : Fin d → ℤ) (q₁ q₂ tk : ℝ) :
    MeasurableSet {ν : GoodSet d β | cycOmega ν.1 u₁ u₂ q₁ q₂ tk} := by
  have := (measurableSet_cycOmega (d := d) (β := β) u₁ u₂ q₁ q₂ tk).preimage
    (measurable_subtype_coe : Measurable fun ν : GoodSet d β => ν.1)
  convert this using 1
  ext ν
  simp [ν.2]

theorem measurable_relaxedVolume (u : Fin d → ℤ) (q tk : ℝ) :
    Measurable fun ν : GoodSet d β =>
      volume {s : ℝ | s ∈ Icc 0 tk ∧ IsRelaxedTimeWrt β (fun r => cycWalk ν.1 u q r) 0 s} := by
  have hR := measurableSet_isRelaxedTimeWrt (β := β) (d := d) (Ω := GoodSet d β)
    (fun ν s => clampWalk u q ν s) (fun _ _ => 0) (measurable_clampWalk u q) measurable_const
    (fun ν s => clampWalk_rlc u q ν s)
  have hS : MeasurableSet {p : GoodSet d β × ℝ | p.2 ∈ Icc 0 tk ∧
      IsRelaxedTimeWrt β (clampWalk u q p.1) 0 p.2} :=
    (measurable_snd measurableSet_Icc).inter hR
  have := measurable_measure_prodMk_left (ν := (volume : Measure ℝ)) hS
  convert this using 2 with ν
  congr 1
  ext s
  simp only [mem_ofPred_eq, mem_preimage]
  have hβ : 0 < β := Fact.out
  refine and_congr_right fun hs => ?_
  exact isRelaxedTimeWrt_congr_Icc hβ hs.1 fun r hr => by
    simp [clampWalk, max_eq_left hr.1]

theorem measurableSet_imp_const {α : Type*} [MeasurableSpace α] (p : Prop) {S : Set α}
    (hS : p → MeasurableSet S) : MeasurableSet {x : α | p → x ∈ S} := by
  by_cases hp : p
  · simpa [hp] using hS hp
  · simp [hp]

theorem measurableSet_gb2 (u : Fin d → ℤ) (q tk R : ℝ) :
    MeasurableSet {ν : GoodSet d β | ∀ s ∈ Icc (0 : ℝ) tk, ‖cycWalk ν.1 u q s - u‖ ≤ R} := by
  by_cases htk : 0 ≤ tk
  · have key : ∀ ν : GoodSet d β, (∃ s ∈ Icc (0 : ℝ) tk, R < ‖cycWalk ν.1 u q s - u‖) ↔
        (∃ r : ℚ, (r : ℝ) ∈ Ico 0 tk ∧ R < ‖cycWalk ν.1 u q r - u‖) ∨
          R < ‖cycWalk ν.1 u q tk - u‖ := fun ν =>
      exists_Icc_iff_rational htk (P := fun s => R < ‖cycWalk ν.1 u q s - u‖)
        (fun s hs hP => by
          obtain ⟨ε, hε, h⟩ := cycWalk_rlc' ν.2 u q hs.1
          exact ⟨ε, hε, fun s' hs' => by rw [h s' hs']; exact hP⟩)
    have hm : ∀ s : ℝ, 0 ≤ s → MeasurableSet {ν : GoodSet d β | R < ‖cycWalk ν.1 u q s - u‖} :=
      fun s hs => measurableSet_lt measurable_const
        ((measurable_of_countable (fun v : Fin d → ℤ => ‖v - u‖)).comp (measurable_cycWalk u q hs))
    have e : {ν : GoodSet d β | ∀ s ∈ Icc (0 : ℝ) tk, ‖cycWalk ν.1 u q s - u‖ ≤ R} =
        ((⋃ r : ℚ, {ν : GoodSet d β | (r : ℝ) ∈ Ico 0 tk ∧ R < ‖cycWalk ν.1 u q r - u‖}) ∪
          {ν : GoodSet d β | R < ‖cycWalk ν.1 u q tk - u‖})ᶜ := by
      ext ν
      simp only [mem_ofPred_eq, mem_compl_iff, mem_union, mem_iUnion]
      rw [← key ν]
      push Not
      exact Iff.rfl
    rw [e]
    refine (MeasurableSet.union (MeasurableSet.iUnion fun r => ?_) (hm tk htk)).compl
    exact measurableSet_and_of (α := GoodSet d β) ((r : ℝ) ∈ Ico 0 tk) fun h => hm r h.1
  · have : {ν : GoodSet d β | ∀ s ∈ Icc (0 : ℝ) tk, ‖cycWalk ν.1 u q s - u‖ ≤ R} = univ := by
      ext ν
      simp only [mem_ofPred_eq, mem_univ, iff_true]
      intro s hs
      exact absurd (hs.1.trans hs.2) htk
    rw [this]; exact MeasurableSet.univ

theorem measurableSet_prox (u₁ u₂ : Fin d → ℤ) (q₁ q₂ tk ρ : ℝ) :
    MeasurableSet {p : GoodSet d β × ℝ | p.2 ∈ Icc 0 tk ∧ ∃ s₁ ∈ Icc (0 : ℝ) tk,
      ‖cycWalk p.1.1 u₁ q₁ s₁ - cycWalk p.1.1 u₂ q₂ p.2‖ ≤ ρ} := by
  by_cases htk : 0 ≤ tk
  · have hf₂ : Measurable fun p : GoodSet d β × ℝ => cycWalk p.1.1 u₂ q₂ p.2 :=
      (measurable_cycWalk_joint (β := β) u₂).comp
        (measurable_fst.prodMk (measurable_const.prodMk measurable_snd))
    have hnorm : Measurable fun v : (Fin d → ℤ) × (Fin d → ℤ) => ‖v.1 - v.2‖ :=
      measurable_of_countable _
    have hm : ∀ s : ℝ, 0 ≤ s → MeasurableSet {p : GoodSet d β × ℝ |
        ‖cycWalk p.1.1 u₁ q₁ s - cycWalk p.1.1 u₂ q₂ p.2‖ ≤ ρ} := by
      intro s hs
      have h1 : Measurable fun p : GoodSet d β × ℝ => cycWalk p.1.1 u₁ q₁ s :=
        (measurable_cycWalk u₁ q₁ hs).comp measurable_fst
      have h2 := hnorm.comp (h1.prodMk hf₂)
      exact measurableSet_le h2 measurable_const
    have e : {p : GoodSet d β × ℝ | p.2 ∈ Icc 0 tk ∧ ∃ s₁ ∈ Icc (0 : ℝ) tk,
        ‖cycWalk p.1.1 u₁ q₁ s₁ - cycWalk p.1.1 u₂ q₂ p.2‖ ≤ ρ} =
        {p : GoodSet d β × ℝ | p.2 ∈ Icc 0 tk} ∩
          ((⋃ r : ℚ, {p : GoodSet d β × ℝ | (r : ℝ) ∈ Ico 0 tk ∧
              ‖cycWalk p.1.1 u₁ q₁ r - cycWalk p.1.1 u₂ q₂ p.2‖ ≤ ρ}) ∪
            {p : GoodSet d β × ℝ | ‖cycWalk p.1.1 u₁ q₁ tk - cycWalk p.1.1 u₂ q₂ p.2‖ ≤ ρ}) := by
      ext p
      simp only [mem_ofPred_eq, mem_inter_iff, mem_union, mem_iUnion]
      refine and_congr Iff.rfl ?_
      exact exists_Icc_iff_rational htk
        (P := fun s => ‖cycWalk p.1.1 u₁ q₁ s - cycWalk p.1.1 u₂ q₂ p.2‖ ≤ ρ) (fun s hs hP => by
          obtain ⟨ε, hε, h⟩ := cycWalk_rlc' p.1.2 u₁ q₁ hs.1
          exact ⟨ε, hε, fun s' hs' => by rw [h s' hs']; exact hP⟩)
    rw [e]
    refine (measurable_snd measurableSet_Icc).inter (MeasurableSet.union
      (MeasurableSet.iUnion fun r => ?_) (hm tk htk))
    exact measurableSet_and_of (α := GoodSet d β × ℝ) ((r : ℝ) ∈ Ico 0 tk) fun h => hm r h.1
  · have : {p : GoodSet d β × ℝ | p.2 ∈ Icc 0 tk ∧ ∃ s₁ ∈ Icc (0 : ℝ) tk,
        ‖cycWalk p.1.1 u₁ q₁ s₁ - cycWalk p.1.1 u₂ q₂ p.2‖ ≤ ρ} = ∅ := by
      ext p
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
      intro h
      exact absurd (h.1.trans h.2) htk
    rw [this]; exact MeasurableSet.empty

theorem measurable_proxVolume (u₁ u₂ : Fin d → ℤ) (q₁ q₂ tk ρ : ℝ) :
    Measurable fun ν : GoodSet d β =>
      volume {s₂ : ℝ | s₂ ∈ Icc 0 tk ∧ ∃ s₁ ∈ Icc (0 : ℝ) tk,
        ‖cycWalk ν.1 u₁ q₁ s₁ - cycWalk ν.1 u₂ q₂ s₂‖ ≤ ρ} :=
  measurable_measure_prodMk_left (ν := (volume : Measure ℝ)) (measurableSet_prox u₁ u₂ q₁ q₂ tk ρ)

/-- Goodness is local; independence at distance (a), on the good configurations. -/
theorem measurableSet_heavyBlockGood (t₀ : ℝ) (n : ℕ) (ι : Fin d → ℤ) :
    MeasurableSet {ν : GoodSet d β | HeavyBlockGood d β t₀ n ν.1 ι} := by
  set k := heavyLevel d n with hk
  set tk := heavyTkPrime d t₀ n with htk
  set U := latNbhd (heavyBlock k ι) ((2 : ℝ) ^ (k + 2)) with hU
  have e : {ν : GoodSet d β | HeavyBlockGood d β t₀ n ν.1 ι} =
      ⋂ u₁ : Fin d → ℤ, ⋂ u₂ : Fin d → ℤ, ⋂ q₁ : ℤ, ⋂ q₂ : ℤ,
        {ν : GoodSet d β | (u₁ ∈ U ∧ u₂ ∈ U ∧ (0 : ℝ) ≤ q₁ ∧ (q₁ : ℝ) ≤ β ∧ (0 : ℝ) ≤ q₂ ∧
            (q₂ : ℝ) ≤ β) →
          ((cycClosesBy ν.1 u₁ q₁ tk ∨
            ENNReal.ofReal ((9 / 10 + 1 / (heavyLevelPrime d t₀ n : ℝ)) * tk) ≤
              volume {s : ℝ | s ∈ Icc 0 tk ∧
                IsRelaxedTimeWrt β (fun r => cycWalk ν.1 u₁ q₁ r) 0 s}) ∧
          (∀ s ∈ Icc (0 : ℝ) tk, ‖cycWalk ν.1 u₁ q₁ s - u₁‖ ≤ (2 : ℝ) ^ (k - 1)) ∧
          (cycOmega ν.1 u₁ u₂ q₁ q₂ tk →
            volume {s₂ : ℝ | s₂ ∈ Icc 0 tk ∧ ∃ s₁ ∈ Icc (0 : ℝ) tk,
              ‖cycWalk ν.1 u₁ q₁ s₁ - cycWalk ν.1 u₂ q₂ s₂‖ ≤ (1.9 : ℝ) ^ k} <
              ENNReal.ofReal ((3.9 : ℝ) ^ k)))} := by
    ext ν
    simp only [mem_ofPred_eq, mem_iInter, HeavyBlockGood]
    constructor
    · intro h u₁ u₂ q₁ q₂ ⟨a, b, c, d', e', f⟩
      exact h u₁ a u₂ b q₁ q₂ c d' e' f
    · intro h u₁ hu₁ u₂ hu₂ q₁ q₂ c d' e' f
      exact h u₁ u₂ q₁ q₂ ⟨hu₁, hu₂, c, d', e', f⟩
  rw [e]
  refine MeasurableSet.iInter fun u₁ => MeasurableSet.iInter fun u₂ =>
    MeasurableSet.iInter fun q₁ => MeasurableSet.iInter fun q₂ => ?_
  refine measurableSet_imp_const _ fun _ => ?_
  refine ((measurableSet_closes u₁ q₁ tk).union
    (measurableSet_le measurable_const (measurable_relaxedVolume u₁ q₁ tk))).inter
    ((measurableSet_gb2 u₁ q₁ tk _).inter ?_)
  exact (measurableSet_omega u₁ u₂ q₁ q₂ tk).imp
    (measurableSet_lt (measurable_proxVolume u₁ u₂ q₁ q₂ tk _) measurable_const)

/-- Goodness is local; independence at distance (a): the set of good `ν` for which the block is good is
measurable. -/
theorem measurableSet_good_and_heavyBlockGood (t₀ : ℝ) (n : ℕ) (ι : Fin d → ℤ) :
    MeasurableSet {ν : Measure (RingSpace d β) | Good ν ∧ HeavyBlockGood d β t₀ n ν ι} :=
  measurableSet_good_and (P := fun ν => HeavyBlockGood d β t₀ n ν ι)
    (measurableSet_heavyBlockGood t₀ n ι)

/-- The set of configurations for which the block is bad is measurable. -/
theorem measurableSet_heavyBlockBad (t₀ : ℝ) (n : ℕ) (ι : Fin d → ℤ) :
    MeasurableSet {ν : Measure (RingSpace d β) | HeavyBlockBad d β t₀ n ν ι} := by
  have : {ν : Measure (RingSpace d β) | HeavyBlockBad d β t₀ n ν ι} =
      {ν | Good ν} \ {ν | Good ν ∧ HeavyBlockGood d β t₀ n ν ι} := by
    ext ν
    simp only [HeavyBlockBad, mem_ofPred_eq, Set.mem_sdiff]
    tauto
  rw [this]
  exact measurableSet_good.diff (measurableSet_good_and_heavyBlockGood t₀ n ι)

end ElboimSly.Paper.Heavy
