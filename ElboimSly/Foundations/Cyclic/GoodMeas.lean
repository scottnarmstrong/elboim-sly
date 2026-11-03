/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.GreedyMeas
public import ElboimSly.Foundations.Interchange.RingSplit
public import ElboimSly.Foundations.Interchange.SymmDef
import Mathlib

/-!
# `Good` is a measurable set of configurations

Measurability, Step 0 (`Good ∈ 𝔊(S_β)`).

`Good = PreGood ∩ (G3)`, and (G3) is a countable Boolean combination of the greedy events of
`GreedyMeas`. Paths *ending* at `y` are reduced to paths starting at `y` by the reflection
`ϱ_*`.
-/

@[expose] public section

open MeasureTheory Set ElboimSly.Interchange
open scoped ENNReal

namespace ElboimSly.Cyclic

variable {d : ℕ} {β : ℝ} [Fact (0 < β)] {ν : Measure (RingSpace d β)}

omit [Fact (0 < β)] in
theorem nice_reflectMeasure (hν : Nice ν) : Nice (reflectMeasure β ν) := by
  refine ⟨fun B hB h => ?_, fun e => ?_⟩
  · unfold reflectMeasure at h ⊢
    rw [ringPush_apply] at h
    obtain ⟨x, hx, h1⟩ := hν.1 _ ((ringMapEquiv _ _).measurable hB) h
    refine ⟨ringMapEquiv (Equiv.refl _) (MeasurableEquiv.neg (AddCircle β)) x, hx, ?_⟩
    obtain ⟨e, θ⟩ := x
    rw [ringMapEquiv_apply, ringPush_singleton]
    simpa using h1
  · have hF := hν.2 e
    refine (hF.preimage (MeasurableEquiv.neg (AddCircle β)).symm.injective.injOn).subset ?_
    intro θ hθ
    exact (mem_ringSet_ringPush (Equiv.refl _) (MeasurableEquiv.neg (AddCircle β)) ν e θ).mp hθ

omit [Fact (0 < β)] in
theorem measurable_reflectMeasure : Measurable (reflectMeasure (d := d) β) :=
  Measure.measurable_map _ (ringMapEquiv _ _).measurable

omit [Fact (0 < β)] in
theorem rings_reflect_reflect (ν : Measure (RingSpace d β)) (e : Edge d) (t : ℝ) :
    Rings (reflectMeasure β (reflectMeasure β ν)) e t ↔ Rings ν e t := by
  rw [rings_reflectMeasure, rings_reflectMeasure, neg_neg]

omit [Fact (0 < β)] in
theorem noPathTo_congr {μ μ' : Measure (RingSpace d β)} (h : ∀ e t, Rings μ e t ↔ Rings μ' e t)
    (J : Set ℝ) (y : Fin d → ℤ) (n : ℕ) : NoPathTo μ J y n ↔ NoPathTo μ' J y n := by
  unfold NoPathTo NRingPath
  simp only [h]

omit [Fact (0 < β)] in
theorem noPathTo_iff_reflect (ν : Measure (RingSpace d β)) (j : ℤ) (y : Fin d → ℤ) (n : ℕ) :
    NoPathTo ν (ringWindow β j) y n ↔
      NoPathFrom (reflectMeasure β ν) (ringWindow β (-j - 2)) y n := by
  constructor
  · intro h
    refine noPathFrom_reflect (J := ringWindow β (-j - 2)) ?_
    have := neg_ringWindow (β := β) (-j - 2)
    rw [show -(-j - 2) - 2 = j by ring] at this
    rw [this]; exact h
  · intro h
    have h2 : NoPathFrom (reflectMeasure β ν) {u | -u ∈ ringWindow β j} y n := by
      rw [neg_ringWindow]; exact h
    exact (noPathTo_congr (rings_reflect_reflect ν) _ y n).mp (noPathTo_reflect h2)

theorem exists_noPathTo_set (_lo _hi : ℝ) (j : ℤ) (y : Fin d → ℤ) (n : ℕ) :
    ∃ U : Set (Measure (RingSpace d β)), MeasurableSet U ∧
      ∀ ν, Nice ν → (NoPathTo ν (ringWindow β j) y n ↔ ν ∈ U) := by
  obtain ⟨U, hU, hUi⟩ := exists_noPathFrom_set (β := β) (d := d)
    ((-j - 2 : ℤ) * β / 4) ((-j - 2 : ℤ) * β / 4 + β / 2) y n
  refine ⟨reflectMeasure β ⁻¹' U, measurable_reflectMeasure hU, fun ν hν => ?_⟩
  rw [noPathTo_iff_reflect, Set.mem_preimage, ← hUi _ (nice_reflectMeasure hν)]
  rfl

theorem exists_noPathFrom_window (j : ℤ) (y : Fin d → ℤ) (n : ℕ) :
    ∃ U : Set (Measure (RingSpace d β)), MeasurableSet U ∧
      ∀ ν, Nice ν → (NoPathFrom ν (ringWindow β j) y n ↔ ν ∈ U) :=
  exists_noPathFrom_set (j * β / 4) (j * β / 4 + β / 2) y n

/-- On `PreGood`, `Good` is exactly (G3). -/
theorem good_iff_of_preGood (hν : ν ∈ PreGood d β) :
    Good ν ↔ ∀ (y : Fin d → ℤ) (j : ℤ), ∃ n : ℕ,
      NoPathFrom ν (ringWindow β j) y n ∧ NoPathTo ν (ringWindow β j) y n := by
  constructor
  · intro h y j
    obtain ⟨n, h1, h2⟩ := h.2.2.2 y j
    exact ⟨n, noPathFrom_iff.mpr h1, noPathTo_iff.mpr h2⟩
  · intro h
    obtain ⟨hs, hg1, hinj⟩ := hν
    have hc := SepPartSeq.structure_of_mem_bSimple hs
    refine ⟨?_, hg1, ⟨fun e θ => SepPartSeq.singleton_le_one hs (e, θ), ?_⟩, fun y j => ?_⟩
    · intro A hA
      rw [hc.2.2.2 A hA]
      generalize (A ∩ SepPartSeq.atoms ν).encard = k
      induction k using ENat.recTopCoe with
      | top => left; simp
      | coe n => right; exact ⟨n, by simp⟩
    · intro e f hef
      refine Set.disjoint_left.mpr fun θ h1 h2 => hef ?_
      have a1 : (e, θ) ∈ SepPartSeq.atoms ν := by
        intro h0; have : (1 : ℝ≥0∞) ≤ 0 := h1.trans_eq h0
        simp at this
      have a2 : (f, θ) ∈ SepPartSeq.atoms ν := by
        intro h0; have : (1 : ℝ≥0∞) ≤ 0 := h2.trans_eq h0
        simp at this
      exact congrArg Prod.fst (hinj a1 a2 rfl)
    · obtain ⟨n, h1, h2⟩ := h y j
      exact ⟨n, noPathFrom_iff.mp h1, noPathTo_iff.mp h2⟩

/-- Measurability, `Good ∈ 𝔊(S_β)`. -/
theorem measurableSet_good : MeasurableSet {ν : Measure (RingSpace d β) | Good ν} := by
  have h1 : ∀ (y : Fin d → ℤ) (j : ℤ) (n : ℕ), ∃ U : Set (Measure (RingSpace d β)),
      MeasurableSet U ∧ ∀ ν, Nice ν → (NoPathFrom ν (ringWindow β j) y n ↔ ν ∈ U) :=
    fun y j n => exists_noPathFrom_window j y n
  have h2 : ∀ (y : Fin d → ℤ) (j : ℤ) (n : ℕ), ∃ U : Set (Measure (RingSpace d β)),
      MeasurableSet U ∧ ∀ ν, Nice ν → (NoPathTo ν (ringWindow β j) y n ↔ ν ∈ U) :=
    fun y j n => exists_noPathTo_set 0 0 j y n
  choose U1 hU1 hU1i using h1
  choose U2 hU2 hU2i using h2
  have : {ν : Measure (RingSpace d β) | Good ν} =
      PreGood d β ∩ ⋂ y : Fin d → ℤ, ⋂ j : ℤ, ⋃ n : ℕ, (U1 y j n ∩ U2 y j n) := by
    ext ν
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter, Set.mem_iUnion]
    constructor
    · intro h
      have hp := good_preGood h
      refine ⟨hp, fun y j => ?_⟩
      obtain ⟨n, a, b⟩ := (good_iff_of_preGood hp).mp h y j
      exact ⟨n, (hU1i y j n ν (good_nice h)).mp a, (hU2i y j n ν (good_nice h)).mp b⟩
    · rintro ⟨hp, h⟩
      refine (good_iff_of_preGood hp).mpr fun y j => ?_
      obtain ⟨n, a, b⟩ := h y j
      exact ⟨n, (hU1i y j n ν (preGood_nice hp)).mpr a, (hU2i y j n ν (preGood_nice hp)).mpr b⟩
  rw [this]
  exact measurableSet_preGood.inter (MeasurableSet.iInter fun y => MeasurableSet.iInter fun j =>
    MeasurableSet.iUnion fun n => (hU1 y j n).inter (hU2 y j n))

end ElboimSly.Cyclic

end
