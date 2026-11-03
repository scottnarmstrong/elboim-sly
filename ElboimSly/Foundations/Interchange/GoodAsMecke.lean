/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Interchange.GoodAsBox
public import ElboimSly.Foundations.PPP.Mecke
public import Mathlib

/-!
# Ring paths and the factorial measure

Configurations are a.s. good (proof of (G3)).

A ring path along `v` in `[p, q]` gives a tuple of distinct atoms of `ν` in `pathBox v`; hence the
Mecke functional `meckePhi` of the box is at least `1`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace ElboimSly.Interchange

variable {d : ℕ} {β : ℝ} [Fact (0 < β)]

theorem measurableSet_pathBox {n : ℕ} (v : Fin (n + 1) → Fin d → ℤ) (a p q : ℝ) :
    MeasurableSet (pathBox β v a p q) :=
  ((measurableSet_edgeTuples v).preimage
    (measurable_pi_iff.2 fun i => (measurable_pi_apply i).fst)).inter
    ((measurableSet_circleSimplex a n p q).preimage
      (measurable_pi_iff.2 fun i => (measurable_pi_apply i).snd))

theorem one_le_meckePhi_pathBox {ν : Measure (RingSpace d β)}
    (hν : ν ∈ (ringSeq (Edge d) β).bSimple) {a p q : ℝ} (ha : a < p) (hq : q ≤ a + β)
    {n : ℕ} {v : Fin (n + 1) → Fin d → ℤ} {t : Fin n → ℝ}
    (hp : IsRingPath ν (Set.Icc p q) n v t) :
    1 ≤ meckePhi (ringSeq (Edge d) β) n ν (pathBox β v a p q) := by
  choose e he hr using hp.2.2
  have hbox : ∀ i, t i ∈ Set.Ioc a (a + β) := fun i =>
    ⟨ha.trans_le (hp.2.1 i).1, (hp.2.1 i).2.trans hq⟩
  have hrep : (fun i => circleRep β a ((t i : ℝ) : AddCircle β)) = t :=
    funext fun i => circleRep_coe (hbox i)
  set x : Fin n → RingSpace d β := fun i => (e i, ((t i : ℝ) : AddCircle β)) with hx
  have hxA : x ∈ pathBox β v a p q := by
    refine ⟨he, ?_⟩
    show orderedSimplex n p q (fun i => circleRep β a ((t i : ℝ) : AddCircle β))
    rw [hrep]
    exact ⟨hp.1, hp.2.1⟩
  have hxS : x ∈ {x : Fin n → RingSpace d β | (∀ i, x i ∈ SepPartSeq.atoms ν) ∧
      Function.Injective x} := by
    refine ⟨fun i => ?_, fun i j hij => ?_⟩
    · have h1 : 1 ≤ ν {(e i, ((t i : ℝ) : AddCircle β))} := hr i
      intro h0
      have : ν {x i} = 0 := h0
      rw [hx] at this
      simp only at this
      rw [this] at h1
      simp at h1
    · have h2 : ((t i : ℝ) : AddCircle β) = ((t j : ℝ) : AddCircle β) := congrArg Prod.snd hij
      have h3 := congrArg (circleRep β a) h2
      rw [circleRep_coe (hbox i), circleRep_coe (hbox j)] at h3
      exact hp.1.injective h3
  rw [meckePhi_of_mem n hν]
  calc (1 : ℝ≥0∞) = (Measure.count : Measure (Fin n → RingSpace d β)) ({x} ∩ _) := by
        rw [Set.inter_eq_left.2 (Set.singleton_subset_iff.2 hxS)]; simp
    _ ≤ factorialMeasure n ν {x} := Measure.le_restrict_apply _ _
    _ ≤ factorialMeasure n ν (pathBox β v a p q) := measure_mono (Set.singleton_subset_iff.2 hxA)

end ElboimSly.Interchange
