/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycSchemeDef
public import ElboimSly.Foundations.Cyclic.CycSchemeInst
public import ElboimSly.Foundations.Cyclic.CycPiece
public import ElboimSly.Foundations.Cyclic.CycRingMeasure
public import ElboimSly.Foundations.Cyclic.CycFirstEvents
public import Mathlib

/-!
# The environment scheme (b): the front of the current walk

The environment scheme (b), (i)--(ii). Facts about `h_fr` (`CycScheme.hFr`) at *front
points* `(ι, e, c_δ(r + t))`:

* `hFr_le_of_front`: a known ring at the front at time `t ∈ (0, β]` forces `h_fr ≤ t`;
* `hFr_attained`: when the clock values of the rings are finite (finite records), the infimum
  `h_fr` is either `∞` or attained by a known ring at the front (the "inf is attained" guard of
  The environment scheme of a plan);
* `hFr_pos`: `h_fr > 0` for such records.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ElboimSly.Circle
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

namespace CycScheme

variable {I : Type*} [MeasurableSpace I] {d : ℕ} {β : ℝ} [Fact (0 < β)]

/-- The front point of `(ι, e)` at parameter `t`: `(ι, e, c_δ(r + t))`. -/
noncomputable def frontPt (β : ℝ) [Fact (0 < β)] (E : CycEntry I d) (e : Edge d) (t : ℝ≥0) :
    I × RingSpace d β :=
  (E.data.copy, (e, E.data.clock β (E.time + t)))

omit [MeasurableSpace I] in
theorem circS_frontPt (E : CycEntry I d) (e : Edge d) {t : ℝ≥0} (ht : (t : ℝ) ∈ Ioc 0 β) :
    circS E.frontT E.frontS (E.data.copy, e) (frontPt β E e t).2.2 = t := by
  have h1 : (frontPt β E e t).2.2 =
      (circX E.frontT E.frontS (E.data.copy, e) (t : ℝ) : AddCircle β) :=
    (CycEntry.circX_front E (E.data.copy, e) t).symm
  rw [h1]
  exact circS_circX E.frontT E.frontS (E.frontS_cases) _ ht

omit [MeasurableSpace I] in
theorem circS_mem_Ioc (E : CycEntry I d) (e : I × Edge d) (y : AddCircle β) :
    circS E.frontT E.frontS e y ∈ Ioc 0 β := by
  unfold circS
  split_ifs
  · exact rep_mem _
  · exact rep_mem _

omit [MeasurableSpace I] in
theorem circS_front_indep (E : CycEntry I d) (e e' : I × Edge d) (y : AddCircle β) :
    circS E.frontT E.frontS e y = circS E.frontT E.frontS e' y := by
  unfold circS CycEntry.frontT CycEntry.frontS
  rfl

omit [MeasurableSpace I] in
theorem hFr_le_of_ring (ρ : CycRec I d) (E : CycEntry I d) {x : I × RingSpace d β}
    (hx : x ∈ ρ.ringSet β) (h1 : x.1 = E.data.copy) (h2 : Edge.Mem E.pos x.2.1) :
    hFr β ρ E ≤ ENNReal.ofReal (circS E.frontT E.frontS (x.1, x.2.1) x.2.2) := by
  classical
  unfold hFr
  refine (iInf₂_le x hx).trans ?_
  rw [ite_eq_left ⟨h1, h2⟩]

omit [MeasurableSpace I] in
theorem hFr_le_of_front (ρ : CycRec I d) (E : CycEntry I d) {e : Edge d} {t : ℝ≥0}
    (ht : (t : ℝ) ∈ Ioc 0 β) (he : Edge.Mem E.pos e)
    (hx : frontPt β E e t ∈ ρ.ringSet β) : hFr β ρ E ≤ (t : ℝ≥0∞) := by
  have := hFr_le_of_ring ρ E hx rfl he
  have h2 : circS E.frontT E.frontS ((frontPt β E e t).1, (frontPt β E e t).2.1)
      (frontPt β E e t).2.2 = t := circS_frontPt E e ht
  rw [h2] at this
  simpa using this

omit [MeasurableSpace I] in
theorem hFr_attained (ρ : CycRec I d) (E : CycEntry I d)
    (hfin : {θ : AddCircle β | ∃ x ∈ ρ.ringSet β, x.2.2 = θ}.Finite) :
    hFr β ρ E = ⊤ ∨ ∃ x ∈ ρ.ringSet β, x.1 = E.data.copy ∧ Edge.Mem E.pos x.2.1 ∧
      hFr β ρ E = ENNReal.ofReal (circS E.frontT E.frontS (x.1, x.2.1) x.2.2) := by
  classical
  set T : Set (I × RingSpace d β) :=
    {x | x ∈ ρ.ringSet β ∧ x.1 = E.data.copy ∧ Edge.Mem E.pos x.2.1} with hT
  by_cases hne : T.Nonempty
  · right
    obtain ⟨x1, hx1⟩ := hne
    set g : AddCircle β → ℝ≥0∞ := fun θ =>
      ENNReal.ofReal (circS E.frontT E.frontS (E.data.copy, x1.2.1) θ) with hg
    have hfinT : ((fun x : I × RingSpace d β => x.2.2) '' T).Finite :=
      hfin.subset (by rintro _ ⟨x, hx, rfl⟩; exact ⟨x, hx.1, rfl⟩)
    obtain ⟨θ0, ⟨x0, hx0, rfl⟩, hmin⟩ := Set.exists_min_image _ g hfinT ⟨x1.2.2, x1, hx1, rfl⟩
    have hval : ∀ x : I × RingSpace d β, ENNReal.ofReal
        (circS E.frontT E.frontS (x.1, x.2.1) x.2.2) = g x.2.2 := fun x => by
      simp only [hg]
      rw [circS_front_indep E (x.1, x.2.1) (E.data.copy, x1.2.1)]
    refine ⟨x0, hx0.1, hx0.2.1, hx0.2.2, ?_⟩
    rw [hval]
    refine le_antisymm ?_ ?_
    · have := hFr_le_of_ring ρ E hx0.1 hx0.2.1 hx0.2.2
      rwa [hval] at this
    · unfold hFr
      refine le_iInf₂ fun x hx => ?_
      by_cases hc : x.1 = E.data.copy ∧ Edge.Mem E.pos x.2.1
      · rw [ite_eq_left hc, hval]; exact hmin _ ⟨x, ⟨hx, hc⟩, rfl⟩
      · rw [ite_eq_right hc]; exact le_top
  · left
    unfold hFr
    refine top_unique (le_iInf₂ fun x hx => ?_)
    rw [ite_eq_right]
    rintro ⟨h1, h2⟩
    exact hne ⟨x, hx, h1, h2⟩

end CycScheme

end ElboimSly.Cyclic

end
