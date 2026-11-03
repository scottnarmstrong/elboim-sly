/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import Mathlib

/-!
# Overriding finitely many coordinates of an infinite product

ES22 (8.3): base coupling with precision n^10; The coupling step of Lemma 7.6, re-tuned (the bookkeeping of the probability spaces).

If `W` has the law `⨂_i P i` and `Z` is independent of `W` with the law of the finite product of
the coordinates `P (j a)`, then replacing the coordinates `j a` of `W` by `Z a` leaves the law
`⨂_i P i` unchanged.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ElboimSly
namespace StrongApprox

/-- Replace the coordinates `j a` of `w` by `z a` (`j` injective). -/
noncomputable def overrideAt {ι X J : Type*} (j : J → ι) (z : J → X) (w : ι → X) : ι → X :=
  Function.extend j z w

theorem overrideAt_apply {ι X J : Type*} {j : J → ι} (hj : Function.Injective j) (z : J → X)
    (w : ι → X) (a : J) : overrideAt j z w (j a) = z a :=
  hj.extend_apply z w a

theorem overrideAt_apply_of_notMem {ι X J : Type*} {j : J → ι} (z : J → X) (w : ι → X) {i : ι}
    (hi : i ∉ Set.range j) : overrideAt j z w i = w i :=
  Function.extend_apply' z w i (by simpa using hi)

theorem measurable_overrideAt {ι X J : Type*} [MeasurableSpace X] [Fintype J]
    {j : J → ι} (hj : Function.Injective j) :
    Measurable fun p : (J → X) × (ι → X) => overrideAt j p.1 p.2 := by
  classical
  refine measurable_pi_iff.2 fun i => ?_
  by_cases hi : i ∈ Set.range j
  · obtain ⟨a, rfl⟩ := hi
    have : (fun p : (J → X) × (ι → X) => overrideAt j p.1 p.2 (j a)) = fun p => p.1 a := by
      funext p; exact overrideAt_apply hj _ _ a
    rw [this]
    exact (measurable_pi_apply a).comp measurable_fst
  · have : (fun p : (J → X) × (ι → X) => overrideAt j p.1 p.2 i) = fun p => p.2 i := by
      funext p; exact overrideAt_apply_of_notMem _ _ hi
    rw [this]
    exact (measurable_pi_apply i).comp measurable_snd

variable {ι X : Type*} [MeasurableSpace X]

/-- The override lemma: the law of the overridden vector is again the product law. -/
theorem map_overrideAt_eq_infinitePi (P : ι → Measure X) [∀ i, IsProbabilityMeasure (P i)]
    {J : Type*} [Fintype J] {j : J → ι} (hj : Function.Injective j)
    {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Z : Ω' → J → X} {W : Ω' → ι → X} (hZ : Measurable Z) (hW : Measurable W)
    (hind : IndepFun Z W P') (hZlaw : P'.map Z = Measure.pi fun a => P (j a))
    (hWlaw : P'.map W = Measure.infinitePi P) :
    P'.map (fun ω => overrideAt j (Z ω) (W ω)) = Measure.infinitePi P := by
  classical
  have hΘ : Measurable fun ω => overrideAt j (Z ω) (W ω) :=
    (measurable_overrideAt hj).comp (hZ.prodMk hW)
  refine Measure.eq_infinitePi _ fun s t ht => ?_
  rw [Measure.map_apply hΘ (MeasurableSet.pi s.countable_toSet fun i _ => ht i)]
  set sA : Finset J := Finset.univ.filter fun a => j a ∈ s with hsA
  set sR : Finset ι := s.filter fun i => i ∉ Set.range j with hsR
  have hset : (fun ω => overrideAt j (Z ω) (W ω)) ⁻¹' (Set.pi (↑s) t) =
      Z ⁻¹' (Set.pi (↑sA) fun a => t (j a)) ∩ W ⁻¹' (Set.pi (↑sR) t) := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_pi, Finset.mem_coe, Set.mem_inter_iff]
    constructor
    · intro h
      refine ⟨fun a ha => ?_, fun i hi => ?_⟩
      · have := h (j a) (by simpa [hsA] using ha)
        rwa [overrideAt_apply hj] at this
      · have hi' := Finset.mem_filter.1 hi
        have := h i hi'.1
        rwa [overrideAt_apply_of_notMem _ _ hi'.2] at this
    · rintro ⟨h1, h2⟩ i hi
      by_cases hri : i ∈ Set.range j
      · obtain ⟨a, rfl⟩ := hri
        rw [overrideAt_apply hj]
        exact h1 a (by simpa [hsA] using hi)
      · rw [overrideAt_apply_of_notMem _ _ hri]
        exact h2 i (Finset.mem_filter.2 ⟨hi, hri⟩)
  rw [hset]
  have hZm : MeasurableSet (Set.pi (↑sA) fun a => t (j a)) :=
    MeasurableSet.pi sA.countable_toSet fun a _ => ht _
  have hWm : MeasurableSet (Set.pi (↑sR) t) :=
    MeasurableSet.pi sR.countable_toSet fun i _ => ht i
  rw [hind.measure_inter_preimage_eq_mul _ _ hZm hWm]
  rw [← Measure.map_apply hZ hZm, ← Measure.map_apply hW hWm, hZlaw, hWlaw,
    Measure.infinitePi_pi P (fun i _ => ht i)]
  have hZpi : (Set.pi (↑sA) fun a => t (j a)) =
      Set.pi Set.univ (fun a => if a ∈ sA then t (j a) else Set.univ) := by
    ext z; simp only [Set.mem_pi, Finset.mem_coe, Set.mem_univ, true_implies]
    refine forall_congr' fun a => ?_
    by_cases h : a ∈ sA <;> simp [h]
  rw [hZpi, Measure.pi_pi]
  have h1 : ∏ a, (P (j a)) (if a ∈ sA then t (j a) else Set.univ) =
      ∏ a ∈ sA, P (j a) (t (j a)) := by
    rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun a => a ∈ sA)]
    have e1 : Finset.univ.filter (fun a => a ∈ sA) = sA := by ext; simp
    rw [e1]
    have e2 : ∏ a ∈ Finset.univ.filter (fun a => a ∉ sA), (P (j a)) (if a ∈ sA then t (j a)
        else Set.univ) = 1 := by
      refine Finset.prod_eq_one fun a ha => ?_
      rw [ite_eq_right (Finset.mem_filter.1 ha).2]; simp
    rw [e2, mul_one]
    exact Finset.prod_congr rfl fun a ha => by rw [ite_eq_left ha]
  rw [h1]
  have h2 : ∏ a ∈ sA, P (j a) (t (j a)) = ∏ i ∈ s.filter (fun i => i ∈ Set.range j), P i (t i) := by
    have : s.filter (fun i => i ∈ Set.range j) = sA.image j := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_image, Set.mem_range, hsA, Finset.mem_univ,
        true_and]
      constructor
      · rintro ⟨hi, a, rfl⟩; exact ⟨a, hi, rfl⟩
      · rintro ⟨a, ha, rfl⟩; exact ⟨ha, a, rfl⟩
    rw [this, Finset.prod_image (fun a _ b _ h => hj h)]
  rw [h2]
  exact Finset.prod_filter_mul_prod_filter_not s (fun i => i ∈ Set.range j) (f := fun i => P i (t i))

end StrongApprox
end ElboimSly
