/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.PPP.Indep
public import ElboimSly.Foundations.PPP.Operations
public import Mathlib

/-!
# Independence of restrictions

Restriction (b), (c).

`IsPoissonPointProcess.iIndepFun_restrict`: the restrictions of a Poisson point process to
pairwise disjoint measurable sets are independent random measures.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ElboimSly

variable {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]

namespace IsPoissonPointProcess

variable {N : Ω → Measure S} {μ : Measure S} {P : Measure Ω}

/-- The key computation, for finitely many sets and count events. -/
theorem measure_inter_count_events {κ : Type*} [Fintype κ] (h : IsPoissonPointProcess N μ P)
    {A : κ → Set S} (hA : ∀ k, MeasurableSet (A k)) (hd : Pairwise (Function.onFun Disjoint A))
    (l : κ → ℕ) (B : ∀ k, Fin (l k) → Set S) (hB : ∀ k i, MeasurableSet (B k i))
    (C : ∀ k, Set (Fin (l k) → ℝ≥0∞)) (hC : ∀ k, MeasurableSet (C k)) :
    P (⋂ k, {ω | (fun i => (N ω).restrict (A k) (B k i)) ∈ C k}) =
      ∏ k, P {ω | (fun i => (N ω).restrict (A k) (B k i)) ∈ C k} := by
  classical
  have hP := h.isProbabilityMeasure
  let a : (Σ k, (Fin (l k) → Bool)) → Set S := fun p => atom (B p.1) p.2 ∩ A p.1
  have ha : ∀ p, MeasurableSet (a p) := fun p =>
    (measurableSet_atom (hB p.1) p.2).inter (hA p.1)
  have had : Pairwise (Function.onFun Disjoint a) := by
    rintro ⟨k, ε⟩ ⟨k', ε'⟩ hne
    by_cases hk : k = k'
    · subst hk
      have : ε ≠ ε' := fun e => hne (by rw [e])
      exact ((pairwise_disjoint_atom (B k) this).mono Set.inter_subset_left
        Set.inter_subset_left)
    · exact (hd hk).mono Set.inter_subset_right Set.inter_subset_right
  let Z : (Σ k, (Fin (l k) → Bool)) → Ω → ℝ≥0∞ := fun p ω => N ω (a p)
  have hZm : ∀ p, Measurable (Z p) := fun p => h.measurable_count (ha p)
  have hZi : iIndepFun Z P := by
    rw [iIndepFun_iff_map_fun_eq_pi_map (fun p => (hZm p).aemeasurable)]
    rw [h.map_counts_fintype ha had]
    congr 1
    funext p
    exact (h.map_count (ha p)).symm
  -- blocks
  let J : κ → Set (Σ k, (Fin (l k) → Bool)) := fun k => {p | p.1 = k}
  have hJ : Pairwise (Function.onFun Disjoint J) := by
    intro k k' hne
    refine Set.disjoint_left.2 fun p hp hp' => hne ?_
    exact hp.symm.trans hp'
  let M : κ → MeasurableSpace Ω := fun k =>
    ⨆ p ∈ J k, MeasurableSpace.comap (Z p) inferInstance
  have hblocks := iIndepFun_blocks hZm hZi J hJ
    (Y := fun k ω => (fun i => (N ω).restrict (A k) (B k i)))
    (𝓨 := fun k => Fin (l k) → ℝ≥0∞) ?_
  · have := (iIndepFun_iff_measure_inter_preimage_eq_mul.1 hblocks Finset.univ
      (sets := fun k => C k) (fun k _ => hC k))
    simpa [Set.preimage] using this
  · intro k
    have hcoord : ∀ ε : Fin (l k) → Bool, Measurable[M k] (Z ⟨k, ε⟩) := by
      intro ε
      refine Measurable.mono (comap_measurable (Z ⟨k, ε⟩)) ?_ le_rfl
      exact le_iSup₂_of_le (⟨k, ε⟩ : Σ k, (Fin (l k) → Bool)) rfl le_rfl
    have hvec : Measurable[M k] fun ω (ε : Fin (l k) → Bool) => Z ⟨k, ε⟩ ω :=
      by let : MeasurableSpace Ω := M k; exact Measurable.of_eval hcoord
    have hfun : (fun ω => (fun i => (N ω).restrict (A k) (B k i))) =
        sumMap (l k) ∘ fun ω (ε : Fin (l k) → Bool) => Z ⟨k, ε⟩ ω := by
      ext ω i
      exact measure_eq_sum_atom (hB k) ((N ω).restrict (A k)) i |>.trans (by
        refine Finset.sum_congr rfl fun ε _ => ?_
        simp only [Z, a]
        rw [Measure.restrict_apply (measurableSet_atom (hB k) ε)])
    rw [hfun]
    exact (measurable_sumMap (l k)).comp hvec

/-- Restriction (b): restrictions to pairwise disjoint measurable sets are
independent random measures. -/
theorem iIndepFun_restrict (h : IsPoissonPointProcess N μ P) {κ : Type*} {A : κ → Set S}
    (hA : ∀ k, MeasurableSet (A k)) (hd : Pairwise (Function.onFun Disjoint A)) :
    iIndepFun (fun k ω => (N ω).restrict (A k)) P := by
  classical
  have hP := h.isProbabilityMeasure
  have hmeas : ∀ k, Measurable fun ω => (N ω).restrict (A k) := fun k =>
    (measurable_restrict_measure (hA k)).comp h.measurable
  rw [iIndepFun_iff_iIndep _ _ _]
  refine iIndep_of_pi_systems (fun k => (hmeas k).comap_le)
    (fun k => {t | ∃ u ∈ countEvents S, (fun ω => (N ω).restrict (A k)) ⁻¹' u = t})
    (fun k => isPiSystem_countEvents.comap _) (fun k => ?_) ?_
  · rw [← generateFrom_countEvents, MeasurableSpace.comap_generateFrom]
    rfl
  · intro J f hf
    choose! F hF hfe using hf
    have hF' : ∀ k ∈ J, ∃ (l : ℕ) (B : Fin l → Set S) (C : Set (Fin l → ℝ≥0∞)),
        (∀ i, MeasurableSet (B i)) ∧ MeasurableSet C ∧ F k = {ν | (fun i => ν (B i)) ∈ C} :=
      fun k hk => hF k hk
    choose! l B C hB hC hFe using hF'
    have hfk : ∀ k ∈ J, f k = {ω | (fun i => (N ω).restrict (A k) (B k i)) ∈ C k} := by
      intro k hk
      rw [← hfe k hk, hFe k hk]
      rfl
    have key := h.measure_inter_count_events (κ := J) (A := fun k => A k) (fun k => hA k)
      (fun i j hij => hd (fun e => hij (Subtype.ext e))) (fun k => l k) (fun k => B k)
      (fun k i => hB k k.2 i) (fun k => C k) (fun k => hC k k.2)
    have e1 : (⋂ k ∈ J, f k) = ⋂ k : J, {ω | (fun i => (N ω).restrict (A k) (B k i)) ∈ C k} := by
      ext ω
      simp only [Set.mem_iInter]
      constructor
      · intro hω k
        rw [← hfk k k.2]; exact hω k k.2
      · intro hω k hk
        rw [hfk k hk]; exact hω ⟨k, hk⟩
    rw [e1, key, ← Finset.prod_coe_sort J (fun k => P (f k))]
    exact Finset.prod_congr rfl fun k _ => by rw [hfk k k.2]

/-- Restriction (b), two-set form. -/
theorem indepFun_restrict (h : IsPoissonPointProcess N μ P) {A B : Set S}
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hd : Disjoint A B) :
    IndepFun (fun ω => (N ω).restrict A) (fun ω => (N ω).restrict B) P := by
  have hi := h.iIndepFun_restrict (A := fun b : Bool => if b then A else B)
    (fun b => by cases b <;> simp [hA, hB])
    (by
      intro b b' hbb'
      cases b <;> cases b' <;> simp_all [Function.onFun, hd.symm])
  simpa using hi.indepFun (i := true) (j := false) (by simp)

end IsPoissonPointProcess

end ElboimSly
