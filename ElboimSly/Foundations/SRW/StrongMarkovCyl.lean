/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.SRW.StrongMarkov
public import Mathlib

/-!
# Strong Markov property on cylinder sets

Strong Markov property (cylinder step).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

namespace ElboimSly
namespace SRW

variable {d : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {Z : Ω → PathSpace d}
  {F : ℝ≥0 → MeasurableSpace Ω} {T : Ω → WithTop ℝ≥0}

theorem IsSRW.strong_markov_cylinder (hZ : IsSRW P Z) (hF : IsAdmissible P Z F)
    (hT : IsStoppingTime hF.filtration T) {A : Set Ω} (hA : MeasurableSet[hT.measurableSpace] A)
    (I : Finset ℝ≥0) {S : Set (∀ i : I, (fun _ : ℝ≥0 => Fin d → ℤ) i)} (hS : MeasurableSet S) :
    P (A ∩ {ω | T ω < ⊤} ∩ {ω | thetaAt T Z ω ∈ cylinder I S}) =
      P (A ∩ {ω | T ω < ⊤}) * P.map Z (cylinder I S) := by
  have := hZ.isProbabilityMeasure
  have hcyl : MeasurableSet (cylinder I S) := MeasurableSet.cylinder (α := fun _ : ℝ≥0 => Fin d → ℤ) I hS
  have hAm : MeasurableSet A := hT.measurableSpace_le A hA
  have hTtop : MeasurableSet {ω | T ω < ⊤} := by
    have : {ω | T ω < ⊤} = {ω | T ω = ⊤}ᶜ := by
      ext ω; simp [lt_top_iff_ne_top]
    rw [this]; exact hT.measurableSet_top.compl
  let Dm : ℕ → Set Ω := fun m => ⋃ k, gset A T m k ∩ {ω | theta (dt m k) (Z ω) ∈ cylinder I S}
  have hgm : ∀ m k, MeasurableSet (gset A T m k) := fun m k =>
    hF.filtration.le _ _ (measurableSet_gset hT hA m k)
  have hthm : ∀ t, MeasurableSet {ω | theta t (Z ω) ∈ cylinder I S} := fun t =>
    ((measurable_theta t).comp hZ.1) hcyl
  have hDm : ∀ m, MeasurableSet (Dm m) := fun m =>
    MeasurableSet.iUnion fun k => (hgm m k).inter (hthm _)
  have hPD : ∀ m, P (Dm m) = P (A ∩ {ω | T ω < ⊤}) * P.map Z (cylinder I S) := by
    intro m
    have hdis : Pairwise (Function.onFun Disjoint fun k =>
        gset A T m k ∩ {ω | theta (dt m k) (Z ω) ∈ cylinder I S}) := fun a b hab =>
      (pairwise_disjoint_gset A T m hab).mono inter_subset_left inter_subset_left
    rw [measure_iUnion hdis fun k => (hgm m k).inter (hthm _)]
    have : ∀ k, P (gset A T m k ∩ {ω | theta (dt m k) (Z ω) ∈ cylinder I S}) =
        P (gset A T m k) * P.map Z (cylinder I S) := fun k =>
      hZ.fixed_time hF (dt m k) (measurableSet_gset hT hA m k) hcyl
    simp_rw [this]
    rw [ENNReal.tsum_mul_right, ← measure_iUnion (pairwise_disjoint_gset A T m) (hgm m),
      iUnion_gset]
  have hE : MeasurableSet (A ∩ {ω | T ω < ⊤} ∩ {ω | thetaAt T Z ω ∈ cylinder I S}) :=
    (hAm.inter hTtop).inter
      ((measurable_thetaAt hT (fun s => (measurable_pi_apply s).comp hZ.1) hZ.2.1) hcyl)
  have hlim := tendsto_measure_of_tendsto_indicator_of_isFiniteMeasure (L := atTop) P hDm
    (A := A ∩ {ω | T ω < ⊤} ∩ {ω | thetaAt T Z ω ∈ cylinder I S}) ?_
  · have hconst : Tendsto (fun m => P (Dm m)) atTop
        (𝓝 (P (A ∩ {ω | T ω < ⊤}) * P.map Z (cylinder I S))) := by
      simp_rw [hPD]; exact tendsto_const_nhds
    exact (tendsto_nhds_unique hlim hconst)
  · intro ω
    by_cases hω : ω ∈ A ∩ {ω | T ω < ⊤}
    · have hk : ∀ m, ∃ k, ω ∈ gset A T m k := fun m => by
        have : ω ∈ ⋃ k, gset A T m k := by rw [iUnion_gset]; exact hω
        simpa using this
      choose k hk using hk
      have hb := fun m => gset_bounds (hk m)
      have hTne : T ω ≠ ⊤ := (hb 0).2.1
      obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.1 hTne
      have hsr : stopReal T ω = r := by unfold stopReal; rw [← hr]; rfl
      have hDiff : ∀ m, ω ∈ Dm m ↔ theta (dt m (k m)) (Z ω) ∈ cylinder I S := by
        intro m
        simp only [Dm, mem_iUnion, mem_inter_iff, mem_ofPred_eq]
        constructor
        · rintro ⟨k', hk', h'⟩
          have : k' = k m := by
            by_contra hne
            exact Set.disjoint_left.1 (pairwise_disjoint_gset A T m hne) hk' (hk m)
          rwa [this] at h'
        · intro h; exact ⟨k m, hk m, h⟩
      have hEiff : ω ∈ A ∩ {ω | T ω < ⊤} ∩ {ω | thetaAt T Z ω ∈ cylinder I S} ↔
          theta r (Z ω) ∈ cylinder I S := by
        simp only [mem_inter_iff, mem_ofPred_eq]
        unfold thetaAt
        rw [ite_eq_right hTne, hsr]
        exact ⟨fun h => h.2, fun h => ⟨hω, h⟩⟩
      have hreg := hZ.2.1 ω
      have hs1 : ∀ m, r ≤ dt m (k m) := fun m => by have := (hb m).2.2.1; rwa [hsr] at this
      have hs2 : ∀ m, dt m (k m) ≤ r + 1 / 2 ^ m := fun m => by
        have := (hb m).2.2.2; rwa [hsr] at this
      have hev : ∀ᶠ m in atTop, ∀ i ∈ I, Z ω (dt m (k m) + i) = Z ω (r + i) := by
        rw [Filter.eventually_all_finset]
        intro i _
        refine hreg.eventually_near (s := fun m => dt m (k m) + i) (fun m => ?_) (fun m => ?_)
        · gcongr; exact hs1 m
        · calc dt m (k m) + i ≤ (r + 1 / 2 ^ m) + i := by gcongr; exact hs2 m
            _ = r + i + 1 / 2 ^ m := by ring
      have hev0 : ∀ᶠ m in atTop, Z ω (dt m (k m)) = Z ω r :=
        hreg.eventually_near (s := fun m => dt m (k m)) hs1 hs2
      filter_upwards [hev, hev0] with m hm hm0
      rw [hDiff m, hEiff, mem_cylinder, mem_cylinder]
      have : I.restrict (theta (dt m (k m)) (Z ω)) = I.restrict (theta r (Z ω)) := by
        funext i
        simp only [Finset.restrict, theta]
        rw [hm i i.2, hm0]
      rw [this]
    · refine Filter.Eventually.of_forall fun m => ?_
      have h1 : ω ∉ Dm m := fun h => by
        obtain ⟨k, hk⟩ := mem_iUnion.1 h
        apply hω
        rw [← iUnion_gset A T m]
        exact mem_iUnion.2 ⟨k, hk.1⟩
      have h2 : ω ∉ A ∩ {ω | T ω < ⊤} ∩ {ω | thetaAt T Z ω ∈ cylinder I S} := fun h => hω h.1
      exact iff_of_false h1 h2

end SRW
end ElboimSly
