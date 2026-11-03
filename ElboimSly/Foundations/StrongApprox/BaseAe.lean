/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.StrongApprox.BaseWalk
public import ElboimSly.Foundations.SRW.GoodAe
public import Mathlib

/-!
# Almost sure facts on the base coupling space

ES22 (8.3): base coupling with precision n^10 ("The walk": almost surely all `Y_{k,i}` lie in `S_k`, and
`K_k = ξ^v_l`; hence `N'(S_k) = K_k`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ElboimSly
namespace StrongApprox

open SRW

theorem ae_infinitePi_of_ae {ι X : Type*} [Countable ι] [MeasurableSpace X]
    (μ : ι → Measure X) [∀ i, IsProbabilityMeasure (μ i)] (p : ι → X → Prop)
    (h : ∀ i, ∀ᵐ x ∂μ i, p i x) : ∀ᵐ x ∂Measure.infinitePi μ, ∀ i, p i (x i) :=
  ae_all_iff.2 fun i => (measurePreserving_eval_infinitePi (μ := μ) i).quasiMeasurePreserving.ae
    (h i)

theorem ae_cellLaw {d : ℕ} (k : CellIdx d) (hk : 1 ≤ k.2) :
    ∀ᵐ y ∂cellLaw d k, y ∈ cellSet d k := by
  rw [ae_iff]
  unfold cellLaw cellSet
  simp only [hk, ite_true]
  have hc : {a : Dir d × ℝ | ¬ a ∈ (({k.1} : Set (Dir d)) ×ˢ Ioc ((k.2 : ℝ) - 1) k.2)} =
      (({k.1} : Set (Dir d)) ×ˢ Ioc ((k.2 : ℝ) - 1) k.2)ᶜ := rfl
  rw [hc, Set.compl_prod_eq_union]
  refine measure_union_null ?_ ?_
  · rw [show ({k.1}ᶜ : Set (Dir d)) ×ˢ (univ : Set ℝ) = ({k.1}ᶜ : Set (Dir d)) ×ˢ univ from rfl,
      Measure.prod_prod]
    simp [Measure.dirac_apply' _ (measurableSet_singleton k.1).compl]
  · rw [Measure.prod_prod]
    simp [Measure.restrict_apply measurableSet_Ioc.compl]

variable {d N : ℕ} {μN : Measure ((Fin N → ℝ) × (Fin N → ℝ))} [IsProbabilityMeasure μN]

/-- Almost surely all the points `Y_{k,i}`, `k ∈ 𝒦_N`, lie in their cells. -/
theorem ae_Y_mem :
    ∀ᵐ ω ∂PMain d N μN, ∀ (a : JIdx d N) (i : ℕ), ω.1.2 a i ∈ cellSet d (jcell d N a) := by
  have h1 : ∀ᵐ y ∂PBpts d N, ∀ (a : JIdx d N) (i : ℕ), y a i ∈ cellSet d (jcell d N a) := by
    unfold PBpts
    rw [← Measure.infinitePi_eq_pi]
    refine ae_infinitePi_of_ae _ (fun a (z : ℕ → Dir d × ℝ) => ∀ i, z i ∈ cellSet d (jcell d N a)) fun a => ?_
    have hk : 1 ≤ (jcell d N a).2 := by simp [jcell]
    refine ae_infinitePi_of_ae _ (fun _ z => z ∈ cellSet d (jcell d N a)) fun i => ?_
    exact ae_cellLaw _ hk
  have hmp : MeasurePreserving (fun ω : OmMain d N => ω.1.2) (PMain d N μN) (PBpts d N) :=
    measurePreserving_snd.comp measurePreserving_fst
  exact hmp.quasiMeasurePreserving.ae h1

theorem measurable_xiOf : Measurable (xiOf d N) := measurable_pi_iff.2 fun p =>
  (measurable_pi_apply p.2).comp (measurable_fst.comp (measurable_pi_apply p.1))

theorem law_xiOf
    (hμ1 : μN.map Prod.fst = Measure.pi fun _ : Fin N => (poissonMeasure 1).map (Nat.cast : ℕ → ℝ)) :
    (PA d N μN).map (xiOf d N) =
      Measure.pi fun _ : JIdx d N => (poissonMeasure 1).map (Nat.cast : ℕ → ℝ) :=
  law_flatten μN (f := fun x => x.1) measurable_fst _ hμ1

/-- Almost surely `ξ^v_l = K_{(v,l)}` as real numbers. -/
theorem ae_xi_eq_kap
    (hμ1 : μN.map Prod.fst = Measure.pi fun _ : Fin N => (poissonMeasure 1).map (Nat.cast : ℕ → ℝ)) :
    ∀ᵐ a ∂PA d N μN, ∀ p, xiOf d N a p = (kapOf d N a p : ℝ) := by
  have hm : MeasurableSet {x : ℝ | ∃ n : ℕ, x = n} := by
    have : {x : ℝ | ∃ n : ℕ, x = n} = Set.range (Nat.cast : ℕ → ℝ) := by
      ext x; simp [eq_comm]
    rw [this]; exact (Set.countable_range _).measurableSet
  have h : ∀ᵐ x ∂(PA d N μN).map (xiOf d N), ∀ p, ∃ n : ℕ, x p = (n : ℝ) := by
    rw [law_xiOf hμ1, ← Measure.infinitePi_eq_pi]
    refine ae_infinitePi_of_ae _ (fun _ (x : ℝ) => ∃ n : ℕ, x = (n : ℝ)) fun p => ?_
    rw [ae_map_iff Measurable.of_discrete.aemeasurable hm]
    exact ae_of_all _ fun n => ⟨n, rfl⟩
  filter_upwards [ae_of_ae_map (measurable_xiOf (d := d) (N := N)).aemeasurable h] with a ha p
  obtain ⟨n, hn⟩ := ha p
  simp [kapOf, xiOf] at hn ⊢
  rw [hn]; simp

end StrongApprox
end ElboimSly
