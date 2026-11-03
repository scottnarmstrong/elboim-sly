/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.PPP.Existence
public import ElboimSly.Foundations.PPP.ExistenceExamples
public import Mathlib

/-!
# A Poisson point process from cell blocks on any probability space

A Poisson point process from cell blocks on any probability space.

Given a countably infinite measurable partition `(Q k)` of `S`, cell laws `ν k` and masses `lam k`
with `(lam k • ν k)|_{Q k} = μ|_{Q k}`, any family of blocks `(K k, (Y k i)_i)` on a probability space
whose joint law is `⨂_k (Po(lam k) ⊗ ν k^{⊗ℕ})` yields the Poisson point process
`ω ↦ ∑_k (∑_{i<K k ω} δ_{Y k i ω})|_{Q k}` with intensity `μ`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace ElboimSly
namespace StrongApprox

variable {S : Type*} [MeasurableSpace S]

/-- The counting measure of the block `(K k, (Y k i)_i)`, restricted to the cell `Q k`, summed over
`k`: the formula `N'` of the written proof. -/
noncomputable def cellProc {𝒦 Ω' : Type*} (Q : 𝒦 → Set S) (K : 𝒦 → Ω' → ℕ)
    (Y : 𝒦 → ℕ → Ω' → S) (ω : Ω') : Measure S :=
  Measure.sum fun k => (blockProc (K k ω, fun i => Y k i ω)).restrict (Q k)

/-- Existence on the standard space, for a partition indexed by `ℕ`. -/
theorem isPoissonPointProcess_nat_blocks (μ : Measure S) (Q : ℕ → Set S)
    (hQm : ∀ k, MeasurableSet (Q k)) (hQd : Pairwise (Function.onFun Disjoint Q))
    (hQu : ⋃ k, Q k = Set.univ) (ν : ℕ → Measure S) [∀ k, IsProbabilityMeasure (ν k)]
    (lam : ℕ → ℝ≥0) (hν : ∀ k, ((lam k : ℝ≥0∞) • ν k).restrict (Q k) = μ.restrict (Q k)) :
    IsPoissonPointProcess (fun ω : ∀ _ : ℕ, ℕ × (ℕ → S) =>
      Measure.sum fun k => (blockProc (ω k)).restrict (Q k)) μ
      (Measure.infinitePi fun k => blockMeasure (ν k) (lam k)) := by
  set P := Measure.infinitePi fun k => blockMeasure (ν k) (lam k) with hP
  have hG : ∀ k, Measurable fun p : ℕ × (ℕ → S) => (blockProc p).restrict (Q k) :=
    fun k => (measurable_restrict_measure (hQm k)).comp measurable_blockProc
  have hk : ∀ k, IsPoissonPointProcess (fun ω : ∀ _ : ℕ, ℕ × (ℕ → S) => (blockProc (ω k)).restrict
      (Q k)) (μ.restrict (Q k)) P := by
    intro k
    have h1 := (isPoissonPointProcess_blockProc (ν k) (lam k)).restrict (hQm k)
    rw [hν k] at h1
    refine h1.of_map_eq ((hG k).comp (measurable_pi_apply k)) ?_
    have e : (fun ω : ∀ _ : ℕ, ℕ × (ℕ → S) => (blockProc (ω k)).restrict (Q k)) =
        (fun p : ℕ × (ℕ → S) => (blockProc p).restrict (Q k)) ∘ fun ω => ω k := rfl
    rw [e, ← Measure.map_map (hG k) (measurable_pi_apply k), hP,
      Measure.infinitePi_map_eval]
  have hi : iIndepFun (fun (k : ℕ) (ω : ∀ _ : ℕ, ℕ × (ℕ → S)) =>
      (blockProc (ω k)).restrict (Q k)) P :=
    iIndepFun_infinitePi (X := fun k p => (blockProc p).restrict (Q k)) hG
  have := IsPoissonPointProcess.sum hk hi
  have hμ : Measure.sum (fun k => μ.restrict (Q k)) = μ := by
    rw [← Measure.restrict_iUnion hQd hQm, hQu, Measure.restrict_univ]
  rwa [hμ] at this

/-- A Poisson point process from cell blocks on any probability space: a Poisson point process from cell blocks on any
probability space. -/
theorem isPoissonPointProcess_cellProc (μ : Measure S) {𝒦 : Type*} [Countable 𝒦] [Infinite 𝒦]
    (Q : 𝒦 → Set S) (hQm : ∀ k, MeasurableSet (Q k)) (hQd : Pairwise (Function.onFun Disjoint Q))
    (hQu : ⋃ k, Q k = Set.univ) (ν : 𝒦 → Measure S) [∀ k, IsProbabilityMeasure (ν k)]
    (lam : 𝒦 → ℝ≥0) (hν : ∀ k, ((lam k : ℝ≥0∞) • ν k).restrict (Q k) = μ.restrict (Q k))
    {Ω' : Type*} [MeasurableSpace Ω'] (P' : Measure Ω') (K : 𝒦 → Ω' → ℕ)
    (Y : 𝒦 → ℕ → Ω' → S) (hK : ∀ k, Measurable (K k)) (hY : ∀ k i, Measurable (Y k i))
    (hlaw : P'.map (fun ω k => (K k ω, fun i => Y k i ω)) =
      Measure.infinitePi fun k => blockMeasure (ν k) (lam k)) :
    IsPoissonPointProcess (cellProc Q K Y) μ P' := by
  obtain ⟨e⟩ : Nonempty (ℕ ≃ 𝒦) := nonempty_equiv_of_countable
  have hQ0 := isPoissonPointProcess_nat_blocks μ (fun n => Q (e n)) (fun n => hQm _)
    (fun a b hab => hQd (e.injective.ne hab))
    (by rw [← hQu]; exact e.surjective.iUnion_comp (fun k => Q k))
    (fun n => ν (e n)) (fun n => lam (e n)) (fun n => hν _)
  set F : Ω' → ∀ k : 𝒦, ℕ × (ℕ → S) := fun ω k => (K k ω, fun i => Y k i ω) with hF
  have hFm : Measurable F := measurable_pi_iff.2 fun k =>
    (hK k).prodMk (measurable_pi_iff.2 fun i => hY k i)
  set X : 𝒦 → Type _ := fun _ => ℕ × (ℕ → S)
  set Θ : Ω' → ∀ _ : ℕ, ℕ × (ℕ → S) := fun ω n => F ω (e n) with hΘ
  have hΘm : Measurable Θ := measurable_pi_iff.2 fun n => (measurable_pi_apply _).comp hFm
  have hΘlaw : P'.map Θ = Measure.infinitePi fun n => blockMeasure (ν (e n)) (lam (e n)) := by
    have h1 := Measure.infinitePi_map_piCongrLeft (X := X)
      (fun k => blockMeasure (ν k) (lam k)) e
    have hΘ' : Θ = (MeasurableEquiv.piCongrLeft X e).symm ∘ F := by
      funext ω n
      simp [Θ, X, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft_symm_apply]
    rw [hΘ', ← Measure.map_map (MeasurableEquiv.measurable _) hFm, hlaw, ← h1]
    rw [Measure.map_map (MeasurableEquiv.measurable _) (MeasurableEquiv.measurable _)]
    simp
  have heq : cellProc Q K Y = fun ω => Measure.sum fun n =>
      (blockProc (Θ ω n)).restrict (Q (e n)) := by
    funext ω
    refine Measure.ext fun s hs => ?_
    simp only [cellProc, Measure.sum_apply _ hs]
    exact (e.tsum_eq fun k => ((blockProc (K k ω, fun i => Y k i ω)).restrict (Q k)) s).symm
  rw [heq]
  refine hQ0.of_map_eq ?_ ?_
  · exact (measurable_measure_sum fun n =>
      (measurable_restrict_measure (hQm _)).comp
        (measurable_blockProc.comp ((measurable_pi_apply n).comp hΘm)))
  · rw [← hΘlaw, Measure.map_map]
    · rfl
    · exact measurable_measure_sum fun n =>
        (measurable_restrict_measure (hQm _)).comp
          (measurable_blockProc.comp (measurable_pi_apply n))
    · exact hΘm

end StrongApprox
end ElboimSly
