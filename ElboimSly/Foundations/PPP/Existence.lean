/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.PPP.Block
public import ElboimSly.Foundations.PPP.Superposition
public import ElboimSly.Foundations.PPP.Finite
public import Mathlib

/-!
# Existence of Poisson point processes

Existence.

For a `σ`-finite measure `μ` on a nonempty space `S` we build
`Ω = ∏_k (ℕ × S^ℕ)`, `P = ⨂_k (Po(λ_k) ⊗ ⨂_i ν_k)` and
`N(ω) = ∑_k (∑_{i<K_k} δ_{Y_{k,i}})|_{Q_k}`, exactly as in the written proof.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace ElboimSly

universe u

variable {S : Type u} [MeasurableSpace S]

section Construction

variable (μ : Measure S) [SigmaFinite μ] (x₀ : S)

/-- `ν_k = μ|_{Q_k} / μ(Q_k)` if `μ(Q_k) > 0`, and `δ_{x₀}` otherwise. -/
noncomputable def piece (k : ℕ) : Measure S :=
  if μ (ppartition μ k) = 0 then Measure.dirac x₀ else ProbabilityTheory.cond μ (ppartition μ k)

instance isProbabilityMeasure_piece (k : ℕ) : IsProbabilityMeasure (piece μ x₀ k) := by
  unfold piece
  split_ifs with h
  · infer_instance
  · exact cond_isProbabilityMeasure_of_finite h (measure_ppartition_lt_top μ k).ne

/-- `λ_k = μ(Q_k)` as a nonnegative real. -/
noncomputable def pieceMass (k : ℕ) : ℝ≥0 := (μ (ppartition μ k)).toNNReal

theorem restrict_piece (k : ℕ) :
    (((pieceMass μ k : ℝ≥0∞)) • piece μ x₀ k).restrict (ppartition μ k) =
      μ.restrict (ppartition μ k) := by
  have hfin := (measure_ppartition_lt_top μ k).ne
  have hm := measurableSet_ppartition μ k
  by_cases h : μ (ppartition μ k) = 0
  · have : pieceMass μ k = 0 := by simp [pieceMass, h]
    rw [this, Measure.restrict_eq_zero.2 h]
    simp
  · simp only [piece, h, ite_false, ProbabilityTheory.cond, pieceMass, ENNReal.coe_toNNReal hfin]
    rw [Measure.restrict_smul, Measure.restrict_smul, Measure.restrict_restrict hm,
      Set.inter_self, smul_smul, ENNReal.mul_inv_cancel h hfin, one_smul]

/-- The sample space `∏_k (ℕ × S^ℕ)`. -/
abbrev ExSpace (S : Type*) : Type _ := ∀ _ : ℕ, ℕ × (ℕ → S)

/-- The law `⨂_k (Po(λ_k) ⊗ ⨂_i ν_k)`. -/
noncomputable def exLaw : Measure (ExSpace S) :=
  Measure.infinitePi fun k => blockMeasure (piece μ x₀ k) (pieceMass μ k)

instance : IsProbabilityMeasure (exLaw μ x₀) := by unfold exLaw; infer_instance

/-- The constructed random measure. -/
noncomputable def exProc (ω : ExSpace S) : Measure S :=
  Measure.sum fun k => (blockProc (ω k)).restrict (ppartition μ k)

theorem isPoissonPointProcess_exProc : IsPoissonPointProcess (exProc μ) μ (exLaw μ x₀) := by
  set P := exLaw μ x₀ with hP
  have hG : ∀ k, Measurable fun p : ℕ × (ℕ → S) => (blockProc p).restrict (ppartition μ k) :=
    fun k => (measurable_restrict_measure (measurableSet_ppartition μ k)).comp measurable_blockProc
  have hk : ∀ k, IsPoissonPointProcess (fun ω : ExSpace S => (blockProc (ω k)).restrict
      (ppartition μ k)) (μ.restrict (ppartition μ k)) P := by
    intro k
    have h1 := (isPoissonPointProcess_blockProc (piece μ x₀ k) (pieceMass μ k)).restrict
      (measurableSet_ppartition μ k)
    rw [restrict_piece μ x₀ k] at h1
    refine h1.of_map_eq ((hG k).comp (measurable_pi_apply k)) ?_
    have e : (fun ω : ExSpace S => (blockProc (ω k)).restrict (ppartition μ k)) =
        (fun p : ℕ × (ℕ → S) => (blockProc p).restrict (ppartition μ k)) ∘ fun ω => ω k := rfl
    rw [e, ← Measure.map_map (hG k) (measurable_pi_apply k), hP, exLaw,
      Measure.infinitePi_map_eval]
  have hi : iIndepFun (fun (k : ℕ) (ω : ExSpace S) =>
      (blockProc (ω k)).restrict (ppartition μ k)) P :=
    iIndepFun_infinitePi (X := fun k p => (blockProc p).restrict (ppartition μ k)) hG
  have := IsPoissonPointProcess.sum hk hi
  have hμ : Measure.sum (fun k => μ.restrict (ppartition μ k)) = μ := by
    rw [← Measure.restrict_iUnion (pairwise_disjoint_ppartition μ) (measurableSet_ppartition μ),
      iUnion_ppartition, Measure.restrict_univ]
  rwa [hμ] at this

theorem exProc_mem_lfSet (ω : ExSpace S) : exProc μ ω ∈ lfSet μ := by
  intro k
  have hm := measurableSet_ppartition μ k
  unfold exProc
  rw [Measure.sum_apply _ hm]
  have hzero : ∀ j, j ≠ k → ((blockProc (ω j)).restrict (ppartition μ j)) (ppartition μ k) = 0 := by
    intro j hj
    rw [Measure.restrict_apply hm,
      (pairwise_disjoint_ppartition μ hj.symm).inter_eq, measure_empty]
  rw [tsum_eq_single k hzero, Measure.restrict_apply hm, Set.inter_self]
  calc blockProc (ω k) (ppartition μ k) ≤ blockProc (ω k) Set.univ := measure_mono (Set.subset_univ _)
    _ < ∞ := by
      unfold blockProc mixedBinomial
      rw [Measure.coe_finsetSum, Finset.sum_apply]
      refine ENNReal.sum_lt_top.2 fun i _ => ?_
      simp

end Construction

theorem poissonMeasure_zero : poissonMeasure 0 = Measure.dirac 0 := by
  refine Measure.ext_of_singleton ?_ |> fun h => h
  intro n
  rw [poissonMeasure_singleton]
  cases n <;> simp

theorem extPoissonMeasure_zero : extPoissonMeasure 0 = Measure.dirac 0 := by
  have := extPoissonMeasure_coe 0
  simp only [ENNReal.coe_zero] at this
  rw [this, poissonMeasure_zero]
  exact (Measure.map_dirac (f := (Nat.cast : ℕ → ℝ≥0∞)) 0).trans (by simp)

theorem pi_dirac_fintype {ι : Type*} [Fintype ι] (a : ι → ℝ≥0∞) :
    Measure.pi (fun i => Measure.dirac (a i)) = Measure.dirac a := by
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.dirac_apply' _ (MeasurableSet.univ_pi hs)]
  simp only [Measure.dirac_apply' _ (hs _)]
  by_cases h : ∀ i, a i ∈ s i
  · simp [Set.indicator, h]
  · push Not at h
    obtain ⟨i, hi⟩ := h
    have hl : (Set.pi Set.univ s).indicator (1 : (ι → ℝ≥0∞) → ℝ≥0∞) a = 0 :=
      Set.indicator_of_notMem (fun h' => hi (Set.mem_univ_pi.1 h' i)) _
    have hr : ∏ j, (s j).indicator (1 : ℝ≥0∞ → ℝ≥0∞) (a j) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi _)
    rw [hl, hr]

/-- The empty space: the zero random measure. -/
theorem isPoissonPointProcess_of_isEmpty {S : Type*} [MeasurableSpace S] [IsEmpty S]
    (μ : Measure S) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] :
    IsPoissonPointProcess (fun _ : Ω => (0 : Measure S)) μ P := by
  refine IsPoissonPointProcess.mk' measurable_const ?_
  intro n A hA hd
  have hμ : ∀ j, μ (A j) = 0 := fun j => by
    rw [Set.eq_empty_of_isEmpty (A j), measure_empty]
  simp_rw [hμ, extPoissonMeasure_zero, pi_dirac_fintype]
  simp [Measure.map_const]

/-- Existence: existence of a Poisson point process for every `σ`-finite
intensity, with `N(ω)` locally finite for every `ω`. -/
theorem exists_isPoissonPointProcess {S : Type u} [MeasurableSpace S] (μ : Measure S)
    [SigmaFinite μ] :
    ∃ (Ω : Type u) (_ : MeasurableSpace Ω) (P : Measure Ω) (N : Ω → Measure S),
      IsProbabilityMeasure P ∧ IsPoissonPointProcess N μ P ∧ ∀ ω, N ω ∈ lfSet μ := by
  by_cases hS : Nonempty S
  · obtain ⟨x₀⟩ := hS
    exact ⟨ExSpace S, inferInstance, exLaw μ x₀, exProc μ, inferInstance,
      isPoissonPointProcess_exProc μ x₀, exProc_mem_lfSet μ⟩
  · rw [not_nonempty_iff] at hS
    refine ⟨PUnit.{u + 1}, inferInstance, Measure.dirac PUnit.unit, fun _ => 0, inferInstance,
      isPoissonPointProcess_of_isEmpty μ _, fun _ => zero_mem_lfSet μ⟩

end ElboimSly
