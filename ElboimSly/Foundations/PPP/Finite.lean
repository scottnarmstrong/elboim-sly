/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.PPP.Law
public import ElboimSly.Foundations.PPP.PoissonMoments
import Mathlib

/-!
# Finiteness and local finiteness

Finiteness and local finiteness.

* `ae_natCast_count`, `lintegral_count`, `ae_count_eq_top`, `ae_forall_natCast_count`: (a).
* `ppartition`: (b), the canonical finite-mass partition `Q` of a `σ`-finite measure.
* `lfSet`, `tau`, `measurableSet_lfSet`, `measurable_tau`, `tau_mem_lfSet`, `sigmaFinite_of_mem_lfSet`,
  `ae_mem_lfSet`, `isPoissonPointProcess_tau`, `tau_comp_ae_eq`: (c).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace ElboimSly

variable {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]

theorem lintegral_id_extPoissonMeasure (a : ℝ≥0∞) :
    ∫⁻ x, x ∂extPoissonMeasure a = a := by
  by_cases h : a = ∞
  · subst h; simp [extPoissonMeasure_top]
  · lift a to ℝ≥0 using h
    have h1 := lintegral_extDescFactorial a 1
    simp only [pow_one] at h1
    refine Eq.trans ?_ h1
    apply lintegral_congr_ae
    have hc : ∀ᵐ x ∂extPoissonMeasure a, x ∈ Set.range (Nat.cast : ℕ → ℝ≥0∞) := by
      rw [ae_iff]
      exact (prob_compl_eq_zero_iff (Set.countable_range _).measurableSet).2
        (extPoissonMeasure_range_natCast a)
    filter_upwards [hc] with x ⟨n, hn⟩
    subst hn
    simp [extDescFactorial_natCast]

namespace IsPoissonPointProcess

variable {N : Ω → Measure S} {μ : Measure S} {P : Measure Ω}

/-- Finiteness and local finiteness (a): a count of finite mean is a.s. a natural number. -/
theorem ae_natCast_count (h : IsPoissonPointProcess N μ P) {A : Set S} (hA : MeasurableSet A)
    (hμ : μ A < ∞) : ∀ᵐ ω ∂P, ∃ n : ℕ, N ω A = n := by
  have hm := h.measurable_count hA
  have key : ∀ᵐ y ∂(P.map fun ω => N ω A), y ∈ Set.range (Nat.cast : ℕ → ℝ≥0∞) := by
    rw [h.map_count hA, ae_iff]
    lift μ A to ℝ≥0 using hμ.ne with r
    exact (prob_compl_eq_zero_iff (Set.countable_range _).measurableSet).2
      (extPoissonMeasure_range_natCast r)
  rw [ae_map_iff (p := fun y => y ∈ Set.range (Nat.cast : ℕ → ℝ≥0∞)) hm.aemeasurable
    (Set.countable_range _).measurableSet] at key
  filter_upwards [key] with ω ⟨n, hn⟩ using ⟨n, hn.symm⟩

/-- Finiteness and local finiteness (a): `E N(A) = μ(A)`. -/
theorem lintegral_count (h : IsPoissonPointProcess N μ P) {A : Set S} (hA : MeasurableSet A) :
    ∫⁻ ω, N ω A ∂P = μ A := by
  have hm := h.measurable_count hA
  calc ∫⁻ ω, N ω A ∂P = ∫⁻ y, y ∂(P.map fun ω => N ω A) := (lintegral_map measurable_id hm).symm
    _ = μ A := by rw [h.map_count hA]; exact lintegral_id_extPoissonMeasure _

/-- Finiteness and local finiteness (a): infinite intensity gives an infinite count a.s. -/
theorem ae_count_eq_top (h : IsPoissonPointProcess N μ P) {A : Set S} (hA : MeasurableSet A)
    (hμ : μ A = ∞) : ∀ᵐ ω ∂P, N ω A = ∞ := by
  have hm := h.measurable_count hA
  have key : ∀ᵐ y ∂(P.map fun ω => N ω A), y = ∞ := by
    rw [h.map_count hA, hμ, extPoissonMeasure_top]
    exact ae_dirac_iff (measurableSet_singleton _) |>.2 rfl
  rw [ae_map_iff (p := fun y => y = ∞) hm.aemeasurable (measurableSet_singleton _)] at key
  exact key

/-- Finiteness and local finiteness (a): countably many sets simultaneously. -/
theorem ae_forall_natCast_count (h : IsPoissonPointProcess N μ P) {ι : Type*} [Countable ι]
    {A : ι → Set S} (hA : ∀ i, MeasurableSet (A i)) (hμ : ∀ i, μ (A i) < ∞) :
    ∀ᵐ ω ∂P, ∀ i, ∃ n : ℕ, N ω (A i) = n :=
  ae_all_iff.2 fun i => h.ae_natCast_count (hA i) (hμ i)

end IsPoissonPointProcess

/-! ### The canonical finite-mass partition and the truncation `τ` -/

section Partition

variable (μ : Measure S) [SigmaFinite μ]

/-- Finiteness and local finiteness (b): `Q k = F k \ ⋃_{j<k} F j`, for Mathlib's spanning sets `F`. -/
noncomputable def ppartition (k : ℕ) : Set S := disjointed (spanningSets μ) k

theorem measurableSet_ppartition (k : ℕ) : MeasurableSet (ppartition μ k) :=
  MeasurableSet.disjointed (measurableSet_spanningSets μ) k

theorem pairwise_disjoint_ppartition : Pairwise (Function.onFun Disjoint (ppartition μ)) :=
  disjoint_disjointed _

theorem iUnion_ppartition : ⋃ k, ppartition μ k = Set.univ := by
  show ⋃ k, disjointed (spanningSets μ) k = _
  rw [iUnion_disjointed, iUnion_spanningSets]

theorem measure_ppartition_lt_top (k : ℕ) : μ (ppartition μ k) < ∞ :=
  lt_of_le_of_lt (measure_mono (disjointed_subset _ k)) (measure_spanningSets_lt_top μ k)

/-- The set of locally finite measures (finite on every cell of the canonical partition). -/
def lfSet : Set (Measure S) := {ν | ∀ k, ν (ppartition μ k) < ∞}

open scoped Classical in
/-- The truncation `τ`: identity on `lfSet`, and `0` elsewhere. -/
noncomputable def tau (ν : Measure S) : Measure S := if ν ∈ lfSet μ then ν else 0

theorem measurableSet_lfSet : MeasurableSet (lfSet μ) := by
  have : lfSet μ = ⋂ k, (fun ν : Measure S => ν (ppartition μ k)) ⁻¹' Set.Iio ∞ := by
    ext ν; simp [lfSet]
  rw [this]
  exact MeasurableSet.iInter fun k =>
    (Measure.measurable_coe (measurableSet_ppartition μ k)) measurableSet_Iio

theorem measurable_tau : Measurable (tau μ : Measure S → Measure S) := by
  classical
  unfold tau
  exact Measurable.ite (measurableSet_lfSet μ) measurable_id measurable_const

theorem zero_mem_lfSet : (0 : Measure S) ∈ lfSet μ := fun k => by simp

theorem tau_mem_lfSet (ν : Measure S) : tau μ ν ∈ lfSet μ := by
  classical
  unfold tau
  split_ifs with h
  · exact h
  · exact zero_mem_lfSet μ

theorem tau_of_mem {ν : Measure S} (h : ν ∈ lfSet μ) : tau μ ν = ν := by
  classical
  simp [tau, h]

theorem sigmaFinite_of_mem_lfSet {ν : Measure S} (h : ν ∈ lfSet μ) : SigmaFinite ν :=
  ⟨⟨{ set := ppartition μ
      set_mem := fun _ => Set.mem_univ _
      finite := h
      spanning := iUnion_ppartition μ }⟩⟩

end Partition

namespace IsPoissonPointProcess

variable {N : Ω → Measure S} {μ : Measure S} {P : Measure Ω}

/-- Finiteness and local finiteness (c): `P(N ∈ 𝓜^lf) = 1`. -/
theorem ae_mem_lfSet [SigmaFinite μ] (h : IsPoissonPointProcess N μ P) :
    ∀ᵐ ω ∂P, N ω ∈ lfSet μ := by
  have := h.ae_forall_natCast_count (measurableSet_ppartition μ) (measure_ppartition_lt_top μ)
  filter_upwards [this] with ω hω k
  obtain ⟨n, hn⟩ := hω k
  rw [hn]; exact ENNReal.natCast_lt_top n

/-- Finiteness and local finiteness (c): `τ ∘ N = N` a.s. -/
theorem tau_comp_ae_eq [SigmaFinite μ] (h : IsPoissonPointProcess N μ P) :
    (fun ω => tau μ (N ω)) =ᵐ[P] N := by
  filter_upwards [h.ae_mem_lfSet] with ω hω using tau_of_mem μ hω

/-- Finiteness and local finiteness (c): `τ ∘ N` is again a PPP of intensity `μ`. -/
theorem tau_comp [SigmaFinite μ] (h : IsPoissonPointProcess N μ P) :
    IsPoissonPointProcess (fun ω => tau μ (N ω)) μ P :=
  h.of_ae_eq ((measurable_tau μ).comp h.measurable) h.tau_comp_ae_eq

end IsPoissonPointProcess

end ElboimSly
