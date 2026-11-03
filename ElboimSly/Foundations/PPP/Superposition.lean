/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.PPP.Operations
public import ElboimSly.Foundations.PPP.PoissonMoments
import Mathlib

/-!
# Superposition of independent Poisson point processes

Superposition (b), (c).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly

variable {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]

/-- Finite measures on `ι → [0,∞]` are determined by their values on boxes `∏ [0, cᵢ]`. -/
theorem ext_pi_Iic {ι : Type*} [Fintype ι] {ρ π : Measure (ι → ℝ≥0∞)} [IsFiniteMeasure ρ]
    (h : ∀ c : ι → ℝ≥0∞,
      ρ (Set.pi Set.univ fun i => Set.Iic (c i)) = π (Set.pi Set.univ fun i => Set.Iic (c i))) :
    ρ = π := by
  have hC : ∀ i : ι, MeasurableSpace.generateFrom
      (Set.range (Set.Iic : ℝ≥0∞ → Set ℝ≥0∞)) = (inferInstance : MeasurableSpace ℝ≥0∞) :=
    fun _ => (borel_eq_generateFrom_Iic ℝ≥0∞).symm.trans BorelSpace.measurable_eq.symm
  have hspan : ∀ i : ι, IsCountablySpanning (Set.range (Set.Iic : ℝ≥0∞ → Set ℝ≥0∞)) :=
    fun _ => ⟨fun _ => Set.univ, fun _ => ⟨⊤, Set.Iic_top⟩, Set.iUnion_const _⟩
  have hbox : ∀ c : ι → ℝ≥0∞, (Set.pi Set.univ fun i => Set.Iic (c i)) ∈
      (Set.pi Set.univ '' Set.pi Set.univ fun _ : ι => Set.range (Set.Iic : ℝ≥0∞ → Set ℝ≥0∞)) :=
    fun c => ⟨fun i => Set.Iic (c i), fun i _ => ⟨c i, rfl⟩, rfl⟩
  refine ext_of_generate_finite
    (Set.pi Set.univ '' Set.pi Set.univ fun _ : ι => Set.range (Set.Iic : ℝ≥0∞ → Set ℝ≥0∞))
    (generateFrom_eq_pi hC hspan).symm (IsPiSystem.pi fun _ => isPiSystem_Iic) ?_ ?_
  · rintro _ ⟨s, hs, rfl⟩
    choose c hc using fun i => hs i (Set.mem_univ i)
    have : s = fun i => Set.Iic (c i) := funext fun i => (hc i).symm
    subst this
    exact h c
  · have := h (fun _ => ⊤)
    simpa [Set.Iic_top] using this

namespace IsPoissonPointProcess

variable {N : ℕ → Ω → Measure S} {μ : ℕ → Measure S} {ν : Measure S} {P : Measure Ω}

/-- Partial sums of independent PPPs are PPPs (induction using `add`). -/
theorem partial_sum (h : ∀ k, IsPoissonPointProcess (N k) (μ k) P) (hi : iIndepFun N P)
    (K : ℕ) :
    IsPoissonPointProcess (fun ω => ∑ k ∈ Finset.range (K + 1), N k ω)
      (∑ k ∈ Finset.range (K + 1), μ k) P := by
  induction K with
  | zero => simpa using h 0
  | succ K ih =>
    have hind := hi.indepFun_finsetSum_of_notMem (fun k => (h k).measurable)
      (s := Finset.range (K + 1)) (i := K + 1) (by simp)
    have h2 := ih.add (h (K + 1)) (by
      refine hind.congr ?_ (Filter.EventuallyEq.refl _ _)
      exact Filter.Eventually.of_forall fun ω => by simp [Finset.sum_apply])
    simpa [Finset.sum_range_succ] using h2

/-- Superposition (b): countable superposition. -/
theorem sum (h : ∀ k, IsPoissonPointProcess (N k) (μ k) P) (hi : iIndepFun N P) :
    IsPoissonPointProcess (fun ω => Measure.sum fun k => N k ω) (Measure.sum μ) P := by
  have := (h 0).isProbabilityMeasure
  refine mk' (measurable_measure_sum fun k => (h k).measurable) ?_
  intro n A hA hd
  set M : ℕ → Ω → Measure S := fun K ω => ∑ k ∈ Finset.range (K + 1), N k ω with hM
  have hVm : ∀ K, Measurable fun ω j => M K ω (A j) := fun K =>
    Measurable.of_eval fun j => ((partial_sum h hi K).measurable_count (hA j))
  have hV : Measurable fun ω j => (Measure.sum fun k => N k ω) (A j) :=
    Measurable.of_eval fun j => (Measure.measurable_coe (hA j)).comp
      (measurable_measure_sum fun k => (h k).measurable)
  refine ext_pi_Iic fun c => ?_
  rw [Measure.pi_pi]
  rw [Measure.map_apply hV (MeasurableSet.univ_pi fun j => measurableSet_Iic)]
  set E : ℕ → Set Ω := fun K => (fun ω j => M K ω (A j)) ⁻¹' Set.pi Set.univ fun j => Set.Iic (c j)
    with hE
  have hEeq : ((fun ω j => (Measure.sum fun k => N k ω) (A j)) ⁻¹'
      Set.pi Set.univ fun j => Set.Iic (c j)) = ⋂ K, E K := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, Set.mem_Iic, true_implies,
      Set.mem_iInter, hE, hM]
    rw [forall_comm]
    refine forall_congr' fun j => ?_
    rw [Measure.sum_apply _ (hA j)]
    constructor
    · intro hle K
      calc (∑ k ∈ Finset.range (K + 1), N k ω) (A j)
          = ∑ k ∈ Finset.range (K + 1), N k ω (A j) := by simp
        _ ≤ ∑' k, N k ω (A j) := ENNReal.sum_le_tsum _
        _ ≤ c j := hle
    · intro hK
      rw [ENNReal.tsum_eq_iSup_nat]
      refine iSup_le fun K => le_trans ?_ (hK K)
      simp only [Measure.coe_finsetSum, Finset.sum_apply]
      exact Finset.sum_le_sum_of_subset (Finset.range_mono (Nat.le_succ K))
  have hanti : Antitone E := by
    intro K K' hKK' ω hω
    simp only [hE, Set.mem_preimage, Set.mem_pi, Set.mem_univ, Set.mem_Iic, true_implies] at hω ⊢
    intro j
    refine le_trans ?_ (hω j)
    simp only [hM, Measure.coe_finsetSum, Finset.sum_apply]
    exact Finset.sum_le_sum_of_subset (Finset.range_mono (Nat.succ_le_succ hKK'))
  have hEm : ∀ K, MeasurableSet (E K) := fun K =>
    hVm K (MeasurableSet.univ_pi fun j => measurableSet_Iic)
  have hlim := tendsto_measure_iInter_atTop (μ := P) (fun K => (hEm K).nullMeasurableSet) hanti
    ⟨0, measure_ne_top _ _⟩
  have hPK : ∀ K, P (E K) = ∏ j, extPoissonMeasure ((∑ k ∈ Finset.range (K + 1), μ k) (A j))
      (Set.Iic (c j)) := by
    intro K
    have := (partial_sum h hi K).map_counts_fintype hA hd
    have hh : P (E K) = (P.map fun ω j => M K ω (A j))
        (Set.pi Set.univ fun j => Set.Iic (c j)) := by
      rw [Measure.map_apply (hVm K) (MeasurableSet.univ_pi fun j => measurableSet_Iic)]
    rw [hh, this, Measure.pi_pi]
  have hlim2 : Tendsto (fun K => P (E K)) atTop
      (𝓝 (∏ j, extPoissonMeasure ((Measure.sum μ) (A j)) (Set.Iic (c j)))) := by
    simp_rw [hPK]
    refine ENNReal.tendsto_finsetProd_of_ne_top Finset.univ (fun j _ => ?_)
      (fun j _ => measure_ne_top _ _)
    have h1 : Tendsto (fun K => (∑ k ∈ Finset.range (K + 1), μ k) (A j)) atTop
        (𝓝 ((Measure.sum μ) (A j))) := by
      simp only [Measure.coe_finsetSum, Finset.sum_apply, Measure.sum_apply _ (hA j)]
      exact (ENNReal.tendsto_nat_tsum fun k => μ k (A j)).comp (tendsto_add_atTop_nat 1)
    exact ((continuous_extPoissonMeasure_Iic (c j)).tendsto _).comp h1
  rw [hEeq]
  exact tendsto_nhds_unique hlim hlim2

/-- Superposition (c), two-set form. -/
theorem restrict_add_restrict_compl {N₁ N₂ : Ω → Measure S} {ν : Measure S}
    (h₁ : IsPoissonPointProcess N₁ ν P) (h₂ : IsPoissonPointProcess N₂ ν P)
    (hi : IndepFun N₁ N₂ P) {A : Set S} (hA : MeasurableSet A) :
    IsPoissonPointProcess (fun ω => (N₁ ω).restrict A + (N₂ ω).restrict Aᶜ) ν P := by
  have hr₁ := h₁.restrict hA
  have hr₂ := h₂.restrict hA.compl
  have hind : IndepFun (fun ω => (N₁ ω).restrict A) (fun ω => (N₂ ω).restrict Aᶜ) P :=
    hi.comp (measurable_restrict_measure hA) (measurable_restrict_measure hA.compl)
  have := hr₁.add hr₂ hind
  rwa [Measure.restrict_add_restrict_compl hA] at this

end IsPoissonPointProcess

end ElboimSly
