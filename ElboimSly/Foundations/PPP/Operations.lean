/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.PPP.Law
import Mathlib

/-!
# Images, restrictions and finite superposition

Images; Restriction (a), superposition (a).

Note that `IsPoissonPointProcess` does not require `σ`-finiteness of the intensity, so the
`σ`-finiteness hypotheses in the written proof are not needed here.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace ElboimSly

variable {Ω S S' : Type*} [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace S']

namespace IsPoissonPointProcess

variable {N : Ω → Measure S} {μ : Measure S} {P : Measure Ω}

/-- Build a PPP from measurability and (PPP2) alone: (PPP1) is the case `n = 1`. -/
theorem mk' (hN : Measurable N)
    (h2 : ∀ (n : ℕ) (A : Fin n → Set S), (∀ j, MeasurableSet (A j)) →
      Pairwise (Function.onFun Disjoint A) →
      P.map (fun ω j => N ω (A j)) = Measure.pi (fun j => extPoissonMeasure (μ (A j)))) :
    IsPoissonPointProcess N μ P := by
  refine ⟨hN, fun A hA => ?_, h2⟩
  have h1 := h2 1 (fun _ => A) (fun _ => hA) (fun i j hij => absurd (Subsingleton.elim i j) hij)
  have hm : Measurable fun ω (_ : Fin 1) => N ω A :=
    Measurable.of_eval fun _ => (Measure.measurable_coe hA).comp hN
  have : (fun ω => N ω A) = (fun x : Fin 1 → ℝ≥0∞ => x 0) ∘ fun ω (_ : Fin 1) => N ω A := rfl
  rw [this, ← Measure.map_map (measurable_pi_apply 0) hm, h1, Measure.pi_map_eval]
  simp

/-- Images: the image of a PPP under a measurable map. -/
theorem map_measure (h : IsPoissonPointProcess N μ P) {φ : S → S'} (hφ : Measurable φ) :
    IsPoissonPointProcess (fun ω => (N ω).map φ) (μ.map φ) P := by
  refine mk' ((measurable_map_measure hφ).comp h.measurable) ?_
  intro n A hA hd
  simp_rw [Measure.map_apply hφ (hA _)]
  exact h.2.2 n _ (fun j => hφ (hA j)) (fun i j hij => (hd hij).preimage φ)

/-- Images: invariance of the law under a measure-preserving map. -/
theorem map_measure_law_eq (h : IsPoissonPointProcess N μ P) {φ : S → S} (hφ : Measurable φ)
    (hμ : μ.map φ = μ) : P.map (fun ω => (N ω).map φ) = P.map N := by
  have h' : IsPoissonPointProcess (fun ω => (N ω).map φ) μ P := hμ ▸ h.map_measure hφ
  exact h.map_eq_map h'

/-- Images: `Law(G(φ_* N)) = Law(G(N))` for every measurable `G`. -/
theorem map_comp_map_measure_law_eq (h : IsPoissonPointProcess N μ P) {φ : S → S}
    (hφ : Measurable φ) (hμ : μ.map φ = μ) {β : Type*} [MeasurableSpace β]
    {G : Measure S → β} (hG : Measurable G) :
    P.map (fun ω => G ((N ω).map φ)) = P.map (fun ω => G (N ω)) := by
  rw [map_comp (N := fun ω => (N ω).map φ) ((measurable_map_measure hφ).comp h.measurable) hG,
    h.map_measure_law_eq hφ hμ, ← map_comp h.measurable hG]

/-- Restriction (a). -/
theorem restrict (h : IsPoissonPointProcess N μ P) {A : Set S} (hA : MeasurableSet A) :
    IsPoissonPointProcess (fun ω => (N ω).restrict A) (μ.restrict A) P := by
  refine mk' ((measurable_restrict_measure hA).comp h.measurable) ?_
  intro n B hB hd
  simp_rw [Measure.restrict_apply (hB _)]
  exact h.2.2 n (fun j => B j ∩ A) (fun j => (hB j).inter hA)
    (fun i j hij => (hd hij).mono Set.inter_subset_left Set.inter_subset_left)

end IsPoissonPointProcess

/-! ### Convolution of finite products -/

theorem map_add_prod_pi {ι : Type*} [Fintype ι] (a b : ι → Measure ℝ≥0∞)
    [∀ i, IsProbabilityMeasure (a i)] [∀ i, IsProbabilityMeasure (b i)] :
    ((Measure.pi a).prod (Measure.pi b)).map (fun p i => p.1 i + p.2 i) =
      Measure.pi fun i => a i ∗ b i := by
  have hT := measurePreserving_arrowProdEquivProdArrow ℝ≥0∞ ℝ≥0∞ ι a b
  have e : (fun p : (ι → ℝ≥0∞) × (ι → ℝ≥0∞) => fun i => p.1 i + p.2 i) ∘
      (MeasurableEquiv.arrowProdEquivProdArrow ℝ≥0∞ ℝ≥0∞ ι) =
      fun (x : ι → ℝ≥0∞ × ℝ≥0∞) i => (fun p : ℝ≥0∞ × ℝ≥0∞ => p.1 + p.2) (x i) := rfl
  have hmeas : Measurable fun p : (ι → ℝ≥0∞) × (ι → ℝ≥0∞) => fun i => p.1 i + p.2 i :=
    Measurable.of_eval fun i => ((measurable_pi_apply i).comp measurable_fst).add
      ((measurable_pi_apply i).comp measurable_snd)
  rw [← hT.map_eq, Measure.map_map hmeas hT.measurable, e,
    Measure.pi_map_pi (fun i => measurable_add.aemeasurable)]
  rfl

namespace IsPoissonPointProcess

variable {N N₁ N₂ : Ω → Measure S} {μ₁ μ₂ : Measure S} {P : Measure Ω}

/-- Superposition (a). -/
theorem add (h₁ : IsPoissonPointProcess N₁ μ₁ P) (h₂ : IsPoissonPointProcess N₂ μ₂ P)
    (hi : IndepFun N₁ N₂ P) :
    IsPoissonPointProcess (fun ω => N₁ ω + N₂ ω) (μ₁ + μ₂) P := by
  have := h₁.isProbabilityMeasure
  refine mk' (measurable_add_measure.comp (h₁.measurable.prodMk h₂.measurable)) ?_
  intro n A hA hd
  let g : Measure S → (Fin n → ℝ≥0∞) := fun ν j => ν (A j)
  have hg : Measurable g := measurable_countVec hA
  have hi' : IndepFun (g ∘ N₁) (g ∘ N₂) P := hi.comp hg hg
  have hp := (indepFun_iff_map_prod_eq_prod_map_map (hg.comp h₁.measurable).aemeasurable
    (hg.comp h₂.measurable).aemeasurable).1 hi'
  have e1 : P.map (g ∘ N₁) = Measure.pi fun j => extPoissonMeasure (μ₁ (A j)) :=
    h₁.map_counts_fintype hA hd
  have e2 : P.map (g ∘ N₂) = Measure.pi fun j => extPoissonMeasure (μ₂ (A j)) :=
    h₂.map_counts_fintype hA hd
  rw [e1, e2] at hp
  have hmeas : Measurable fun p : (Fin n → ℝ≥0∞) × (Fin n → ℝ≥0∞) => fun i => p.1 i + p.2 i :=
    Measurable.of_eval fun i => ((measurable_pi_apply i).comp measurable_fst).add
      ((measurable_pi_apply i).comp measurable_snd)
  have hpair : Measurable fun ω => (g (N₁ ω), g (N₂ ω)) :=
    (hg.comp h₁.measurable).prodMk (hg.comp h₂.measurable)
  have : (fun ω j => (N₁ ω + N₂ ω) (A j)) =
      (fun p : (Fin n → ℝ≥0∞) × (Fin n → ℝ≥0∞) => fun i => p.1 i + p.2 i) ∘
        fun ω => (g (N₁ ω), g (N₂ ω)) := by
    ext ω j; simp [g]
  rw [this, ← Measure.map_map hmeas hpair]
  have hp' : P.map (fun ω => (g (N₁ ω), g (N₂ ω))) = _ := hp
  rw [hp', map_add_prod_pi]
  congr 1
  ext j : 1
  simp only [Measure.add_apply]
  exact extPoissonMeasure_conv _ _

end IsPoissonPointProcess

end ElboimSly
