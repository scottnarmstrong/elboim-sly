/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.PPP.MeckeMeasurable
public import ElboimSly.Foundations.PPP.MeckeDiag
public import ElboimSly.Foundations.PPP.Simple
public import ElboimSly.Foundations.PPP.PoissonMoments
public import Mathlib

/-!
# Factorial moment measures of Poisson point processes

Factorial moment measures.

For a dissecting system `D` of `(S, μ)` with `μ` diffuse and a Poisson point process `N`:

* `measurable_meckePhi_count`: `ω ↦ 𝟙_{Ω_s} N(ω)^{(n)}(A)` is measurable;
* `lintegral_meckePhi`: `E 𝟙_{Ω_s} N^{(n)}(A) = μ^{⊗ n}(A)`;
* `measure_exists_distinct_atoms_le`: the union bound.

The generating hypothesis of the written proof is not needed: the `π`-system `meckeC` of boxes of
pairwise disjoint sets (together with subsets of the off-diagonal complement) already generates.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ElboimSly

variable {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]

namespace SepPartSeq

variable {D : SepPartSeq S}

theorem pi_injSet_compl_null (D : SepPartSeq S) {n : ℕ} {μ : Measure S} [SigmaFinite μ]
    (hdiff : ∀ x, μ {x} = 0) : Measure.pi (fun _ : Fin n => μ) (injSet S n)ᶜ = 0 := by
  have : (injSet S n)ᶜ ⊆ ⋃ i, ⋃ j, ⋃ (_ : i ≠ j), {x : Fin n → S | x i = x j} := by
    intro x hx
    simp only [injSet, Set.mem_compl_iff, Set.mem_ofPred_eq, Function.Injective, not_forall] at hx
    obtain ⟨i, j, hij, hne⟩ := hx
    simp only [Set.mem_iUnion]
    exact ⟨i, j, hne, hij⟩
  refine measure_mono_null this ?_
  refine measure_iUnion_null fun i => measure_iUnion_null fun j => measure_iUnion_null fun hne => ?_
  exact D.pi_coords_eq_null hdiff hne

/-- The `π`-system sets used to cover the product space. -/
def meckeCover (D : SepPartSeq S) (n : ℕ) : Option (ℕ × (Fin n → ℕ)) → Set (Fin n → S)
  | none => (injSet S n)ᶜ
  | some p => if Function.Injective p.2 then Set.pi Set.univ (fun j => D.cell p.1 (p.2 j)) else ∅

theorem meckeCover_mem (D : SepPartSeq S) (n : ℕ) (o : Option (ℕ × (Fin n → ℕ))) :
    D.meckeCover n o ∈ D.meckeC n := by
  cases o with
  | none => exact Or.inr ⟨(D.measurableSet_injSet n).compl, subset_rfl⟩
  | some p =>
    by_cases hinj : Function.Injective p.2
    · simp only [meckeCover, hinj, ite_true]
      refine Or.inl ⟨_, fun j => D.measurableSet_cell _ _, fun j => ?_, ?_, rfl⟩
      · by_cases hne : (D.cell p.1 (p.2 j)).Nonempty
        · obtain ⟨y, hy⟩ := hne
          exact ⟨_, D.cell_subset_cell_zero hy⟩
        · exact ⟨0, by rw [Set.not_nonempty_iff_eq_empty.1 hne]; simp⟩
      · intro i j hij
        refine Set.disjoint_left.2 fun y hy hy' => hij (hinj ?_)
        have h1 : D.idx p.1 y = p.2 i := hy
        have h2 : D.idx p.1 y = p.2 j := hy'
        rw [← h1, ← h2]
    · simp only [meckeCover, hinj, ite_false]
      exact Or.inr ⟨MeasurableSet.empty, by simp⟩

theorem iUnion_meckeCover (D : SepPartSeq S) (n : ℕ) :
    ⋃ o, D.meckeCover n o = Set.univ := by
  ext x
  simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
  by_cases hx : Function.Injective x
  · obtain ⟨m, hm⟩ := D.exists_separating_level (Set.finite_range x)
    have hb : Function.Injective (fun j => D.idx m (x j)) := by
      intro i j hij
      exact hx (hm _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ hij)
    refine ⟨some (m, fun j => D.idx m (x j)), ?_⟩
    simp only [meckeCover, hb, ite_true, Set.mem_pi, Set.mem_univ, true_implies]
    exact fun j => rfl
  · exact ⟨none, hx⟩

end SepPartSeq

namespace IsPoissonPointProcess

variable {N : Ω → Measure S} {μ : Measure S} {P : Measure Ω}

/-- Expectation of a product of counts of disjoint sets. -/
theorem lintegral_prod_count (h : IsPoissonPointProcess N μ P) {n : ℕ} {B : Fin n → Set S}
    (hB : ∀ j, MeasurableSet (B j)) (hd : Pairwise (Function.onFun Disjoint B)) :
    ∫⁻ ω, ∏ j, N ω (B j) ∂P = ∏ j, μ (B j) := by
  have := h.isProbabilityMeasure
  have hmap := h.map_counts_fintype hB hd
  have hm : ∀ j, Measurable fun ω => N ω (B j) := fun j => h.measurable_count (hB j)
  have hZ : iIndepFun (fun j ω => N ω (B j)) P := by
    rw [iIndepFun_iff_map_fun_eq_pi_map (fun j => (hm j).aemeasurable), hmap]
    congr 1
    funext j
    exact (h.map_count (hB j)).symm
  rw [lintegral_prod_eq_prod_lintegral_of_indepFun Finset.univ (fun j ω => N ω (B j)) hZ hm]
  exact Finset.prod_congr rfl fun j _ => h.lintegral_count (hB j)

/-- Factorial moment measures (measurability). -/
theorem measurable_meckePhi_count (h : IsPoissonPointProcess N μ P) (D : SepPartSeq S) (n : ℕ)
    {A : Set (Fin n → S)} (hA : MeasurableSet A) :
    Measurable fun ω => meckePhi D n (N ω) A :=
  (Measure.measurable_coe hA).comp ((D.measurable_meckePhi n).comp h.measurable)

/-- Factorial moment measures: `E 𝟙_{Ω_s} N^{(n)}(A) = μ^{⊗ n}(A)`. -/
theorem lintegral_meckePhi (h : IsPoissonPointProcess N μ P) (D : SepPartSeq S)
    (hD : D.IsDissecting μ) (hdiff : ∀ x, μ {x} = 0) (n : ℕ) {A : Set (Fin n → S)}
    (hA : MeasurableSet A) :
    ∫⁻ ω, meckePhi D n (N ω) A ∂P = Measure.pi (fun _ : Fin n => μ) A := by
  have := h.isProbabilityMeasure
  have := SepPartSeq.sigmaFinite_of_isDissecting hD
  have hκ : Measurable fun ω => meckePhi D n (N ω) := (D.measurable_meckePhi n).comp h.measurable
  have hM : ∀ B, MeasurableSet B → Measure.bind P (fun ω => meckePhi D n (N ω)) B =
      ∫⁻ ω, meckePhi D n (N ω) B ∂P := fun B hB => Measure.bind_apply hB hκ.aemeasurable
  suffices hext : Measure.bind P (fun ω => meckePhi D n (N ω)) =
      Measure.pi (fun _ : Fin n => μ) by
    rw [← hM A hA, hext]
  have hbox : ∀ B : Fin n → Set S, (∀ j, MeasurableSet (B j)) →
      Pairwise (Function.onFun Disjoint B) →
      Measure.bind P (fun ω => meckePhi D n (N ω)) (Set.pi Set.univ B) =
        Measure.pi (fun _ : Fin n => μ) (Set.pi Set.univ B) := by
    intro B hB hd
    rw [hM _ (MeasurableSet.univ_pi hB), Measure.pi_pi]
    rw [← h.lintegral_prod_count hB hd]
    refine lintegral_congr_ae ?_
    filter_upwards [h.ae_mem_bSimple D hD hdiff] with ω hω
    exact SepPartSeq.meckePhi_box hω hB hd
  have hsmall : ∀ s : Set (Fin n → S), MeasurableSet s → s ⊆ (injSet S n)ᶜ →
      Measure.bind P (fun ω => meckePhi D n (N ω)) s = Measure.pi (fun _ : Fin n => μ) s := by
    intro s hs hsub
    rw [hM s hs, measure_mono_null hsub (D.pi_injSet_compl_null hdiff)]
    refine (lintegral_congr fun ω => ?_).trans lintegral_zero
    by_cases hω : N ω ∈ D.bSimple
    · rw [meckePhi_of_mem n hω]; exact factorialMeasure_eq_zero_of_subset n _ hs hsub
    · rw [meckePhi_of_not_mem n hω]; rfl
  have heq : ∀ s ∈ D.meckeC n, Measure.bind P (fun ω => meckePhi D n (N ω)) s =
      Measure.pi (fun _ : Fin n => μ) s := by
    rintro s (⟨B, hB, -, hd, rfl⟩ | ⟨hs, hsub⟩)
    · exact hbox B hB hd
    · exact hsmall s hs hsub
  obtain ⟨e, he⟩ := exists_surjective_nat (Option (ℕ × (Fin n → ℕ)))
  refine Measure.ext_of_generateFrom_of_iUnion (D.meckeC n) (fun i => D.meckeCover n (e i))
    (D.generateFrom_meckeC n).symm (D.isPiSystem_meckeC n) ?_
    (fun i => D.meckeCover_mem n (e i)) ?_ heq
  · rw [← D.iUnion_meckeCover n]
    ext x
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨i, hi⟩; exact ⟨e i, hi⟩
    · rintro ⟨o, ho⟩; obtain ⟨i, rfl⟩ := he o; exact ⟨i, ho⟩
  · intro i
    rw [heq _ (D.meckeCover_mem n (e i))]
    cases e i with
    | none => simp [SepPartSeq.meckeCover, D.pi_injSet_compl_null hdiff]
    | some p =>
      by_cases hinj : Function.Injective p.2
      · simp only [SepPartSeq.meckeCover, hinj, ite_true, Measure.pi_pi]
        exact (ENNReal.prod_lt_top fun j _ => SepPartSeq.IsDissecting.measure_cell_lt_top D hD p.1 (p.2 j)).ne
      · simp [SepPartSeq.meckeCover, hinj]

/-- Factorial moment measures (union bound): the probability that `N` is not simple or has `n`
pairwise distinct atoms with tuple in `A` is at most `μ^{⊗ n}(A)`. -/
theorem measure_not_simple_or_distinct_atoms_le (h : IsPoissonPointProcess N μ P)
    (D : SepPartSeq S) (hD : D.IsDissecting μ) (hdiff : ∀ x, μ {x} = 0) (n : ℕ)
    {A : Set (Fin n → S)} (hA : MeasurableSet A) :
    P ({ω | N ω ∉ D.bSimple} ∪ {ω | 1 ≤ meckePhi D n (N ω) A}) ≤
      Measure.pi (fun _ : Fin n => μ) A := by
  have hnull : P {ω | N ω ∉ D.bSimple} = 0 := ae_iff.1 (h.ae_mem_bSimple D hD hdiff)
  refine (measure_union_le _ _).trans ?_
  rw [hnull, zero_add, ← h.lintegral_meckePhi D hD hdiff n hA]
  have := mul_meas_ge_le_lintegral₀ (μ := P) (f := fun ω => meckePhi D n (N ω) A)
    (h.measurable_meckePhi_count D n hA).aemeasurable 1
  simpa using this

end IsPoissonPointProcess

end ElboimSly
