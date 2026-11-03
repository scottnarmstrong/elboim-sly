/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Frozen.Defs.IsPoissonPointProcess
public import ElboimSly.Foundations.PPP.Giry
public import ElboimSly.Foundations.PPP.PoissonFacts
import Mathlib

/-!
# Joint law of counts and uniqueness in law

Joint law of arbitrary counts; Uniqueness in law.

* `IsPoissonPointProcess.map_counts_fintype`: (PPP2) for an arbitrary finite index type.
* `IsPoissonPointProcess.map_count_vec`: joint law of arbitrary counts (a).
* `IsPoissonPointProcess.of_map_eq`, `IsPoissonPointProcess.of_ae_eq`: joint law of arbitrary counts (b).
* `IsPoissonPointProcess.map_eq_map`: uniqueness in law, with converse `of_map_eq`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace ElboimSly

variable {Ω Ω' S : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] [MeasurableSpace S]

namespace IsPoissonPointProcess

variable {N : Ω → Measure S} {μ : Measure S} {P : Measure Ω}

theorem measurable (h : IsPoissonPointProcess N μ P) : Measurable N := h.1

theorem measurable_count (h : IsPoissonPointProcess N μ P) {A : Set S} (hA : MeasurableSet A) :
    Measurable fun ω => N ω A :=
  (Measure.measurable_coe hA).comp h.1

theorem map_count (h : IsPoissonPointProcess N μ P) {A : Set S} (hA : MeasurableSet A) :
    P.map (fun ω => N ω A) = extPoissonMeasure (μ A) := h.2.1 A hA

/-- `n = 0` in (PPP2): `P` is a probability measure. -/
theorem isProbabilityMeasure (h : IsPoissonPointProcess N μ P) : IsProbabilityMeasure P := by
  have h0 := h.2.2 0 (fun j => (Fin.elim0 j : Set S)) (fun j => Fin.elim0 j)
    (fun i => Fin.elim0 i)
  refine ⟨?_⟩
  have := congrArg (fun m => m Set.univ) h0
  rw [Measure.map_apply (Measurable.of_eval fun j => Fin.elim0 j) MeasurableSet.univ] at this
  simpa using this

/-- (PPP2) for an arbitrary finite index type. -/
theorem map_counts_fintype (h : IsPoissonPointProcess N μ P) {ι : Type*} [Fintype ι]
    {A : ι → Set S} (hA : ∀ i, MeasurableSet (A i)) (hd : Pairwise (Function.onFun Disjoint A)) :
    P.map (fun ω i => N ω (A i)) = Measure.pi (fun i => extPoissonMeasure (μ (A i))) := by
  classical
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  have h1 := h.2.2 (Fintype.card ι) (fun j => A (e j)) (fun j => hA _)
    (fun i j hij => hd (e.injective.ne hij))
  have hmp := measurePreserving_piCongrLeft
    (fun i => extPoissonMeasure (μ (A i))) e
  have hf : Measurable fun ω (j : Fin (Fintype.card ι)) => N ω (A (e j)) :=
    Measurable.of_eval fun j => h.measurable_count (hA _)
  have hg : (fun ω i => N ω (A i)) =
      (MeasurableEquiv.piCongrLeft (fun _ : ι => ℝ≥0∞) e) ∘
        fun ω (j : Fin (Fintype.card ι)) => N ω (A (e j)) := by
    ext ω i
    obtain ⟨j, rfl⟩ := e.surjective i
    rw [Function.comp_apply, MeasurableEquiv.piCongrLeft_apply_apply]
  rw [hg, ← Measure.map_map (MeasurableEquiv.measurable _) hf, h1, hmp.map_eq]

end IsPoissonPointProcess

/-! ### Atoms of a finite family of sets -/

/-- The atom `α_ε = ⋂_{ε i} Bᵢ ∩ ⋂_{¬ ε i} Bᵢᶜ` of `B₀,…,B_{l-1}`. Joint law of arbitrary counts. -/
def atom {l : ℕ} (B : Fin l → Set S) (ε : Fin l → Bool) : Set S :=
  ⋂ i, if ε i then B i else (B i)ᶜ

omit [MeasurableSpace S] in
theorem mem_atom {l : ℕ} {B : Fin l → Set S} {ε : Fin l → Bool} {x : S} :
    x ∈ atom B ε ↔ ∀ i, (x ∈ B i ↔ ε i = true) := by
  simp only [atom, Set.mem_iInter]
  refine forall_congr' fun i => ?_
  cases h : ε i <;> simp

theorem measurableSet_atom {l : ℕ} {B : Fin l → Set S} (hB : ∀ i, MeasurableSet (B i))
    (ε : Fin l → Bool) : MeasurableSet (atom B ε) :=
  MeasurableSet.iInter fun i => by
    split_ifs
    exacts [hB i, (hB i).compl]

omit [MeasurableSpace S] in
theorem pairwise_disjoint_atom {l : ℕ} (B : Fin l → Set S) :
    Pairwise (Function.onFun Disjoint (atom B)) := by
  intro ε ε' hne
  rw [Function.onFun, Set.disjoint_left]
  intro x h1 h2
  apply hne
  funext i
  have h1 := mem_atom.1 h1 i
  have h2 := mem_atom.1 h2 i
  exact Bool.eq_iff_iff.2 (h1.symm.trans h2)

omit [MeasurableSpace S] in
theorem eq_biUnion_atom {l : ℕ} (B : Fin l → Set S) (i : Fin l) :
    B i = ⋃ ε ∈ (Finset.univ.filter fun ε : Fin l → Bool => ε i = true), atom B ε := by
  classical
  ext x
  simp only [Set.mem_iUnion, Finset.mem_filter, Finset.mem_univ, true_and, exists_prop]
  constructor
  · intro hx
    refine ⟨fun j => decide (x ∈ B j), by simpa using hx, mem_atom.2 fun j => by simp⟩
  · rintro ⟨ε, hε, hx⟩
    exact (mem_atom.1 hx i).2 hε

/-- The summation map `Σ` of joint law of arbitrary counts. -/
noncomputable def sumMap (l : ℕ) (y : (Fin l → Bool) → ℝ≥0∞) : Fin l → ℝ≥0∞ :=
  fun i => ∑ ε ∈ Finset.univ.filter (fun ε : Fin l → Bool => ε i = true), y ε

theorem measurable_sumMap (l : ℕ) : Measurable (sumMap l) :=
  Measurable.of_eval fun _i =>
    Finset.measurable_sum _ fun ε _ => measurable_pi_apply ε

theorem measure_eq_sum_atom {l : ℕ} {B : Fin l → Set S} (hB : ∀ i, MeasurableSet (B i))
    (ν : Measure S) (i : Fin l) :
    ν (B i) = ∑ ε ∈ Finset.univ.filter (fun ε : Fin l → Bool => ε i = true), ν (atom B ε) := by
  conv_lhs => rw [eq_biUnion_atom B i]
  exact measure_biUnion_finset
    (fun ε _ ε' _ hne => pairwise_disjoint_atom B hne) fun ε _ => measurableSet_atom hB ε

namespace IsPoissonPointProcess

variable {N : Ω → Measure S} {μ : Measure S} {P : Measure Ω}

/-- Joint law of arbitrary counts (a). -/
theorem map_count_vec (h : IsPoissonPointProcess N μ P) {l : ℕ} {B : Fin l → Set S}
    (hB : ∀ i, MeasurableSet (B i)) :
    P.map (fun ω i => N ω (B i)) =
      (Measure.pi fun ε : Fin l → Bool => extPoissonMeasure (μ (atom B ε))).map (sumMap l) := by
  have hf : Measurable fun ω (ε : Fin l → Bool) => N ω (atom B ε) :=
    Measurable.of_eval fun ε => h.measurable_count (measurableSet_atom hB ε)
  have hg : (fun ω i => N ω (B i)) = sumMap l ∘ fun ω (ε : Fin l → Bool) => N ω (atom B ε) := by
    ext ω i
    exact measure_eq_sum_atom hB (N ω) i
  rw [hg, ← Measure.map_map (measurable_sumMap l) hf,
    h.map_counts_fintype (measurableSet_atom hB) (pairwise_disjoint_atom B)]

theorem map_comp (hN : Measurable N) {β : Type*} [MeasurableSpace β] {g : Measure S → β}
    (hg : Measurable g) : P.map (fun ω => g (N ω)) = (P.map N).map g :=
  (Measure.map_map hg hN).symm

/-- Joint law of arbitrary counts (b), law form: any random measure with the same law is a PPP. -/
theorem of_map_eq (h : IsPoissonPointProcess N μ P) {N' : Ω' → Measure S} {P' : Measure Ω'}
    (hN' : Measurable N') (hlaw : P'.map N' = P.map N) : IsPoissonPointProcess N' μ P' := by
  refine ⟨hN', ?_, ?_⟩
  · intro A hA
    rw [map_comp hN' (Measure.measurable_coe hA), hlaw,
      ← map_comp h.measurable (Measure.measurable_coe hA), h.map_count hA]
  · intro n A hA hd
    have hg : Measurable fun (ν : Measure S) (j : Fin n) => ν (A j) :=
      Measurable.of_eval fun j => Measure.measurable_coe (hA j)
    rw [map_comp hN' hg, hlaw, ← map_comp h.measurable hg]
    exact h.2.2 n A hA hd

/-- Joint law of arbitrary counts (b), a.s. form. -/
theorem of_ae_eq (h : IsPoissonPointProcess N μ P) {N' : Ω → Measure S} (hN' : Measurable N')
    (hae : N' =ᵐ[P] N) : IsPoissonPointProcess N' μ P :=
  h.of_map_eq hN' (Measure.map_congr hae)

/-- Uniqueness in law: uniqueness in law. -/
theorem map_eq_map (h : IsPoissonPointProcess N μ P) {N' : Ω' → Measure S} {P' : Measure Ω'}
    (h' : IsPoissonPointProcess N' μ P') : P'.map N' = P.map N := by
  have := h.isProbabilityMeasure
  have := h'.isProbabilityMeasure
  refine ext_of_generate_finite (countEvents S) generateFrom_countEvents.symm
    isPiSystem_countEvents ?_ ?_
  · rintro _ ⟨l, B, C, hB, hC, rfl⟩
    have e1 := h'.map_count_vec hB
    have e2 := h.map_count_vec hB
    have hm : MeasurableSet ((fun (ν : Measure S) i => ν (B i)) ⁻¹' C) :=
      measurable_countVec hB hC
    show (P'.map N') ((fun (ν : Measure S) i => ν (B i)) ⁻¹' C) =
      (P.map N) ((fun (ν : Measure S) i => ν (B i)) ⁻¹' C)
    rw [Measure.map_apply h'.measurable hm, Measure.map_apply h.measurable hm]
    have a1 : P' (N' ⁻¹' ((fun (ν : Measure S) i => ν (B i)) ⁻¹' C)) =
        (P'.map fun ω i => N' ω (B i)) C := by
      rw [Measure.map_apply (Measurable.of_eval fun i => h'.measurable_count (hB i)) hC]; rfl
    have a2 : P (N ⁻¹' ((fun (ν : Measure S) i => ν (B i)) ⁻¹' C)) =
        (P.map fun ω i => N ω (B i)) C := by
      rw [Measure.map_apply (Measurable.of_eval fun i => h.measurable_count (hB i)) hC]; rfl
    rw [a1, a2, e1, e2]
  · simp [Measure.map_apply h'.measurable MeasurableSet.univ,
      Measure.map_apply h.measurable MeasurableSet.univ]

end IsPoissonPointProcess

end ElboimSly
