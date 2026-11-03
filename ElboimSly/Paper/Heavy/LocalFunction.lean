/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.PPP.Restriction
public import ElboimSly.Foundations.PPP.Giry
public import ElboimSly.Foundations.PPP.Law
public import Mathlib

/-!
# A local event of a Poisson point process is a function of the restriction

Goodness is local; independence at distance (c), in abstract form.

Let `N` be a Poisson point process on `S` with intensity `μ` and let `A ⊆ S` be measurable.
Let `F` be a measurable set of measures such that membership in `F` is *local on `A`* for the
measures in a measurable set `Gd` of full probability: if `ν, ν' ∈ Gd` and `ν|_A = ν'|_A`, then
`ν ∈ F ↔ ν' ∈ F`.  Then there is a measurable `G` with
`{N ∈ F} = {N|_A ∈ G}` almost surely.

The proof is the freezing argument of the written proof: `X = N|_A` and `Y = N|_{Aᶜ}` are independent,
`N = X + Y`, so the joint law is a product `μ_X ⊗ μ_Y`.  For `μ_X`-a.e. `x` the section
`y ↦ 1_F(x + y)` is `μ_Y`-a.e. constant, by locality; `G` is the set of `x` for which the section
is `1`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace ElboimSly.Paper.Heavy

open ElboimSly

variable {S : Type*} [MeasurableSpace S] {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {N : Ω → Measure S} {μ : Measure S}

/-- Goodness is local; independence at distance (c), abstract form. -/
theorem exists_measurable_set_of_local (hN : IsPoissonPointProcess N μ P) {A : Set S}
    (hA : MeasurableSet A) {F Gd : Set (Measure S)} (hF : MeasurableSet F)
    (hGd : MeasurableSet Gd) (hgood : ∀ᵐ ω ∂P, N ω ∈ Gd)
    (hloc : ∀ ν ∈ Gd, ∀ ν' ∈ Gd, ν.restrict A = ν'.restrict A → (ν ∈ F ↔ ν' ∈ F)) :
    ∃ G : Set (Measure S), MeasurableSet G ∧
      ∀ᵐ ω ∂P, (N ω ∈ F ↔ (N ω).restrict A ∈ G) := by
  have := hN.isProbabilityMeasure
  have hAc : MeasurableSet Aᶜ := hA.compl
  set X : Ω → Measure S := fun ω => (N ω).restrict A with hXdef
  set Y : Ω → Measure S := fun ω => (N ω).restrict Aᶜ with hYdef
  have hX : Measurable X := (measurable_restrict_measure hA).comp hN.measurable
  have hY : Measurable Y := (measurable_restrict_measure hAc).comp hN.measurable
  have hind : IndepFun X Y P := hN.indepFun_restrict hA hAc disjoint_compl_right
  have hjoint : P.map (fun ω => (X ω, Y ω)) = (P.map X).prod (P.map Y) :=
    (indepFun_iff_map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable).1 hind
  have : IsProbabilityMeasure (P.map Y) := inferInstance
  have : IsProbabilityMeasure (P.map X) := inferInstance
  have hsum : ∀ ω, X ω + Y ω = N ω := fun ω => Measure.restrict_add_restrict_compl hA
  -- the sets in the product of the two laws
  let Fset : Set (Measure S × Measure S) := {p | p.1 + p.2 ∈ F}
  have hFset : MeasurableSet Fset := measurable_add_measure hF
  let Cset : Set (Measure S × Measure S) := {p | p.1 + p.2 ∈ Gd ∧ p.2.restrict A = 0}
  have hCset : MeasurableSet Cset := by
    refine (measurable_add_measure hGd).inter ?_
    have : Measurable fun y : Measure S => y.restrict A univ :=
      Measure.measurable_coe MeasurableSet.univ |>.comp (measurable_restrict_measure hA)
    have h2 : MeasurableSet {y : Measure S | y.restrict A univ = 0} :=
      this (measurableSet_singleton 0)
    have : {p : Measure S × Measure S | p.2.restrict A = 0} =
        {p | p.2.restrict A univ = 0} := by
      ext p; simp
    show MeasurableSet {p : Measure S × Measure S | p.2.restrict A = 0}
    rw [this]
    exact measurable_snd h2
  have hCae : ∀ᵐ p ∂((P.map X).prod (P.map Y)), p ∈ Cset := by
    rw [← hjoint]
    refine ae_map_iff (hX.prodMk hY).aemeasurable hCset |>.2 ?_
    filter_upwards [hgood] with ω hω
    refine ⟨by simpa [hsum ω] using hω, ?_⟩
    simp only [hYdef]
    rw [Measure.restrict_restrict hA, Set.inter_compl_self, Measure.restrict_empty]
  have hCx : ∀ᵐ x ∂(P.map X), ∀ᵐ y ∂(P.map Y), (x, y) ∈ Cset := Measure.ae_ae_of_ae_prod hCae
  -- the set `G`
  set G : Set (Measure S) := {x | 0 < (P.map Y) (Prod.mk x ⁻¹' Fset)} with hGdef
  have hG : MeasurableSet G :=
    measurableSet_lt measurable_const (measurable_measure_prodMk_left hFset)
  refine ⟨G, hG, ?_⟩
  -- the sectionwise statement
  have hsec : ∀ᵐ x ∂(P.map X), ∀ᵐ y ∂(P.map Y), (x + y ∈ F ↔ x ∈ G) := by
    filter_upwards [hCx] with x hx
    have hx' : (P.map Y) {y | (x, y) ∈ Cset}ᶜ = 0 := ae_iff.1 hx
    have hpos : 0 < (P.map Y) {y | (x, y) ∈ Cset} := by
      by_contra hneg
      have h0 : (P.map Y) {y | (x, y) ∈ Cset} = 0 := by simpa using hneg
      have := measure_univ_le_add_compl (μ := P.map Y) {y | (x, y) ∈ Cset}
      rw [h0, hx', add_zero, measure_univ] at this
      exact absurd this (by simp)
    -- locality on the section
    have hsame : ∀ y, (x, y) ∈ Cset → ∀ y', (x, y') ∈ Cset → (x + y ∈ F ↔ x + y' ∈ F) := by
      intro y hy y' hy'
      refine hloc _ hy.1 _ hy'.1 ?_
      rw [Measure.restrict_add, Measure.restrict_add, hy.2, hy'.2]
    filter_upwards [hx] with y hy
    constructor
    · intro hyF
      show 0 < (P.map Y) (Prod.mk x ⁻¹' Fset)
      refine lt_of_lt_of_le hpos (measure_mono fun y' hy' => ?_)
      exact (hsame y hy y' hy').1 hyF
    · intro hxG
      by_contra hnot
      have hsub : Prod.mk x ⁻¹' Fset ⊆ {y | (x, y) ∈ Cset}ᶜ := by
        intro y' hy' hy'C
        exact hnot ((hsame y hy y' hy'C).2 hy')
      have : (P.map Y) (Prod.mk x ⁻¹' Fset) = 0 := measure_mono_null hsub hx'
      exact absurd hxG (by simp [hGdef, this])
  have hprod : ∀ᵐ p ∂((P.map X).prod (P.map Y)), (p.1 + p.2 ∈ F ↔ p.1 ∈ G) := by
    rw [Measure.ae_prod_iff_ae_ae]
    · exact hsec
    · have h1 : MeasurableSet {p : Measure S × Measure S | p.1 + p.2 ∈ F} := hFset
      have h2 : MeasurableSet {p : Measure S × Measure S | p.1 ∈ G} := measurable_fst hG
      have : {p : Measure S × Measure S | (p.1 + p.2 ∈ F ↔ p.1 ∈ G)} =
          ({p | p.1 + p.2 ∈ F} ∩ {p | p.1 ∈ G}) ∪ ({p | p.1 + p.2 ∈ F}ᶜ ∩ {p | p.1 ∈ G}ᶜ) := by
        ext p; simp only [mem_ofPred_eq, mem_union, mem_inter_iff, mem_compl_iff]; tauto
      show MeasurableSet {p : Measure S × Measure S | (p.1 + p.2 ∈ F ↔ p.1 ∈ G)}
      rw [this]
      exact (h1.inter h2).union (h1.compl.inter h2.compl)
  rw [← hjoint] at hprod
  filter_upwards [ae_of_ae_map (hX.prodMk hY).aemeasurable hprod] with ω hω
  simpa [hsum ω] using hω

end ElboimSly.Paper.Heavy
