/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycMultiDef
public import ElboimSly.Foundations.Cyclic.CycSchemeEquiv
public import ElboimSly.Foundations.PPP.Simple
public import ElboimSly.Foundations.PPP.DissectingExamples
public import ElboimSly.Foundations.PPP.Finite
public import Mathlib

/-!
# Several walks explored one after another (a), Step 3: counting measures and eventual agreement

Several walks explored one after another (a), Step 3. A `PPP(μ)` on `𝒮 = I × Ed × 𝕋` is almost
surely a simple counting measure: `N(A) = #(A ∩ atoms N)` for every measurable `A`
(`ae_cyc_count`). If a family of sets `Z s` is monotone and right-continuous, then
`(N|_{Z(s)ᶜ} + N'|_{Z(s)})(B)` is eventually constant as `s ↓ s₀` when `N(B), N'(B) < ∞`
(`eventually_tilde_apply`).
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

variable {I : Type*} [MeasurableSpace I] [Countable I] [MeasurableSingletonClass I] {d : ℕ}
  {β : ℝ} [Fact (0 < β)]

/-- A `PPP(# ⊗ μ_β)` is almost surely a simple counting measure. -/
theorem ae_cyc_count {Ω : Type*} [MeasurableSpace Ω] {Pr : Measure Ω}
    {N : Ω → Measure (CycS I d β)} (hN : IsPoissonPointProcess N (cycIntensity I d β) Pr) :
    ∀ᵐ ω ∂Pr, ∃ a : Set (CycS I d β), ∀ A : Set (CycS I d β), MeasurableSet A →
      N ω A = (A ∩ a).encard := by
  have hD : (SepPartSeq.prodCount I (ringSeq (Edge d) β)).IsDissecting
      (cycIntensity I d β) :=
    SepPartSeq.prodCount_isDissecting (ringSeq (Edge d) β) (ringIntensity d β)
      (ringSeq_isDissecting (Edge d) β)
  have hdiff : ∀ x, cycIntensity I d β {x} = 0 := fun x => by
    have : ({x} : Set (CycS I d β)) = {x.1} ×ˢ {x.2} := by
      ext ⟨a, b⟩; simp [Prod.ext_iff]
    rw [this]
    show ((Measure.count : Measure I).prod (ringIntensity d β)) _ = 0
    rw [Measure.prod_prod]
    have h2 : ringIntensity d β {x.2} = 0 := ring_singleton (Edge d) β x.2
    rw [h2, mul_zero]
  filter_upwards [hN.ae_mem_bSimple _ hD hdiff] with ω hω
  exact ⟨SepPartSeq.atoms (N ω), (SepPartSeq.structure_of_mem_bSimple hω).2.2.2⟩

/-- If `N, N'` are counting measures with finitely many atoms in `B`, and `Z` is monotone and
right-continuous, then `(N|_{Z(s)ᶜ} + N'|_{Z(s)})(B)` is eventually constant as `s_m ↓ s₀`. -/
theorem eventually_tilde_apply {S : Type*} [MeasurableSpace S] (Z : ℝ≥0 → Set S)
    (hZm : ∀ s, MeasurableSet (Z s)) (hmono : Monotone Z)
    (hrc : ∀ s0 x, (∀ s, s0 < s → x ∈ Z s) → x ∈ Z s0)
    (N N' : Measure S) (a a' : Set S)
    (hN : ∀ A, MeasurableSet A → N A = (A ∩ a).encard)
    (hN' : ∀ A, MeasurableSet A → N' A = (A ∩ a').encard)
    {B : Set S} (hB : MeasurableSet B) (hfin : N B ≠ ⊤) (hfin' : N' B ≠ ⊤)
    (s0 : ℝ≥0) (sm : ℕ → ℝ≥0) (h1 : ∀ m, s0 ≤ sm m)
    (h2 : ∀ s, s0 < s → ∀ᶠ m in atTop, sm m ≤ s) :
    ∀ᶠ m in atTop, (N.restrict (Z (sm m))ᶜ + N'.restrict (Z (sm m))) B =
      (N.restrict (Z s0)ᶜ + N'.restrict (Z s0)) B := by
  have hfa : (B ∩ a).Finite := by
    refine Set.encard_ne_top_iff.1 fun h => hfin ?_
    rw [hN B hB, h]; rfl
  have hfa' : (B ∩ a').Finite := by
    refine Set.encard_ne_top_iff.1 fun h => hfin' ?_
    rw [hN' B hB, h]; rfl
  have hW : (B ∩ a ∪ B ∩ a').Finite := hfa.union hfa'
  have hx : ∀ x, ∀ᶠ m in atTop, (x ∈ Z (sm m) ↔ x ∈ Z s0) := fun x => by
    by_cases hx : x ∈ Z s0
    · exact Eventually.of_forall fun m => ⟨fun _ => hx, fun _ => hmono (h1 m) hx⟩
    · have : ¬ ∀ s, s0 < s → x ∈ Z s := fun h => hx (hrc s0 x h)
      push Not at this
      obtain ⟨s, hs, hxs⟩ := this
      filter_upwards [h2 s hs] with m hm
      exact ⟨fun h => absurd (hmono hm h) hxs, fun h => absurd h hx⟩
  have hall := (Filter.eventually_all_finite hW).2 fun x _ => hx x
  filter_upwards [hall] with m hm
  simp only [Measure.add_apply, Measure.restrict_apply hB]
  rw [hN _ (hB.inter (hZm _).compl), hN' _ (hB.inter (hZm _)),
    hN _ (hB.inter (hZm _).compl), hN' _ (hB.inter (hZm _))]
  have e1 : (B ∩ (Z (sm m))ᶜ) ∩ a = (B ∩ (Z s0)ᶜ) ∩ a := by
    ext x
    simp only [mem_inter_iff, mem_compl_iff]
    constructor
    · rintro ⟨⟨hxB, hxZ⟩, hxa⟩
      exact ⟨⟨hxB, fun h => hxZ ((hm x (Or.inl ⟨hxB, hxa⟩)).2 h)⟩, hxa⟩
    · rintro ⟨⟨hxB, hxZ⟩, hxa⟩
      exact ⟨⟨hxB, fun h => hxZ ((hm x (Or.inl ⟨hxB, hxa⟩)).1 h)⟩, hxa⟩
  have e2 : (B ∩ Z (sm m)) ∩ a' = (B ∩ Z s0) ∩ a' := by
    ext x
    simp only [mem_inter_iff]
    constructor
    · rintro ⟨⟨hxB, hxZ⟩, hxa⟩
      exact ⟨⟨hxB, (hm x (Or.inr ⟨hxB, hxa⟩)).1 hxZ⟩, hxa⟩
    · rintro ⟨⟨hxB, hxZ⟩, hxa⟩
      exact ⟨⟨hxB, (hm x (Or.inr ⟨hxB, hxa⟩)).2 hxZ⟩, hxa⟩
  rw [e1, e2]

end ElboimSly.Cyclic

end
