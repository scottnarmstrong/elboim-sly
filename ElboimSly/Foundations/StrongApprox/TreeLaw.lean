/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.StrongApprox.DyadicTree
public import Mathlib.Probability.Distributions.Poisson.Basic
public import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Laws in the dyadic tree: the structural step

Laws in the tree. Concatenation of two independent i.i.d. vectors is an i.i.d. vector,
and a split step that maps `ν' ⊗ 𝒩(0,1)` to `ν ⊗ ν` propagates the i.i.d. law of the leaves from the
children to the parent. The reindexing of the written proof through `finSumFinEquiv` and
`piCongrLeft` is replaced by the recursive description of the tree.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set

namespace ElboimSly
namespace StrongApprox

/-- Concatenation of two vectors of lengths `a` and `b` into a vector of length `c = a + b`. -/
def cat {α : Type*} (a b c : ℕ) (h : a + b = c) (x : (Fin a → α) × (Fin b → α)) : Fin c → α :=
  fun i => if hi : (i : ℕ) < a then x.1 ⟨i, hi⟩ else x.2 ⟨i - a, by omega⟩

variable {α : Type*} [MeasurableSpace α]

theorem measurable_cat (a b c : ℕ) (h : a + b = c) : Measurable (cat (α := α) a b c h) := by
  refine Measurable.of_eval fun i => ?_
  unfold cat
  by_cases h : (i : ℕ) < a
  · simp only [h, dite_true]
    exact (measurable_pi_apply _).comp measurable_fst
  · simp only [h, dite_false]
    exact (measurable_pi_apply _).comp measurable_snd

/-- Concatenating two independent i.i.d. vectors gives an i.i.d. vector. -/
theorem measurePreserving_cat (μ : Measure α) [IsProbabilityMeasure μ] (a b c : ℕ)
    (h : a + b = c) :
    MeasurePreserving (cat (α := α) a b c h)
      ((Measure.pi fun _ : Fin a => μ).prod (Measure.pi fun _ : Fin b => μ))
      (Measure.pi fun _ : Fin c => μ) := by
  have hm := measurable_cat (α := α) a b c h
  subst h
  refine ⟨hm, ?_⟩
  symm
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.map_apply hm (MeasurableSet.univ_pi hs)]
  have : cat (α := α) a b (a + b) rfl ⁻¹' (Set.univ.pi s) =
      (Set.univ.pi fun i : Fin a => s (Fin.castAdd b i)) ×ˢ
        (Set.univ.pi fun i : Fin b => s (Fin.natAdd a i)) := by
    ext x
    simp only [mem_preimage, mem_pi, mem_univ, forall_true_left, mem_prod]
    rw [Fin.forall_fin_add]
    have h1 : ∀ i : Fin a, cat (α := α) a b (a + b) rfl x (Fin.castAdd b i) = x.1 i := by
      intro i; simp [cat]
    have h2 : ∀ i : Fin b, cat (α := α) a b (a + b) rfl x (Fin.natAdd a i) = x.2 i := by
      intro i; simp [cat]
    simp only [h1, h2]
  rw [this, Measure.prod_prod, Measure.pi_pi, Measure.pi_pi, Fin.prod_univ_add]

section Comm

variable {A B C D : Type*} [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
  [MeasurableSpace D]

/-- The rearrangement `((a, c), (b, d)) ↦ ((a, b), (c, d))` preserves product measures. -/
theorem measurePreserving_prodProdProdComm' (μa : Measure A) (μb : Measure B) (μc : Measure C)
    (μd : Measure D) [SFinite μa] [SFinite μb] [SFinite μc] [SFinite μd] :
    MeasurePreserving (fun p : (A × C) × (B × D) => ((p.1.1, p.2.1), (p.1.2, p.2.2)))
      ((μa.prod μc).prod (μb.prod μd)) ((μa.prod μb).prod (μc.prod μd)) := by
  have f1 := measurePreserving_prodAssoc μa μc (μb.prod μd)
  have f2 := (MeasurePreserving.id μa).prod
    (MeasurePreserving.symm _ (measurePreserving_prodAssoc μc μb μd))
  have f3 := (MeasurePreserving.id μa).prod
    ((Measure.measurePreserving_swap (μ := μc) (ν := μb)).prod (MeasurePreserving.id μd))
  have f4 := (MeasurePreserving.id μa).prod (measurePreserving_prodAssoc μb μc μd)
  have f5 := MeasurePreserving.symm _ (measurePreserving_prodAssoc μa μb (μc.prod μd))
  exact f5.comp (f4.comp (f3.comp (f2.comp f1)))

end Comm

section Step

variable {X : Type*} [MeasurableSpace X]

/-- The structural induction step for the law of the leaves of the tree. -/
theorem tree_step (n : ℕ) (ν' ν : Measure X) [IsProbabilityMeasure ν']
    [IsProbabilityMeasure ν] (ρ : Measure α) [IsProbabilityMeasure ρ]
    (split : X × ℝ → X × X)
    (hsplit : MeasurePreserving split (ν'.prod saN) (ν.prod ν))
    (L : X → DT n → Fin (2 ^ n) → α)
    (hL : MeasurePreserving (fun p : X × DT n => L p.1 p.2) (ν.prod (muDT n))
      (Measure.pi fun _ : Fin (2 ^ n) => ρ)) :
    MeasurePreserving
      (fun p : X × DT (n + 1) =>
        cat (2 ^ n) (2 ^ n) (2 ^ (n + 1)) (by ring)
          (L (split (p.1, p.2.1)).1 p.2.2.1, L (split (p.1, p.2.1)).2 p.2.2.2))
      (ν'.prod (muDT (n + 1))) (Measure.pi fun _ : Fin (2 ^ (n + 1)) => ρ) := by
  have e1 := measurePreserving_prodAssoc ν' saN ((muDT n).prod (muDT n))
  have e2 := (hsplit.prod (MeasurePreserving.id ((muDT n).prod (muDT n))))
  have e3 := measurePreserving_prodProdProdComm' ν (muDT n) ν (muDT n)
  have e4 := hL.prod hL
  have e5 := measurePreserving_cat ρ (2 ^ n) (2 ^ n) (2 ^ (n + 1)) (by ring)
  exact e5.comp (e4.comp (e3.comp (e2.comp (MeasurePreserving.symm _ e1))))

end Step

end StrongApprox
end ElboimSly
