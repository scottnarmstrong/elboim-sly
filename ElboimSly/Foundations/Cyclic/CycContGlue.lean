/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycRegenLawMeas
public import ElboimSly.Foundations.Cyclic.CycRegenCut
public import ElboimSly.Foundations.Cyclic.CycThitDriven
public import ElboimSly.Foundations.Cyclic.CycDrivenRegenMeas
public import Mathlib

/-!
# Gluing a first piece to a sequence of pieces

Plan-level coupling after a stopping time (d), proof ("the construction of regenerated cyclic walk is a measurable
map `G` of the sequence of pieces").

* `contPieces p q`: the sequence of pieces `p, q 0, q 1, …`;
* `contGlue b p q`: the regenerated walk built from these pieces, glued at the partial sums of the
  closing times `pathTreg b`;
* `measurable_contGlue_at`: `(p, q) ↦ contGlue b p q t` is measurable for the product
  `σ`-algebras on path space (the regeneration times lie in `b ℕ ∪ {∞}`, so the pieces are only
  evaluated at countably many shifts).
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

variable {d : ℕ}

/-- The pieces `p, q 0, q 1, …`. -/
def contPieces (p : ℝ≥0 → Fin d → ℤ) (q : ℕ → ℝ≥0 → Fin d → ℤ) : ℕ → ℝ≥0 → Fin d → ℤ
  | 0 => p
  | k + 1 => q k

/-- The walk glued from the first piece `p` and the further pieces `q k`, at the partial sums of
their closing times `pathTreg b`. -/
noncomputable def contGlue (b : ℝ≥0) (p : ℝ≥0 → Fin d → ℤ) (q : ℕ → ℝ≥0 → Fin d → ℤ) :
    ℝ≥0 → Fin d → ℤ :=
  gluedWalk (partialSums fun k => pathTreg b (contPieces p q k)) (contPieces p q)

theorem measurable_pathTreg (b : ℝ≥0) :
    Measurable (pathTreg b : (ℝ≥0 → Fin d → ℤ) → ℝ≥0∞) := by
  refine measurable_of_Iic fun c => ?_
  rcases eq_or_ne c ⊤ with rfl | hc
  · simp
  lift c to ℝ≥0 using hc
  have : {p : ℝ≥0 → Fin d → ℤ | pathTreg b p ≤ c} =
      ⋃ k : ℕ, {p | 1 ≤ k ∧ (k : ℝ≥0) * b ≤ c ∧ p (k * b) = 0} := by
    ext p
    simp only [mem_ofPred_eq, mem_iUnion, pathTreg_le_iff]
    constructor
    · rintro ⟨k, h1, h2, h3⟩; exact ⟨k, h1, h3, h2⟩
    · rintro ⟨k, h1, h3, h2⟩; exact ⟨k, h1, h2, h3⟩
  show MeasurableSet {p : ℝ≥0 → Fin d → ℤ | pathTreg b p ≤ c}
  rw [this]
  refine MeasurableSet.iUnion fun k => ?_
  by_cases h : 1 ≤ k ∧ (k : ℝ≥0) * b ≤ c
  · have : {p : ℝ≥0 → Fin d → ℤ | 1 ≤ k ∧ (k : ℝ≥0) * b ≤ c ∧ p (k * b) = 0} =
        {p | p (k * b) = 0} := by
      ext p; simp [h]
    rw [this]
    exact measurableSet_eq_fun (measurable_pi_apply _) measurable_const
  · have : {p : ℝ≥0 → Fin d → ℤ | 1 ≤ k ∧ (k : ℝ≥0) * b ≤ c ∧ p (k * b) = 0} = ∅ := by
      ext p
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
      tauto
    rw [this]
    exact MeasurableSet.empty

theorem measurable_contPieces (n : ℕ) :
    Measurable fun x : (ℝ≥0 → Fin d → ℤ) × (ℕ → ℝ≥0 → Fin d → ℤ) => contPieces x.1 x.2 n := by
  cases n with
  | zero => exact measurable_fst
  | succ k => exact (measurable_pi_apply k).comp measurable_snd

theorem measurable_contSigma (b : ℝ≥0) (n : ℕ) :
    Measurable fun x : (ℝ≥0 → Fin d → ℤ) × (ℕ → ℝ≥0 → Fin d → ℤ) =>
      partialSums (fun k => pathTreg b (contPieces x.1 x.2 k)) n :=
  Finset.measurable_sum _ fun k _ => (measurable_pathTreg b).comp (measurable_contPieces k)

theorem partialSums_toNNReal_mem (b : ℝ≥0) (τ : ℕ → ℝ≥0∞)
    (hτ : ∀ k, τ k = ⊤ ∨ ∃ j : ℕ, τ k = (((j : ℝ≥0) * b : ℝ≥0) : ℝ≥0∞)) (n : ℕ) :
    ∃ k : ℕ, (partialSums τ n).toNNReal = (k : ℝ≥0) * b := by
  induction n with
  | zero => exact ⟨0, by simp [partialSums]⟩
  | succ n ih =>
    rw [partialSums_succ]
    obtain ⟨k, hk⟩ := ih
    by_cases hp : partialSums τ n = ⊤
    · exact ⟨0, by simp [hp]⟩
    rcases hτ n with h | ⟨j, hj⟩
    · exact ⟨0, by simp [h]⟩
    · refine ⟨k + j, ?_⟩
      rw [ENNReal.toNNReal_add hp (by rw [hj]; exact ENNReal.coe_ne_top), hk, hj]
      simp [add_mul]

theorem measurable_eval_countable {X : Type*} [MeasurableSpace X] {F : X → ℝ≥0 → Fin d → ℤ}
    (hF : Measurable F) {g : X → ℝ≥0} (hg : Measurable g) {S : Set ℝ≥0} (hS : S.Countable)
    (hgS : ∀ x, g x ∈ S) : Measurable fun x => F x (g x) := by
  have : Countable S := hS.to_subtype
  have h1 : Measurable fun x : X => (⟨g x, hgS x⟩ : S) := hg.subtype_mk
  have h2 : Measurable fun q : X × S => F q.1 q.2 :=
    measurable_from_prod_countable_left (f := fun q : X × S => F q.1 q.2)
      fun s => (measurable_pi_apply (s : ℝ≥0)).comp hF
  exact h2.comp (measurable_id.prodMk h1)

theorem measurable_contGlue_at {b : ℝ≥0} (t : ℝ≥0) :
    Measurable fun x : (ℝ≥0 → Fin d → ℤ) × (ℕ → ℝ≥0 → Fin d → ℤ) => contGlue b x.1 x.2 t := by
  have hσ := measurable_contSigma (d := d) b
  have hF : ∀ n, Measurable fun x : (ℝ≥0 → Fin d → ℤ) × (ℕ → ℝ≥0 → Fin d → ℤ) =>
      contPieces x.1 x.2 n (t - (partialSums (fun k => pathTreg b (contPieces x.1 x.2 k))
        n).toNNReal) := by
    intro n
    refine measurable_eval_countable (measurable_contPieces n)
      (g := fun x => t - (partialSums (fun k => pathTreg b (contPieces x.1 x.2 k)) n).toNNReal)
      (measurable_const.sub (ENNReal.measurable_toNNReal.comp (hσ n)))
      (S := Set.range fun k : ℕ => t - (k : ℝ≥0) * b) (Set.countable_range _) fun x => ?_
    have hτ : ∀ k, pathTreg b (contPieces x.1 x.2 k) = ⊤ ∨
        ∃ j : ℕ, pathTreg b (contPieces x.1 x.2 k) = (((j : ℝ≥0) * b : ℝ≥0) : ℝ≥0∞) := fun k => by
      rcases pathTreg_top_or b (contPieces x.1 x.2 k) with h | ⟨j, -, hj, -⟩
      · exact Or.inl h
      · exact Or.inr ⟨j, hj⟩
    obtain ⟨k, hk⟩ := partialSums_toNNReal_mem b
      (fun k => pathTreg b (contPieces x.1 x.2 k)) hτ n
    exact ⟨k, by simp only [hk]⟩
  exact measurable_index (measurable_gluedCount_of hσ t) hF

end ElboimSly.Cyclic

end
