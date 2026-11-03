/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.StrongApprox.X1Err1
public import ElboimSly.Foundations.StrongApprox.Increments
public import Mathlib

/-!
# Pathwise identities in the coupling space

Laws in the coupling (d) (Part II).

On the event that all clocks are finite, `∑_{i ≤ j} X^k_i = β^k(T^k_{j+1})` and
`∑_{i ≤ j} Y^k_i = β^k(j+1)`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace ElboimSly.StrongApprox

open ElboimSly.Brownian

variable {d ℓ : ℕ}

lemma sum_filter_le_range {α : Type*} [AddCommMonoid α] (f : ℕ → α) (j : Fin ℓ) :
    ∑ i ∈ Finset.univ.filter (· ≤ j), f (i : ℕ) = ∑ n ∈ Finset.range ((j : ℕ) + 1), f n := by
  have : (Finset.univ.filter (· ≤ j)).map Fin.valEmbedding = Finset.range ((j : ℕ) + 1) := by
    ext n
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Fin.valEmbedding_apply,
      Finset.mem_range]
    constructor
    · rintro ⟨i, hi, rfl⟩
      have : (i : ℕ) ≤ j := hi
      omega
    · intro hn
      refine ⟨⟨n, by omega⟩, ?_, rfl⟩
      show n ≤ (j : ℕ)
      omega
  rw [← this, Finset.sum_map]
  rfl

/-- The path of the `k`-th coordinate, as a function of the second component. -/
noncomputable def pathK (k : Fin d) (ω : Ω1 d ℓ) : ℝ≥0 → ℝ := fun t => Bd d t ω.2 k

lemma isC0_pathK (k : Fin d) (ω : Ω1 d ℓ) : IsC0 (pathK k ω) :=
  (isProcess_of_realBM (isStandardRealBM_Bd_coord d k)).1 ω.2

/-- The clock `T^k_j` of coordinate `k`. -/
noncomputable def clockK (k : Fin d) (ω : Ω1 d ℓ) (j : ℕ) : ℝ≥0∞ :=
  embClock (rr ℓ ω.1 k) (pathK k ω) j

lemma Vfull_fst (k : Fin d) (ω : Ω1 d ℓ) (i : Fin ℓ) :
    (Vfull ℓ ω k i).1 = embX (rr ℓ ω.1 k) (pathK k ω) i := rfl

lemma Vfull_snd (k : Fin d) (ω : Ω1 d ℓ) (i : Fin ℓ) :
    (Vfull ℓ ω k i).2 = embTau (rr ℓ ω.1 k) (pathK k ω) i := rfl

/-- `∑_{i ≤ j} X^k_i = β^k(T^k_{j+1})` when the clock is finite. -/
lemma sum_X_eq (k : Fin d) (ω : Ω1 d ℓ) (j : Fin ℓ) (hfin : clockK k ω ((j : ℕ) + 1) < ⊤) :
    ∑ i ∈ Finset.univ.filter (· ≤ j), (Vfull ℓ ω k i).1 =
      Bd d (clockK k ω ((j : ℕ) + 1)).toNNReal ω.2 k := by
  have h := (embClock_spec (isC0_pathK k ω) (rr ℓ ω.1 k) ((j : ℕ) + 1) hfin).2
  have e := sum_filter_le_range (fun n => embX (rr ℓ ω.1 k) (pathK k ω) n) j
  simp only [Vfull_fst]
  rw [e, h]
  rfl

/-- `∑_{i ≤ j} (B(i+1) - B(i))_k = B(j+1)_k`. -/
lemma sum_Y_eq (k : Fin d) (ω : Ω1 d ℓ) (j : Fin ℓ) :
    ∑ i ∈ Finset.univ.filter (· ≤ j), unitIncr (Bd d) ℓ ω.2 i k =
      Bd d (((j : ℕ) + 1 : ℕ) : ℝ≥0) ω.2 k := by
  have e := sum_filter_le_range (fun n : ℕ => Bd d ((n : ℝ≥0) + 1) ω.2 k - Bd d (n : ℝ≥0) ω.2 k) j
  have h0 : Bd d 0 ω.2 k = 0 := by
    have := (isC0_pathK (ℓ := ℓ) k ω).2
    simpa [pathK] using this
  have tele := Finset.sum_range_sub (fun n : ℕ => Bd d (n : ℝ≥0) ω.2 k) ((j : ℕ) + 1)
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero] at tele ⊢
  simp only [unitIncr, Pi.sub_apply]
  rw [e, tele, h0, sub_zero]

/-- `∑_{i ≤ j} (τ^k_i - 1) = T^k_{j+1} - (j+1)` when the clocks are finite. -/
lemma sum_tau_eq (k : Fin d) (ω : Ω1 d ℓ) (j : Fin ℓ)
    (hfin : ∀ i : Fin ℓ, (Vfull ℓ ω k i).2 < ⊤) :
    ∑ i ∈ Finset.univ.filter (· ≤ j), ((Vfull ℓ ω k i).2.toReal - 1) =
      (clockK k ω ((j : ℕ) + 1)).toReal - ((j : ℕ) + 1) := by
  have hfin' : ∀ n < ℓ, embTau (rr ℓ ω.1 k) (pathK k ω) n < ⊤ := fun n hn => hfin ⟨n, hn⟩
  have hjℓ : (j : ℕ) + 1 ≤ ℓ := j.2
  have e := sum_filter_le_range
    (fun n => (embTau (rr ℓ ω.1 k) (pathK k ω) n).toReal - 1) j
  simp only [Vfull_snd]
  have hsum : ∑ n ∈ Finset.range ((j : ℕ) + 1), (embTau (rr ℓ ω.1 k) (pathK k ω) n).toReal =
      (clockK k ω ((j : ℕ) + 1)).toReal := by
    rw [clockK, embClock, ENNReal.toReal_sum]
    intro n hn
    exact (hfin' n (by have := Finset.mem_range.1 hn; omega)).ne
  rw [e, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one,
    hsum]
  push_cast
  ring

end ElboimSly.StrongApprox
