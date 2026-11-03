/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import Mathlib

/-!
# Binomial weights and tails as explicit finite sums

Binomial law; Basic properties of the binomial law. The binomial law is handled through its
explicit finite sums: `concBinomWeight K p i` is `b_{K,p}(i)` for `i : ℤ`, and
`concBinomLE K p m = P(Bin(K,p) ≤ m)`, `concBinomGE K p m = P(Bin(K,p) ≥ m)`.
-/

public section

namespace ElboimSly

open Finset

/-- The binomial weight `b_{K,p}(i) = C(K,i) p^i (1-p)^(K-i)` for `0 ≤ i ≤ K`, and `0` otherwise.
Binomial law. -/
@[expose] noncomputable def concBinomWeight (K : ℕ) (p : ℝ) (i : ℤ) : ℝ :=
  if 0 ≤ i ∧ i ≤ K then (K.choose i.toNat : ℝ) * p ^ i.toNat * (1 - p) ^ (K - i.toNat) else 0

/-- The lower tail `P(Bin(K,p) ≤ m) = ∑_{i ≤ m} b_{K,p}(i)`. Binomial law. -/
@[expose] noncomputable def concBinomLE (K : ℕ) (p : ℝ) (m : ℤ) : ℝ :=
  ∑ i ∈ range (K + 1), if (i : ℤ) ≤ m then concBinomWeight K p i else 0

/-- The upper tail `P(Bin(K,p) ≥ m) = ∑_{i ≥ m} b_{K,p}(i)`. Binomial law. -/
@[expose] noncomputable def concBinomGE (K : ℕ) (p : ℝ) (m : ℤ) : ℝ :=
  ∑ i ∈ range (K + 1), if m ≤ (i : ℤ) then concBinomWeight K p i else 0

/-- The weight at a natural number, without the case distinction. -/
lemma concBinomWeight_natCast (K : ℕ) (p : ℝ) (i : ℕ) :
    concBinomWeight K p (i : ℤ) = (K.choose i : ℝ) * p ^ i * (1 - p) ^ (K - i) := by
  unfold concBinomWeight
  by_cases h : i ≤ K
  · simp [h]
  · have : K.choose i = 0 := Nat.choose_eq_zero_of_lt (by omega)
    simp [this]

lemma concBinomWeight_nonneg {K : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (i : ℤ) :
    0 ≤ concBinomWeight K p i := by
  unfold concBinomWeight
  split_ifs
  · have : 0 ≤ 1 - p := by linarith
    positivity
  · exact le_rfl

/-- Basic properties of the binomial law (a), the generating function. -/
lemma concBinomWeight_sum_mul_pow (K : ℕ) (p x : ℝ) :
    ∑ i ∈ range (K + 1), concBinomWeight K p i * x ^ i = (1 - p + p * x) ^ K := by
  rw [add_comm (1 - p), add_pow]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [concBinomWeight_natCast, mul_pow]
  ring

/-- Basic properties of the binomial law (a): the weights sum to one. -/
lemma concBinomWeight_sum_one (K : ℕ) (p : ℝ) :
    ∑ i ∈ range (K + 1), concBinomWeight K p i = 1 := by
  have := concBinomWeight_sum_mul_pow K p 1
  simpa using this

/-- Basic properties of the binomial law (b): vanishing below zero. -/
lemma concBinomLE_of_neg (K : ℕ) (p : ℝ) {m : ℤ} (hm : m < 0) : concBinomLE K p m = 0 := by
  unfold concBinomLE
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [ite_eq_right]
  omega

/-- Basic properties of the binomial law (b): equals one from `K` on. -/
lemma concBinomLE_of_ge (K : ℕ) (p : ℝ) {m : ℤ} (hm : (K : ℤ) ≤ m) : concBinomLE K p m = 1 := by
  unfold concBinomLE
  rw [← concBinomWeight_sum_one K p]
  refine Finset.sum_congr rfl fun i hi => ?_
  have : i < K + 1 := Finset.mem_range.1 hi
  rw [ite_eq_left]
  omega

/-- Basic properties of the binomial law (b): monotonicity in `m`. -/
lemma concBinomLE_mono {K : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : Monotone (concBinomLE K p) := by
  intro m m' h
  unfold concBinomLE
  refine Finset.sum_le_sum fun i _ => ?_
  by_cases h1 : (i : ℤ) ≤ m
  · rw [ite_eq_left h1, ite_eq_left (h1.trans h)]
  · rw [ite_eq_right h1]
    split_ifs
    · exact concBinomWeight_nonneg hp0 hp1 _
    · exact le_rfl

lemma concBinomLE_nonneg {K : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (m : ℤ) :
    0 ≤ concBinomLE K p m :=
  Finset.sum_nonneg fun i _ => by
    split_ifs
    · exact concBinomWeight_nonneg hp0 hp1 _
    · exact le_rfl

/-- Pascal's rule for the weights. -/
lemma concBinomWeight_pascal (K : ℕ) (p : ℝ) (i : ℕ) :
    concBinomWeight (K + 1) p ((i + 1 : ℕ) : ℤ) =
      p * concBinomWeight K p (i : ℤ) + (1 - p) * concBinomWeight K p ((i + 1 : ℕ) : ℤ) := by
  simp only [concBinomWeight_natCast]
  by_cases h : i < K
  · obtain ⟨t, rfl⟩ : ∃ t, K = i + 1 + t := ⟨K - (i + 1), by omega⟩
    have e1 : i + 1 + t + 1 - (i + 1) = t + 1 := by omega
    have e2 : i + 1 + t - i = t + 1 := by omega
    have e3 : i + 1 + t - (i + 1) = t := by omega
    rw [e1, e2, e3, Nat.choose_succ_succ]
    push_cast
    ring
  · rcases Nat.eq_or_lt_of_le (not_lt.1 h) with hK | hK
    · subst hK
      simp [Nat.choose_succ_self]
      ring
    · have h1 : K.choose i = 0 := Nat.choose_eq_zero_of_lt hK
      have h2 : K.choose (i + 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
      have h3 : (K + 1).choose (i + 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
      simp [h1, h2, h3]

/-- Basic properties of the binomial law (c), recursion. -/
lemma concBinomLE_succ (K : ℕ) (p : ℝ) (m : ℤ) :
    concBinomLE (K + 1) p m = (1 - p) * concBinomLE K p m + p * concBinomLE K p (m - 1) := by
  unfold concBinomLE
  rw [Finset.sum_range_succ' _ (K + 1)]
  have hL : ∀ i ∈ range (K + 1),
      (if ((i + 1 : ℕ) : ℤ) ≤ m then concBinomWeight (K + 1) p ((i + 1 : ℕ) : ℤ) else 0) =
        (if (i : ℤ) ≤ m - 1 then p * concBinomWeight K p (i : ℤ) else 0) +
        (if ((i + 1 : ℕ) : ℤ) ≤ m then (1 - p) * concBinomWeight K p ((i + 1 : ℕ) : ℤ) else 0) := by
    intro i _
    rw [concBinomWeight_pascal]
    by_cases h : ((i + 1 : ℕ) : ℤ) ≤ m
    · have h' : (i : ℤ) ≤ m - 1 := by push_cast at h; omega
      rw [ite_eq_left h, ite_eq_left h, ite_eq_left h']
    · have h' : ¬ (i : ℤ) ≤ m - 1 := by push_cast at h; omega
      rw [ite_eq_right h, ite_eq_right h, ite_eq_right h']; simp
  rw [Finset.sum_congr rfl hL, Finset.sum_add_distrib]
  have hlast : ∑ i ∈ range (K + 1),
      (if ((i + 1 : ℕ) : ℤ) ≤ m then (1 - p) * concBinomWeight K p ((i + 1 : ℕ) : ℤ) else 0) =
      ∑ i ∈ range K,
      (if ((i + 1 : ℕ) : ℤ) ≤ m then (1 - p) * concBinomWeight K p ((i + 1 : ℕ) : ℤ) else 0) := by
    rw [Finset.sum_range_succ]
    have : concBinomWeight K p ((K + 1 : ℕ) : ℤ) = 0 := by
      rw [concBinomWeight_natCast, Nat.choose_succ_self]; simp
    rw [this]; simp
  rw [hlast]
  have hF : ∑ i ∈ range (K + 1), (if (i : ℤ) ≤ m then concBinomWeight K p i else 0) =
      (if ((0 : ℕ) : ℤ) ≤ m then concBinomWeight K p ((0 : ℕ) : ℤ) else 0) +
      ∑ i ∈ range K, (if ((i + 1 : ℕ) : ℤ) ≤ m then concBinomWeight K p ((i + 1 : ℕ) : ℤ) else 0) := by
    rw [Finset.sum_range_succ']; ring
  rw [hF]
  have h0 : concBinomWeight (K + 1) p ((0 : ℕ) : ℤ) = (1 - p) * concBinomWeight K p ((0 : ℕ) : ℤ) := by
    simp only [concBinomWeight_natCast]; simp [pow_succ]; ring
  rw [h0, mul_add, Finset.mul_sum, Finset.mul_sum]
  simp only [mul_ite, mul_zero]
  have : ∀ x : ℝ, (if ((0 : ℕ) : ℤ) ≤ m then (1 - p) * x else 0) =
      if ((0 : ℕ) : ℤ) ≤ m then (1 - p) * x else 0 := fun _ => rfl
  ring

end ElboimSly
