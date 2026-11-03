/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Escape.Es53Step
public import ElboimSly.Paper.Escape.Es53NumDef
public import ElboimSly.Paper.Escape.PointGeom
public import Mathlib

/-!
# The set `A = {0} ∪ A'` is sparse and far from `p_i`

ES22 Lemma 5.3, "`𝒞`, conditionally": `A ⊆ {‖y - p_i‖ ≥ L_C}` and
`|A ∩ (p_i + [-r,r]^d)| ≤ r^{8/3}` for `r ≥ L_C = n^{17}/7`, from density of the explored walks around p_i and the
admissibility of the block (`‖p_i‖ ≥ 2^{j-2}`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace ElboimSly.Paper.Escape

open ElboimSly ElboimSly.Cyclic ElboimSly.Paper

variable {k : ℕ} {β : ℝ} [Fact (0 < β)] {n : ℕ} {u : Fin (k + 2) → ℤ} {b : ℕ}
  {hlog : 1 < Real.log β}

/-- Admissibility: `‖p_i‖ ≥ 2^j/4`. -/
theorem norm_escPoint_ge {j : ℕ} (hj : 2 ≤ j) (hadm : EscAdmissible j u) (i : ℕ)
    (hi : (i : ℝ) * escLambda n ≤ 3 * ((2 : ℝ) ^ j / 16)) :
    (2 : ℝ) ^ j / 4 ≤ ‖escPoint n j u i‖ := by
  have ha : (0 : ℝ) < (2 : ℝ) ^ j / 4 := by positivity
  have hl : (0 : ℝ) ≤ (i : ℝ) * escLambda n := by positivity
  have hcoord : ∀ c, |((escPoint n j u i c : ℤ) : ℝ)| ≤ ‖escPoint n j u i‖ := by
    intro c
    have := norm_le_pi_norm (escPoint n j u i) c
    simpa [Real.norm_eq_abs, Int.norm_eq_abs] using this
  rcases hadm with hnot | hu
  · -- `0 ∉ B`: a coordinate of `u` is `≥ 1` or `≤ -2^j`
    have : ∃ c, ¬ (u c ≤ 0 ∧ 0 < u c + 2 ^ j) := by
      by_contra hh
      push Not at hh
      exact hnot (fun c => ⟨by have := (hh c).1; omega, by have := (hh c).2; omega⟩ : (0 : Fin (k + 2) → ℤ) ∈ escBlock j u)
    obtain ⟨c, hc⟩ := this
    have hp : ∀ c', ((escPoint n j u i c' : ℤ) : ℝ) = u c' + ((escPoint n j u i c' : ℤ) - u c' : ℝ) := by
      intro c'; ring
    have h2j : (2 : ℝ) ^ j = 4 * ((2 : ℝ) ^ j / 4) := by ring
    by_cases hc0 : c = 0
    · subst hc0
      have e := escPoint_zero_coord (n := n) (u := u) hj i
      by_cases hu : u 0 ≤ 0
      · have hu2 : ¬ (0 < u 0 + 2 ^ j) := fun h => hc ⟨hu, h⟩
        have hu3 : (u 0 : ℝ) + (2 : ℝ) ^ j ≤ 0 := by
          have : u 0 + 2 ^ j ≤ 0 := by omega
          exact_mod_cast this
        have := hcoord 0
        rw [e] at this
        have := le_trans (neg_le_abs _) this
        linarith
      · have hu1 : (1 : ℝ) ≤ u 0 := by
          have : 1 ≤ u 0 := by omega
          exact_mod_cast this
        have := hcoord 0
        rw [e] at this
        have := le_trans (le_abs_self _) this
        linarith
    · by_cases hc1 : c = 1
      · subst hc1
        have e := escPoint_one_coord (n := n) (u := u) hj i
        by_cases hu : u 1 ≤ 0
        · have hu2 : ¬ (0 < u 1 + 2 ^ j) := fun h => hc ⟨hu, h⟩
          have hu3 : (u 1 : ℝ) + (2 : ℝ) ^ j ≤ 0 := by
            have : u 1 + 2 ^ j ≤ 0 := by omega
            exact_mod_cast this
          have := hcoord 1
          rw [e] at this
          have := le_trans (neg_le_abs _) this
          linarith
        · have hu1 : (1 : ℝ) ≤ u 1 := by
            have : 1 ≤ u 1 := by omega
            exact_mod_cast this
          have := hcoord 1
          rw [e] at this
          have := le_trans (le_abs_self _) this
          linarith
      · have e := escPoint_other_coord (n := n) (u := u) hj i hc0 hc1
        by_cases hu : u c ≤ 0
        · have hu2 : ¬ (0 < u c + 2 ^ j) := fun h => hc ⟨hu, h⟩
          have hu3 : (u c : ℝ) + (2 : ℝ) ^ j ≤ 0 := by
            have : u c + 2 ^ j ≤ 0 := by omega
            exact_mod_cast this
          have := hcoord c
          rw [e] at this
          have := le_trans (neg_le_abs _) this
          linarith
        · have hu1 : (1 : ℝ) ≤ u c := by
            have : 1 ≤ u c := by omega
            exact_mod_cast this
          have := hcoord c
          rw [e] at this
          have := le_trans (le_abs_self _) this
          linarith
  · subst hu
    have e := escPoint_zero_coord (n := n) (u := (0 : Fin (k + 2) → ℤ)) hj i
    have := hcoord 0
    rw [e] at this
    simp only [Pi.zero_apply, Int.cast_zero, zero_add] at this
    have := le_trans (le_abs_self _) this
    linarith

theorem escVisNbr_subset_escVneG {ν : Measure (CycS ℕ (k + 2) β)} (hν : CycGood ν) {m : ℕ}
    (hm : m < escIstar n (escJ n)) :
    escVisNbr n u b hlog ν m ⊆ escVneG n (escJ n) β (escIstar n (escJ n)) u (escWalkE n u b ν)
      (escBlockMinus (escJ n) u) (escTauE n u b hlog ν) (m + 1) := by
  rintro y ⟨jj, hjj, s, hs, hy⟩
  have hI : 1 ≤ jj + 1 ∧ jj + 1 ≤ escIstar n (escJ n) := ⟨by omega, by omega⟩
  refine ⟨jj + 1, hI.1, hI.2, by omega, (s : ℝ), NNReal.coe_nonneg s, ?_, ?_⟩
  · unfold escTauE
    rw [ite_eq_left hI]
    simp only [Nat.add_sub_cancel]
    have hne := escEntry_len_ne_top (n := n) (u := u) (b := b) (hlog := hlog) (ν := ν) jj
    have := ENNReal.toReal_mono hne hs
    simpa using this
  · rw [escWalkE_eq_envPath hν, Real.toNNReal_coe]
    have := escEntry_fn (n := n) (u := u) (b := b) (hlog := hlog) (ν := ν) jj s
    rw [min_eq_left hs, ENNReal.toNNReal_coe] at this
    rw [← this]
    exact hy

theorem A_density {ν : Measure (CycS ℕ (k + 2) β)} (hν : CycGood ν) {m : ℕ}
    (hm : m < escIstar n (escJ n)) {n₀ : ℕ} (hadm : EscAdmissible (escJ n) u)
    (hj2 : 2 ≤ escJ n) (hj1 : (n : ℝ) ^ 20 ≤ 2 ^ escJ n) (hn2 : 2 ≤ n)
    (hIlam : 16 * (escIstar n (escJ n) * escLambda n) ≤ 3 * 2 ^ escJ n)
    (_hL1 : (4 : ℝ) ^ (n₀ + 1) ≤ (n : ℝ) ^ 17 / 7)
    (hL3 : (n : ℝ) ^ 17 / 7 ≤ (n : ℝ) ^ 17 / 6 - 2)
    (hd1 : escVneG n (escJ n) β (escIstar n (escJ n)) u (escWalkE n u b ν)
      (escBlockMinus (escJ n) u) (escTauE n u b hlog ν) (m + 1) ⊆
        {y | (n : ℝ) ^ 17 / 6 - 2 < ‖y - escPoint n (escJ n) u (m + 1)‖})
    (hd2 : ∀ r : ℝ, (n : ℝ) ^ 17 / 7 ≤ r →
      ((escVneG n (escJ n) β (escIstar n (escJ n)) u (escWalkE n u b ν)
        (escBlockMinus (escJ n) u) (escTauE n u b hlog ν) (m + 1) ∩
          {y | ‖y - escPoint n (escJ n) u (m + 1)‖ ≤ r}).ncard : ℝ) ≤ r ^ (8 / 3 : ℝ) / 2) :
    (∀ z ∈ ({0} ∪ escVisNbr n u b hlog ν m : Set (Fin (k + 2) → ℤ)),
      (n : ℝ) ^ 17 / 7 ≤ ‖z - escPoint n (escJ n) u (m + 1)‖) ∧
    (∀ r : ℝ, (n : ℝ) ^ 17 / 7 ≤ r →
      ((({0} ∪ escVisNbr n u b hlog ν m : Set (Fin (k + 2) → ℤ)) ∩
        {z | ‖z - escPoint n (escJ n) u (m + 1)‖ ≤ r}).ncard : ℝ) ≤ r ^ (8 / 3 : ℝ)) := by
  have hsub := escVisNbr_subset_escVneG (n := n) (u := u) (b := b) (hlog := hlog) hν hm
  have hmI : 1 ≤ m + 1 ∧ m + 1 ≤ escIstar n (escJ n) := ⟨by omega, Nat.succ_le_of_lt hm⟩
  have hlam16 : ((m + 1 : ℕ) : ℝ) * escLambda n ≤ 3 * ((2 : ℝ) ^ escJ n / 16) := by
    have h1 : (16 : ℝ) * (escIstar n (escJ n) * escLambda n) ≤ 3 * 2 ^ escJ n := by
      exact_mod_cast hIlam
    have h2 : ((m + 1 : ℕ) : ℝ) ≤ escIstar n (escJ n) := by exact_mod_cast hmI.2
    have h3 : ((m + 1 : ℕ) : ℝ) * escLambda n ≤ escIstar n (escJ n) * escLambda n :=
      mul_le_mul_of_nonneg_right h2 (Nat.cast_nonneg _)
    linarith
  have hn2r : (2 : ℝ) ≤ n := by exact_mod_cast hn2
  have hp := norm_escPoint_ge (n := n) hj2 hadm (m + 1) hlam16
  constructor
  · rintro z (hz | hz)
    · rw [mem_singleton_iff] at hz
      subst hz
      rw [zero_sub, norm_neg]
      refine le_trans ?_ hp
      have h3 : (8 : ℝ) ≤ (n : ℝ) ^ 3 := by
        calc (8 : ℝ) = 2 ^ 3 := by norm_num
          _ ≤ (n : ℝ) ^ 3 := pow_le_pow_left₀ (by norm_num) hn2r 3
      have : (n : ℝ) ^ 20 = (n : ℝ) ^ 17 * (n : ℝ) ^ 3 := by ring
      have hn17p : 0 ≤ (n : ℝ) ^ 17 := by positivity
      nlinarith
    · have := hd1 (hsub hz)
      simp only [mem_ofPred_eq] at this
      linarith
  · intro r hr
    have hbox : {z : Fin (k + 2) → ℤ | ‖z - escPoint n (escJ n) u (m + 1)‖ ≤ r}.Finite :=
      box_finite _ r
    have hV : (escVisNbr n u b hlog ν m ∩ {z | ‖z - escPoint n (escJ n) u (m + 1)‖ ≤ r}).ncard ≤
        (escVneG n (escJ n) β (escIstar n (escJ n)) u (escWalkE n u b ν)
          (escBlockMinus (escJ n) u) (escTauE n u b hlog ν) (m + 1) ∩
            {y | ‖y - escPoint n (escJ n) u (m + 1)‖ ≤ r}).ncard :=
      Set.ncard_le_ncard (inter_subset_inter_left _ hsub) (hbox.subset inter_subset_right)
    have hU : (({0} ∪ escVisNbr n u b hlog ν m : Set (Fin (k + 2) → ℤ)) ∩
        {z | ‖z - escPoint n (escJ n) u (m + 1)‖ ≤ r}).ncard ≤
        1 + (escVisNbr n u b hlog ν m ∩ {z | ‖z - escPoint n (escJ n) u (m + 1)‖ ≤ r}).ncard := by
      have : (({0} ∪ escVisNbr n u b hlog ν m : Set (Fin (k + 2) → ℤ)) ∩
          {z | ‖z - escPoint n (escJ n) u (m + 1)‖ ≤ r}) ⊆
          {0} ∪ (escVisNbr n u b hlog ν m ∩ {z | ‖z - escPoint n (escJ n) u (m + 1)‖ ≤ r}) := by
        rintro z ⟨hz1 | hz1, hz2⟩
        · exact Or.inl hz1
        · exact Or.inr ⟨hz1, hz2⟩
      refine (Set.ncard_le_ncard this ((Set.finite_singleton _).union
        (hbox.subset inter_subset_right))).trans ?_
      refine (Set.ncard_union_le _ _).trans ?_
      simp
    have hr4 : (4 : ℝ) ≤ r := by
      have h4 : (4 : ℝ) ≤ 4 ^ (n₀ + 1) := by
        calc (4 : ℝ) = 4 ^ 1 := by norm_num
          _ ≤ 4 ^ (n₀ + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
      linarith
    have hrr : r ≤ r ^ (8 / 3 : ℝ) := by
      calc r = r ^ (1 : ℝ) := (Real.rpow_one r).symm
        _ ≤ r ^ (8 / 3 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
    have h1 : (((escVisNbr n u b hlog ν m ∩
        {z | ‖z - escPoint n (escJ n) u (m + 1)‖ ≤ r}).ncard : ℕ) : ℝ) ≤ r ^ (8 / 3 : ℝ) / 2 :=
      le_trans (by exact_mod_cast hV) (hd2 r hr)
    have hU' : ((({0} ∪ escVisNbr n u b hlog ν m : Set (Fin (k + 2) → ℤ)) ∩
        {z | ‖z - escPoint n (escJ n) u (m + 1)‖ ≤ r}).ncard : ℝ) ≤
        1 + ((escVisNbr n u b hlog ν m ∩
          {z | ‖z - escPoint n (escJ n) u (m + 1)‖ ≤ r}).ncard : ℝ) := by exact_mod_cast hU
    linarith

end ElboimSly.Paper.Escape
