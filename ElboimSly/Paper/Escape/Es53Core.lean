/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Escape.Es53Events
public import ElboimSly.Paper.Escape.Plan53Rec
public import ElboimSly.Paper.Escape.Win
public import Mathlib

/-!
# On `𝒥 = ℬ ∩ ℬ' ∩ 𝒞 ∩ 𝒟 ∩ 𝒢`, `τ_i = 4^n`

ES22 Lemma 5.3 ("On `𝒥`, `τ_i = 4^n` and `W_i = W'_i` on `[0,4^n]`"), the part concerning the
conditions (1)-(7).  `core_stopLen`: if the true walk `W_i` satisfies the five events (with a set
`A ∋ 0` containing `A'`), then none of the conditions (1)-(7) holds before `4^n`, so `τ_i = 4^n`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Escape

open ElboimSly ElboimSly.Cyclic ElboimSly.Paper

variable {k : ℕ} {β : ℝ} [Fact (0 < β)] {n : ℕ} {u : Fin (k + 2) → ℤ} {b : ℕ}
  {hlog : 1 < Real.log β}

theorem coe_le_tn {x : ℝ} (_hx : 0 ≤ x) {s : ℝ≥0} (hs : x ≤ (s : ℝ)) : tn x ≤ s :=
  Real.toNNReal_le_iff_le_coe.2 hs

theorem le_tn_of_coe_le {x : ℝ} (hx : 0 ≤ x) {s : ℝ≥0} (h : (s : ℝ) ≤ x) : s ≤ tn x :=
  (Real.le_toNNReal_iff_coe_le hx).2 h

theorem core_stopLen (ν : Measure (CycS ℕ (k + 2) β)) {m : ℕ} (hm : m < escIstar n (escJ n))
    {m₁ : ℕ} (hm8 : 8 ≤ m₁) (hm1n : m₁ ≤ n) (hm1a : (m₁ : ℝ) ≤ Real.log (Real.log β))
    (hm1b : (4 : ℝ) ^ m₁ ≤ Real.log β) (hβ : Real.exp 2 ≤ Real.log β) (hn : 2 ≤ n)
    (hj1 : (n : ℝ) ^ 20 ≤ 2 ^ escJ n)
    (hIlam : 16 * (escIstar n (escJ n) * escLambda n) ≤ 3 * 2 ^ escJ n)
    (hjn : (escJ n : ℝ) * 4 ^ escJ n ≤ 4 ^ n)
    {A : Set (Fin (k + 2) → ℤ)} (hA0 : (0 : Fin (k + 2) → ℤ) ∈ A)
    (hAsub : escVisNbr n u b hlog ν m ⊆ A)
    (hB : EsB n m₁ (escPoint n (escJ n) u (m + 1))
      (envPath ν (0, escPoint n (escJ n) u (m + 1), (b : ℝ), true)).1.fn)
    (hB' : EsB' n (escJ n) (escPoint n (escJ n) u (m + 1))
      (envPath ν (0, escPoint n (escJ n) u (m + 1), (b : ℝ), true)).1.fn)
    (hC : EsC n A (envPath ν (0, escPoint n (escJ n) u (m + 1), (b : ℝ), true)).1.fn)
    (hD : EsD n m₁ (envPath ν (0, escPoint n (escJ n) u (m + 1), (b : ℝ), true)).1.fn)
    (hG : EsG n (escJ n) (escIstar n (escJ n)) u (m + 1)
      (envPath ν (0, escPoint n (escJ n) u (m + 1), (b : ℝ), true)).1.fn) :
    (planA n β u b hlog).stopLen m ((planA n β u b hlog).ideal (envRuleA n u b hlog ν) m)
      (envPath ν (0, escPoint n (escJ n) u (m + 1), (b : ℝ), true)) = (4 : ℝ≥0∞) ^ n := by
  set pT := envPath ν (0, escPoint n (escJ n) u (m + 1), (b : ℝ), true) with hpT
  set j := escJ n with hj
  set p := escPoint n j u (m + 1) with hp
  have hRC : IsRCPath pT.1.fn := fun t => pT.1.rc t
  have hT4 : tn ((4 : ℝ) ^ n) = (4 : ℝ≥0) ^ n := by
    simp [tn, Real.toNNReal_pow]
  have h4pos : (0 : ℝ) ≤ (4 : ℝ) ^ n := by positivity
  have hCr := forall_of_not_exists_qSet hRC (bot_le : (0 : ℝ≥0) ≤ _) (P := fun v => v ∈ A) hC
  have hjnn : tn ((j : ℝ) * 4 ^ j) ≤ tn ((4 : ℝ) ^ n) := Real.toNNReal_le_toNNReal hjn
  have hB'r := forall_of_not_exists_qSet hRC hjnn (P := fun v => ‖v - p‖ < 2 ^ j) hB'
  have hGr := forall_of_not_exists_qSet hRC (bot_le : (0 : ℝ≥0) ≤ _)
    (P := fun v => (Metric.infDist (fun c => ((v c : ℤ) : ℝ))
        ((fun x c => ((x c : ℤ) : ℝ)) '' escBlockMinus j u) ≤ (2 : ℝ) ^ j / 8) ∨
      (∃ ℓ, 1 ≤ ℓ ∧ ℓ ≤ escIstar n j ∧ ℓ ≠ m + 1 ∧ ‖v - escPoint n j u ℓ‖ ≤ (n : ℝ) ^ 17 / 6)) hG
  have hmI : 1 ≤ m + 1 ∧ m + 1 ≤ escIstar n (escJ n) := ⟨by omega, Nat.succ_le_of_lt hm⟩
  have hlam16 : ((m + 1 : ℕ) : ℝ) * escLambda n ≤ 3 * ((2 : ℝ) ^ j / 16) := by
    have h1 : (16 : ℝ) * (escIstar n j * escLambda n) ≤ 3 * 2 ^ j := by exact_mod_cast hIlam
    have h2 : ((m + 1 : ℕ) : ℝ) ≤ escIstar n j := by exact_mod_cast hmI.2
    have h3 : ((m + 1 : ℕ) : ℝ) * escLambda n ≤ escIstar n j * escLambda n :=
      mul_le_mul_of_nonneg_right h2 (Nat.cast_nonneg _)
    linarith
  have hj2 : 2 ≤ j := by
    by_contra hh
    push Not at hh
    have : (2 : ℝ) ^ j ≤ 2 ^ 1 := pow_le_pow_right₀ (by norm_num) (by omega)
    have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have : (2 : ℝ) ^ 20 ≤ (n : ℝ) ^ 20 := pow_le_pow_left₀ (by norm_num) hn2 20
    norm_num at *
    linarith
  have hn17 : (n : ℝ) ^ 17 / 6 ≤ (2 : ℝ) ^ j / 48 := by
    have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have h3 : (8 : ℝ) ≤ (n : ℝ) ^ 3 := by
      calc (8 : ℝ) = 2 ^ 3 := by norm_num
        _ ≤ (n : ℝ) ^ 3 := pow_le_pow_left₀ (by norm_num) hn2 3
    have : (n : ℝ) ^ 20 = (n : ℝ) ^ 17 * (n : ℝ) ^ 3 := by ring
    have hn17p : 0 ≤ (n : ℝ) ^ 17 := by positivity
    nlinarith
  refine stopLen_eq_of_no_cond (planA_ruleAt n u b hlog m) hlog _ pT ?_
  intro t ht hcany
  have ht' : (t : ℝ) < 4 ^ n := ht
  have htT : t ≤ tn ((4 : ℝ) ^ n) := le_tn_of_coe_le h4pos ht'.le
  unfold EscRP.Cany EscRP.Cpos at hcany
  simp only [snoc_last'] at hcany
  rcases hcany with ((h1 | h4 | h5 | h6) | h2 | h3 | h7)
  · -- (1)
    unfold escC1 at h1
    rw [entEnd_cut] at h1
    exact hCr t bot_le htT (by rw [h1]; exact hA0)
  · -- (4)
    unfold EscRP.C4 at h4
    rw [entEnd_cut] at h4
    obtain ⟨ℓ', hℓ1, hℓI, hℓne, hℓ⟩ := h4
    by_cases htj : (t : ℝ) ≤ (j : ℝ) * 4 ^ j
    · exact hGr t bot_le (le_tn_of_coe_le (by positivity) htj)
        (Or.inr ⟨ℓ', hℓ1, hℓI, hℓne, hℓ⟩)
    · push Not at htj
      have hb := hB'r t (coe_le_tn (by positivity) htj.le) htT
      apply hb
      have hd := point_dist_le (n := n) (j := j) (u := u) hℓ1 hℓI hmI.1 hmI.2 hIlam
      rw [norm_sub_rev] at hd
      have h := norm_sub_le_norm_sub_add_norm_sub (pT.1.fn t) (escPoint n j u ℓ') p
      have hℓ' : ‖pT.1.fn t - escPoint n j u ℓ'‖ ≤ (n : ℝ) ^ 17 / 6 := hℓ
      have : (0 : ℝ) < 2 ^ j := by positivity
      linarith
  · -- (5)
    unfold EscRP.Cvisit at h5
    obtain ⟨ℓ', hℓ1, hℓ2, hh, hc⟩ := h5
    have hidx : (escRP n β u 0).idx ℓ' = ℓ' - 1 := by simp [EscRP.idx, escRP]
    have hlt : (escRP n β u 0).idx ℓ' < m := by rw [hidx]; omega
    rw [snoc_castSucc' _ _ hlt hh] at hc
    unfold escC5 at hc
    obtain ⟨s, hs, hsn⟩ := hc
    simp only [snoc_last'] at hsn
    rw [entEnd_cut] at hsn
    have hent : ((planA n β u b hlog).ideal (envRuleA n u b hlog ν) m)
        ⟨(escRP n β u 0).idx ℓ', hlt⟩ = escEntry n u b hlog ν ((escRP n β u 0).idx ℓ') :=
      ideal_apply' (i := ⟨(escRP n β u 0).idx ℓ', hlt⟩) (m := m)
    rw [hent] at hs hsn
    exact hCr t bot_le htT (hAsub ⟨(escRP n β u 0).idx ℓ', hlt, s, hs, hsn⟩)
  · -- (6)
    unfold EscRP.C6 at h6
    rw [entEnd_cut] at h6
    by_cases htj : (t : ℝ) ≤ (j : ℝ) * 4 ^ j
    · exact hGr t bot_le (le_tn_of_coe_le (by positivity) htj) (Or.inl h6)
    · push Not at htj
      have hb := hB'r t (coe_le_tn (by positivity) htj.le) htT
      apply hb
      have := escPoint_norm_lt_of_infDist (n := n) (u := u) hj2 (m + 1) hlam16 (pT.1.fn t) h6
      rwa [norm_escCast_sub] at this
  · -- (2)
    unfold EscRP.C2 at h2
    rw [tm_cut, entEnd_cut] at h2
    obtain ⟨hl, hnorm⟩ := h2
    have ht4m : (4 : ℝ) ^ m₁ ≤ t := hm1b.trans hl
    have ht0 : 0 < (t : ℝ) := lt_of_lt_of_le (by positivity) ht4m
    set m0 := ⌊Real.logb 4 (t : ℝ)⌋₊ with hm0
    have hlogb0 : 0 ≤ Real.logb 4 (t : ℝ) :=
      Real.logb_nonneg (by norm_num) (le_trans (one_le_pow₀ (by norm_num)) ht4m)
    have hm1m0 : m₁ ≤ m0 := by
      refine Nat.le_floor ?_
      rw [Real.le_logb_iff_rpow_le (by norm_num) ht0, Real.rpow_natCast]
      exact ht4m
    have hm0t : (4 : ℝ) ^ m0 ≤ t := by
      have := Nat.floor_le hlogb0
      rw [← hm0, Real.le_logb_iff_rpow_le (by norm_num) ht0, Real.rpow_natCast] at this
      exact this
    have htm0 : (t : ℝ) < 4 ^ (m0 + 1) := by
      have := Nat.lt_floor_add_one (Real.logb 4 (t : ℝ))
      rw [← hm0, Real.logb_lt_iff_lt_rpow (by norm_num) ht0] at this
      rw [← Real.rpow_natCast]
      exact_mod_cast this
    have hm0n : m0 ≤ n := by
      by_contra hh
      push Not at hh
      have : (4 : ℝ) ^ n < 4 ^ m0 := pow_lt_pow_right₀ (by norm_num) hh
      linarith
    have hBr := forall_of_not_exists_qSet hRC
      (Real.toNNReal_le_toNNReal (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 4) hm0n))
      (P := fun v => ‖v - p‖ < 2 ^ (m0 + 3) / m0) (hB m0 hm1m0 hm0n) t
      (coe_le_tn (by positivity) hm0t) htT
    apply hBr
    have hm01 : 1 ≤ m0 := by omega
    have := esArith_C2 hm01 hm0t htm0
    rw [← Real.norm_natCast] at this ⊢
    simp only [Real.norm_natCast] at *
    exact lt_of_le_of_lt hnorm this
  · -- (3)
    unfold EscRP.C3 at h3
    rw [tm_cut] at h3
    have hL := escL_pos hlog (t : ℝ)
    have hw := isCyclicPath_shift (pT.cut (t : ℝ≥0∞))
    have h3' : pathTfast (fun s : ℝ => (pT.cut (t : ℝ≥0∞)).1.fn s.toNNReal -
        (pT.cut (t : ℝ≥0∞)).1.fn 0) (escL β (t : ℝ)) ≤ ENNReal.ofReal t := h3
    rw [← not_lt, ofReal_lt_pathTfast_iff hw hL] at h3'
    push Not at h3'
    obtain ⟨t₁, ht₁0, ht₁t, s₁, hs1, hs2, hdisp⟩ := h3'
    have hcutfn : ∀ x : ℝ≥0, (pT.cut (t : ℝ≥0∞)).1.fn x = pT.1.fn (min x t) :=
      fun x => cut_fn_apply (0, escPoint n j u (m + 1), (b : ℝ), true) pT t x
    set a1 : ℝ≥0 := t₁.toNNReal with ha1
    set a2 : ℝ≥0 := (max s₁ 0).toNNReal with ha2
    have ha1r : (a1 : ℝ) = t₁ := Real.coe_toNNReal _ ht₁0.le
    have ha2r : (a2 : ℝ) = max s₁ 0 := Real.coe_toNNReal _ (le_max_right _ _)
    have ha1t : a1 ≤ t := by rw [← NNReal.coe_le_coe, ha1r]; exact ht₁t
    have ha21 : a2 ≤ a1 := by
      rw [← NNReal.coe_le_coe, ha1r, ha2r]; exact max_le hs2 ht₁0.le
    have ha12 : a1 ≤ a2 + 1 := by
      rw [← NNReal.coe_le_coe, NNReal.coe_add, ha1r, ha2r, NNReal.coe_one]
      linarith [le_max_left s₁ 0]
    have hnorm : ‖pT.1.fn a1 - pT.1.fn a2‖ =
        ‖((pT.cut (t : ℝ≥0∞)).1.fn t₁.toNNReal - (pT.cut (t : ℝ≥0∞)).1.fn 0) -
          ((pT.cut (t : ℝ≥0∞)).1.fn (max s₁ 0).toNNReal - (pT.cut (t : ℝ≥0∞)).1.fn 0)‖ := by
      rw [sub_sub_sub_cancel_right, hcutfn, hcutfn, min_eq_left ha1t,
        min_eq_left (ha21.trans ha1t)]
    have hdisp' : escL β (t : ℝ) ≤ ‖pT.1.fn a1 - pT.1.fn a2‖ := by
      rw [hnorm]; exact hdisp
    set m' := max m₁ ⌈Real.logb 4 t₁⌉₊ with hm'
    have hm'n : m' ≤ n := by
      refine max_le hm1n ?_
      refine Nat.ceil_le.2 ?_
      rw [Real.logb_le_iff_le_rpow (by norm_num) ht₁0, Real.rpow_natCast]
      exact (ht₁t.trans ht'.le)
    have hm'1 : (m' : ℝ) ≤ Real.log (max (t : ℝ) (Real.log β)) :=
      esArith_C3b ht₁0 ht₁t hm8 hm1a hβ
    have hm'2 : (m' : ℝ) ^ 2 ≤ escL β (t : ℝ) := by
      unfold escL
      exact pow_le_pow_left₀ (Nat.cast_nonneg _) hm'1 2
    have ha1T : a1 ≤ tn ((4 : ℝ) ^ m') :=
      le_tn_of_coe_le (by positivity) (by rw [ha1r]; exact esArith_C3a ht₁0 m₁)
    refine hD m' (le_max_left _ _) hm'n ?_
    exact (exists_win_qSet hRC (T := tn ((4 : ℝ) ^ m'))
      (fun a b => (m' : ℝ) ^ 2 ≤ ‖a - b‖)).1
        ⟨a1, a2, by rw [ha1]; exact Real.toNNReal_pos.2 ht₁0, ha1T, ha21, ha12,
          hm'2.trans hdisp'⟩
  · -- (7)
    unfold EscRP.C7 at h7
    rw [tm_cut] at h7
    exact absurd ht' (not_lt.2 (le_of_eq h7.symm))

end ElboimSly.Paper.Escape
