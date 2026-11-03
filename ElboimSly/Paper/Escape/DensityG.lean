/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Escape.VisitsG
public import ElboimSly.Paper.Escape.Density
public import Mathlib

/-!
# Density of the explored walks around p_i for an arbitrary family of stopping times

`escDensity` with `escTauSeq` replaced by a family `τ` with `EscBefore`.
-/

@[expose] public section

namespace ElboimSly.Paper.Escape

open ElboimSly.Paper

variable {k : ℕ}

/-- Density of the explored walks around p_i: `V_{≠i}`. -/
def escVneG (_n _j : ℕ) (_β : ℝ) (I : ℕ) (_u : Fin (k + 2) → ℤ) (W : ℕ → ℝ → Fin (k + 2) → ℤ)
    (_Bm : Set (Fin (k + 2) → ℤ)) (τ : ℕ → ℝ) (i : ℕ) : Set (Fin (k + 2) → ℤ) :=
  {y | ∃ ℓ, 1 ≤ ℓ ∧ ℓ ≤ I ∧ ℓ ≠ i ∧ ∃ s, 0 ≤ s ∧
    s ≤ τ ℓ ∧ ‖y - W ℓ s‖ ≤ 1}

lemma far_of_ltG {n j : ℕ} {β : ℝ} {I : ℕ} {P : ℕ → Fin (k + 2) → ℤ}
    {W : ℕ → ℝ → Fin (k + 2) → ℤ} {Bm : Set (Fin (k + 2) → ℤ)} {τ : ℕ → ℝ}
    (hτ : EscBefore n j β I P W Bm τ) {ℓ i : ℕ} (hi1 : 1 ≤ i)
    (hiI : i ≤ I) (hne : i ≠ ℓ) {s : ℝ} (hs : 0 < s)
    (hlt : s < τ ℓ) : (n : ℝ) ^ 17 / 6 < ‖W ℓ s - P i‖ := by
  by_contra hle
  push Not at hle
  apply hτ _ _ hs hlt
  exact Or.inr (Or.inr (Or.inr (Or.inl ⟨i, hi1, hiI, hne, hle⟩)))

theorem escDensityG_incl {n j : ℕ} {β : ℝ} {I : ℕ} {u : Fin (k + 2) → ℤ}
    {W : ℕ → ℝ → Fin (k + 2) → ℤ} {Bm : Set (Fin (k + 2) → ℤ)} {τ : ℕ → ℝ}
    (hτ : EscBefore n j β I (escPoint n j u) W Bm τ) {i : ℕ} (hn : 2 ≤ n)
    (hi1 : 1 ≤ i) (hiI : i ≤ I) (hW0 : ∀ ℓ, W ℓ 0 = escPoint n j u ℓ)
    (hnn : ∀ ℓ t, 0 < t → ∀ ε > 0, ∃ s, t - ε < s ∧ s < t ∧ ‖W ℓ t - W ℓ s‖ ≤ 1) :
    escVneG n j β I u W Bm τ i ⊆ {y | (n : ℝ) ^ 17 / 6 - 2 < ‖y - escPoint n j u i‖} := by
  rintro y ⟨ℓ, hℓ1, hℓI, hne, s, hs0, hsτ, hy⟩
  have hlam := (escLambda_bounds hn).1
  have hpd : (n : ℝ) ^ 17 / 6 < ‖W ℓ 0 - escPoint n j u i‖ := by
    rw [hW0, norm_point_sub]
    have : (1 : ℝ) ≤ |(ℓ : ℝ) - i| := by
      have : (ℓ : ℤ) ≠ i := by exact_mod_cast hne
      have h1 : (1 : ℤ) ≤ |(ℓ : ℤ) - i| := Int.one_le_abs (sub_ne_zero.2 this)
      have : ((1 : ℤ) : ℝ) ≤ ((|(ℓ : ℤ) - i| : ℤ) : ℝ) := by exact_mod_cast h1
      simpa using this
    nlinarith
  have hmain : (n : ℝ) ^ 17 / 6 - 1 < ‖W ℓ s - escPoint n j u i‖ := by
    rcases hs0.eq_or_lt with h0 | hpos
    · subst h0; linarith
    · rcases hsτ.eq_or_lt with heq | hlt
      · -- s = τ_ℓ > 0: nearest-neighbour jump from just before
        obtain ⟨s0, hs0a, hs0b, hjump⟩ := hnn ℓ s hpos s hpos
        have hs0pos : 0 < s0 := by linarith
        have hfar := far_of_ltG hτ (n := n) (j := j) (β := β) (I := I) (P := escPoint n j u)
          (W := W) (Bm := Bm) hi1 hiI (Ne.symm hne) hs0pos (by rw [← heq]; exact hs0b)
        have := norm_sub_le_norm_sub_add_norm_sub (W ℓ s0) (W ℓ s) (escPoint n j u i)
        have h2 := norm_sub_rev (W ℓ s0) (W ℓ s)
        linarith
      · have := far_of_ltG hτ (n := n) (j := j) (β := β) (I := I) (P := escPoint n j u)
          (W := W) (Bm := Bm) hi1 hiI (Ne.symm hne) hpos hlt
        linarith
  have := norm_sub_le_norm_sub_add_norm_sub (W ℓ s) y (escPoint n j u i)
  rw [norm_sub_rev (W ℓ s) y] at this
  show (n : ℝ) ^ 17 / 6 - 2 < ‖y - escPoint n j u i‖
  linarith

/-- The counting part of density of the explored walks around p_i, given the two asymptotic estimates. -/
theorem escDensityG_count {n j : ℕ} {β : ℝ} {I : ℕ} {u : Fin (k + 2) → ℤ}
    {W : ℕ → ℝ → Fin (k + 2) → ℤ} {Bm : Set (Fin (k + 2) → ℤ)} {τ : ℕ → ℝ}
    (hτ : EscBefore n j β I (escPoint n j u) W Bm τ) {i : ℕ}
    (hβ : Real.exp 2 ≤ Real.log β) (hlb : Real.log β ≤ (n : ℝ) ^ 17 / 7) (hn4 : 4 ≤ n)
    (hj1 : (n : ℝ) ^ 20 ≤ 2 ^ j) (hj2 : (2 : ℝ) ^ j < 2 * n ^ 20) (hI : I ≤ n ^ 3)
    (hIlam : 16 * (I * escLambda n) ≤ 3 * 2 ^ j) (hi1 : 1 ≤ i) (hiI : i ≤ I)
    (hA : ∀ r : ℝ, (n : ℝ) ^ 17 / 7 ≤ r →
      (n : ℝ) ^ 3 * densK (k + 2) * ((4 * (n : ℝ) ^ 20) ^ 2 *
        Real.log (4 * (n : ℝ) ^ 20) ^ (2 * (k + 2) + 2)) ≤ r ^ (8 / 3 : ℝ) / 2)
    (hB : ∀ r : ℝ, (2 : ℝ) ^ j ≤ r → ∀ x : ℝ, 0 ≤ x → x ≤ r ^ (3 / 20 : ℝ) →
      x * densK (k + 2) * ((3 * r) ^ 2 * Real.log (3 * r) ^ (2 * (k + 2) + 2)) ≤
        r ^ (8 / 3 : ℝ) / 2)
    {r : ℝ} (hr : (n : ℝ) ^ 17 / 7 ≤ r) :
    ((escVneG n j β I u W Bm τ i ∩ {y | ‖y - escPoint n j u i‖ ≤ r}).ncard : ℝ) ≤
      r ^ (8 / 3 : ℝ) / 2 := by
  classical
  set m := 2 * (k + 2) + 2 with hm
  set F : Finset ℕ := (Finset.Icc 1 I).erase i with hF
  have hn4r : (4 : ℝ) ≤ n := by exact_mod_cast hn4
  have hn17 : (10 : ℝ) ≤ (n : ℝ) ^ 17 / 7 := by
    have : (4 : ℝ) ^ 17 ≤ (n : ℝ) ^ 17 := pow_le_pow_left₀ (by norm_num) hn4r 17
    have : (4 : ℝ) ^ 17 = 17179869184 := by norm_num
    linarith
  have hr10 : 10 ≤ r := by linarith
  set P := escPoint n j u with hP
  let R : ℕ → ℝ := fun ℓ => r + 1 + ‖P i - P ℓ‖
  let X : ℕ → Set (Fin (k + 2) → ℤ) := fun ℓ =>
    {x | ∃ s, 0 ≤ s ∧ s ≤ τ ℓ ∧ W ℓ s = x} ∩ {x | ‖x - P ℓ‖ ≤ R ℓ}
  have hXfin : ∀ ℓ, (X ℓ).Finite := fun ℓ =>
    (box_finite (P ℓ) (R ℓ)).subset Set.inter_subset_right
  have hsub : (escVneG n j β I u W Bm τ i ∩ {y | ‖y - P i‖ ≤ r}) ⊆
      ⋃ ℓ ∈ F, {y | ∃ x ∈ X ℓ, ‖y - x‖ ≤ 1} := by
    rintro y ⟨⟨ℓ, hℓ1, hℓI, hne, s, hs0, hsτ, hy⟩, hyr⟩
    simp only [Set.mem_ofPred_eq] at hyr
    simp only [Set.mem_iUnion]
    refine ⟨ℓ, by simp [hF, hne, hℓ1, hℓI], W ℓ s, ⟨⟨s, hs0, hsτ, rfl⟩, ?_⟩, ?_⟩
    · simp only [Set.mem_ofPred_eq, R]
      have h1 := norm_sub_le_norm_sub_add_norm_sub (W ℓ s) y (P ℓ)
      have h2 := norm_sub_le_norm_sub_add_norm_sub y (P i) (P ℓ)
      have h3 := norm_sub_rev (W ℓ s) y
      linarith
    · exact hy
  have hRℓ : ∀ ℓ, max (Real.log β) 10 ≤ R ℓ := fun ℓ => by
    have : 0 ≤ ‖P i - P ℓ‖ := norm_nonneg _
    exact max_le (by simp only [R]; linarith) (by simp only [R]; linarith)
  have hcard1 : ((escVneG n j β I u W Bm τ i ∩ {y | ‖y - P i‖ ≤ r}).ncard : ℝ) ≤
      ∑ ℓ ∈ F, densK (k + 2) * (R ℓ ^ 2 * Real.log (R ℓ) ^ m) := by
    have hfinU : (⋃ ℓ ∈ F, {y | ∃ x ∈ X ℓ, ‖y - x‖ ≤ 1}).Finite :=
      Set.Finite.biUnion F.finite_toSet (fun ℓ _ => nbhd_finite _ (hXfin ℓ))
    have h1 : (escVneG n j β I u W Bm τ i ∩ {y | ‖y - P i‖ ≤ r}).ncard ≤
        ∑ ℓ ∈ F, ({y | ∃ x ∈ X ℓ, ‖y - x‖ ≤ 1} : Set (Fin (k + 2) → ℤ)).ncard :=
      (Set.ncard_le_ncard hsub hfinU).trans (ncard_biUnion_le F _)
    have h1' : ((escVneG n j β I u W Bm τ i ∩ {y | ‖y - P i‖ ≤ r}).ncard : ℝ) ≤
        ∑ ℓ ∈ F, ((({y | ∃ x ∈ X ℓ, ‖y - x‖ ≤ 1} : Set (Fin (k + 2) → ℤ)).ncard : ℕ) : ℝ) := by
      exact_mod_cast h1
    refine h1'.trans (Finset.sum_le_sum fun ℓ _ => ?_)
    have h2 : ((({y | ∃ x ∈ X ℓ, ‖y - x‖ ≤ 1} : Set (Fin (k + 2) → ℤ)).ncard : ℕ) : ℝ) ≤
        3 ^ (k + 2) * ((X ℓ).ncard : ℝ) := by
      exact_mod_cast ncard_nbhd_le _ (hXfin ℓ)
    have h3 := escVisitsG_b hτ (n := n) (j := j) (I := I) (P := P) (W := W) (Bm := Bm) ℓ hβ (hRℓ ℓ)
    calc _ ≤ 3 ^ (k + 2) * ((X ℓ).ncard : ℝ) := h2
      _ ≤ 3 ^ (k + 2) * (6 * 33 ^ (k + 2) * R ℓ ^ 2 * Real.log (R ℓ) ^ m) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = densK (k + 2) * (R ℓ ^ 2 * Real.log (R ℓ) ^ m) := by unfold densK; ring
  have hcardF : (F.card : ℝ) ≤ (n : ℝ) ^ 3 := by
    have : F.card ≤ n ^ 3 := by
      refine (Finset.card_le_card (Finset.erase_subset _ _)).trans ?_
      simp only [Nat.card_Icc, Nat.add_sub_cancel]; exact hI
    exact_mod_cast this
  have hdist : ∀ ℓ ∈ F, ‖P i - P ℓ‖ ≤ 3 * 2 ^ j / 16 := fun ℓ hℓ => by
    simp only [hF, Finset.mem_erase, Finset.mem_Icc] at hℓ
    exact point_dist_le hℓ.2.1 hℓ.2.2 hi1 hiI hIlam
  have hK0 := densK_pos (k + 2)
  have hn20 : (16 : ℝ) ≤ (n : ℝ) ^ 20 := by
    have : (4 : ℝ) ^ 20 ≤ (n : ℝ) ^ 20 := pow_le_pow_left₀ (by norm_num) hn4r 20
    have : (16 : ℝ) ≤ 4 ^ 20 := by norm_num
    linarith
  by_cases hrj : r ≤ 2 ^ j
  · -- case A
    have hRle : ∀ ℓ ∈ F, R ℓ ≤ 4 * (n : ℝ) ^ 20 := fun ℓ hℓ => by
      have := hdist ℓ hℓ
      simp only [R]; linarith
    have hbound : ∑ ℓ ∈ F, densK (k + 2) * (R ℓ ^ 2 * Real.log (R ℓ) ^ m) ≤
        ∑ ℓ ∈ F, densK (k + 2) * ((4 * (n : ℝ) ^ 20) ^ 2 *
          Real.log (4 * (n : ℝ) ^ 20) ^ m) := by
      refine Finset.sum_le_sum fun ℓ hℓ => ?_
      have hR1 : 1 ≤ R ℓ := by have := hRℓ ℓ; linarith [le_max_right (Real.log β) 10]
      have := F_mono (m := m) hR1 (hRle ℓ hℓ)
      exact mul_le_mul_of_nonneg_left this hK0.le
    refine hcard1.trans (hbound.trans ?_)
    rw [Finset.sum_const, nsmul_eq_mul]
    · have := hA r hr
      calc (F.card : ℝ) * (densK (k + 2) * ((4 * (n : ℝ) ^ 20) ^ 2 *
            Real.log (4 * (n : ℝ) ^ 20) ^ m)) ≤
          (n : ℝ) ^ 3 * (densK (k + 2) * ((4 * (n : ℝ) ^ 20) ^ 2 *
            Real.log (4 * (n : ℝ) ^ 20) ^ m)) := by
            apply mul_le_mul_of_nonneg_right hcardF
            have : 0 ≤ Real.log (4 * (n : ℝ) ^ 20) := Real.log_nonneg (by linarith)
            positivity
        _ = _ := by ring
        _ ≤ _ := this
  · -- case B
    push Not at hrj
    have hRle : ∀ ℓ ∈ F, R ℓ ≤ 3 * r := fun ℓ hℓ => by
      have := hdist ℓ hℓ
      simp only [R]; linarith
    have hbound : ∑ ℓ ∈ F, densK (k + 2) * (R ℓ ^ 2 * Real.log (R ℓ) ^ m) ≤
        ∑ ℓ ∈ F, densK (k + 2) * ((3 * r) ^ 2 * Real.log (3 * r) ^ m) := by
      refine Finset.sum_le_sum fun ℓ hℓ => ?_
      have hR1 : 1 ≤ R ℓ := by have := hRℓ ℓ; linarith [le_max_right (Real.log β) 10]
      have := F_mono (m := m) hR1 (hRle ℓ hℓ)
      exact mul_le_mul_of_nonneg_left this hK0.le
    refine hcard1.trans (hbound.trans ?_)
    · rw [Finset.sum_const, nsmul_eq_mul]
      have hn3 : (n : ℝ) ^ 3 ≤ r ^ (3 / 20 : ℝ) := by
        have h0 : (0 : ℝ) < n := by linarith
        have e : (n : ℝ) ^ 3 = ((n : ℝ) ^ 20) ^ (3 / 20 : ℝ) := by
          rw [← Real.rpow_natCast, ← Real.rpow_natCast (n : ℝ) 20, ← Real.rpow_mul h0.le]
          norm_num
        rw [e]
        exact Real.rpow_le_rpow (by positivity) (hj1.trans hrj.le) (by norm_num)
      have := hB r hrj.le (F.card : ℝ) (Nat.cast_nonneg _) (hcardF.trans hn3)
      calc (F.card : ℝ) * (densK (k + 2) * ((3 * r) ^ 2 * Real.log (3 * r) ^ m)) =
          (F.card : ℝ) * densK (k + 2) * ((3 * r) ^ 2 * Real.log (3 * r) ^ m) := by ring
        _ ≤ _ := this

/-- Density of the explored walks around p_i. -/
theorem escDensityG (k : ℕ) : ∃ nD : ℕ, 4 ≤ nD ∧ ∀ {n j : ℕ} {β : ℝ} {I : ℕ}
    {u : Fin (k + 2) → ℤ} {W : ℕ → ℝ → Fin (k + 2) → ℤ} {Bm : Set (Fin (k + 2) → ℤ)}
    {τ : ℕ → ℝ} {i : ℕ}, EscBefore n j β I (escPoint n j u) W Bm τ →
    nD ≤ n → Real.exp 2 ≤ Real.log β → Real.log β ≤ (n : ℝ) ^ 17 / 7 →
    (n : ℝ) ^ 20 ≤ 2 ^ j → (2 : ℝ) ^ j < 2 * n ^ 20 → I ≤ n ^ 3 →
    16 * (I * escLambda n) ≤ 3 * 2 ^ j → 1 ≤ i → i ≤ I →
    (∀ ℓ, W ℓ 0 = escPoint n j u ℓ) →
    (∀ ℓ t, 0 < t → ∀ ε > 0, ∃ s, t - ε < s ∧ s < t ∧ ‖W ℓ t - W ℓ s‖ ≤ 1) →
    escVneG n j β I u W Bm τ i ⊆ {y | (n : ℝ) ^ 17 / 6 - 2 < ‖y - escPoint n j u i‖} ∧
    ∀ r : ℝ, (n : ℝ) ^ 17 / 7 ≤ r →
      ((escVneG n j β I u W Bm τ i ∩ {y | ‖y - escPoint n j u i‖ ≤ r}).ncard : ℝ) ≤
        r ^ (8 / 3 : ℝ) / 2 := by
  obtain ⟨NA, hNA⟩ := caseA_arith (k + 2)
  obtain ⟨Y, hY1, hY⟩ := caseB_arith (k + 2)
  refine ⟨max (max 4 NA) ⌈Y⌉₊, le_trans (le_max_left _ _) (le_max_left _ _), ?_⟩
  intro n j β I u W Bm τ i hτ hn hβ hlb hj1 hj2 hI hIlam hi1 hiI hW0 hnn
  have hn4 : 4 ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hNAn : NA ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hYn : Y ≤ n := le_trans (Nat.le_ceil Y) (by exact_mod_cast le_trans (le_max_right _ _) hn)
  have hn4r : (4 : ℝ) ≤ n := by exact_mod_cast hn4
  refine ⟨escDensityG_incl hτ (by omega) hi1 hiI hW0 hnn, fun r hr => ?_⟩
  refine escDensityG_count hτ hβ hlb hn4 hj1 hj2 hI hIlam hi1 hiI
    (fun r hr => hNA n hNAn hn4 r hr) (fun r hr x hx0 hxr => ?_) hr
  have hrY : Y ≤ r := by
    have h1 : (n : ℝ) ≤ (n : ℝ) ^ 20 := by
      calc (n : ℝ) = (n : ℝ) ^ 1 := by simp
        _ ≤ (n : ℝ) ^ 20 := pow_le_pow_right₀ (by linarith) (by norm_num)
    linarith
  exact hY r hrY x hx0 hxr

end ElboimSly.Paper.Escape
