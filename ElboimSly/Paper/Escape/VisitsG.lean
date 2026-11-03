/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Escape.Visits
public import Mathlib

/-!
# Vertices visited by an explored walk for an arbitrary family of stopping times

The statements of `escVisits_a`, `escVisits_b` with `escTauSeq` replaced by a family `τ` that
satisfies `EscBefore`: none of the conditions (1)-(7) holds strictly before `τ i`.  This applies to
the stopping lengths of the plan `𝒫_𝒜` (see `EscBefore` and `Plan53Env`).
-/

@[expose] public section

namespace ElboimSly.Paper.Escape

open ElboimSly.Paper

variable {k n j : ℕ} {β : ℝ} {I : ℕ} {P : ℕ → Fin (k + 2) → ℤ} {W : ℕ → ℝ → Fin (k + 2) → ℤ}
  {Bm : Set (Fin (k + 2) → ℤ)} {τ : ℕ → ℝ}

/-- None of the conditions (1)-(7) holds strictly before `τ i`. -/
def EscBefore (n j : ℕ) (β : ℝ) (I : ℕ) (P : ℕ → Fin (k + 2) → ℤ)
    (W : ℕ → ℝ → Fin (k + 2) → ℤ) (Bm : Set (Fin (k + 2) → ℤ)) (τ : ℕ → ℝ) : Prop :=
  ∀ i t, 0 < t → t < τ i →
    ¬ EscStopCond n j β I P W Bm (fun ℓ => if ℓ < i then τ ℓ else 0) i t

/-- Vertices visited by an explored walk (a). -/
theorem escVisitsG_a (hτ : EscBefore n j β I P W Bm τ) (ℓ : ℕ) {R : ℝ} (hR : max (Real.log β) 10 ≤ R) {s : ℝ} (_hs0 : 0 ≤ s)
    (hsτ : s < τ ℓ) (hin : ‖W ℓ s - P ℓ‖ ≤ R) :
    s < 4 * R ^ 2 * Real.log R ^ 2 := by
  by_contra hge
  push Not at hge
  have hR10 : 10 ≤ R := le_trans (le_max_right _ _) hR
  have hlb : Real.log β ≤ R := le_trans (le_max_left _ _) hR
  have hRT := R_le_T hR10
  have hs : 0 < s := by linarith
  apply hτ _ _ hs hsτ
  refine Or.inr (Or.inl ⟨by linarith, ?_⟩)
  exact hin.trans (sqrt_div_log_ge hR10 hge)

/-- Before `τ_ℓ`, condition (3) fails: displacements over windows are `< ln² max(s, ln β)`. -/
lemma window_boundG (hτ : EscBefore n j β I P W Bm τ) (ℓ : ℕ) (_hβ : Real.exp 2 ≤ Real.log β) {s : ℝ} (hs0 : 0 < s)
    (hsτ : s < τ ℓ) :
    ‖W ℓ s - W ℓ (⌊s⌋₊ : ℝ)‖ < Real.log (max s (Real.log β)) ^ 2 := by
  by_contra hge
  push Not at hge
  apply hτ _ _ hs0 hsτ
  refine Or.inr (Or.inr (Or.inl ?_))
  unfold pathTfast
  refine iInf₂_le_of_le s ⟨hs0, (⌊s⌋₊ : ℝ), ?_, ?_, ?_⟩ le_rfl
  · have := Nat.lt_floor_add_one s; linarith
  · exact Nat.floor_le hs0.le
  · rwa [max_eq_left (Nat.cast_nonneg _)]

/-- Vertices visited by an explored walk (b). -/
theorem escVisitsG_b (hτ : EscBefore n j β I P W Bm τ) (ℓ : ℕ) (hβ : Real.exp 2 ≤ Real.log β) {R : ℝ}
    (hR : max (Real.log β) 10 ≤ R) :
    (({x | ∃ s, 0 ≤ s ∧ s ≤ τ ℓ ∧ W ℓ s = x} ∩
        {x | ‖x - P ℓ‖ ≤ R}).ncard : ℝ) ≤
      6 * 33 ^ (k + 2) * R ^ 2 * Real.log R ^ (2 * (k + 2) + 2) := by
  classical
  have hR10 : 10 ≤ R := le_trans (le_max_right _ _) hR
  have hlb : Real.log β ≤ R := le_trans (le_max_left _ _) hR
  set T : ℝ := 4 * R ^ 2 * Real.log R ^ 2 with hT
  have hRT : R ≤ T := R_le_T hR10
  have hT0 : 0 < T := by linarith
  have hlR : 2 ≤ Real.log R := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9
    have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    nlinarith [Real.exp_pos 1]
  -- the radius
  set L : ℝ := Real.log T ^ 2 with hL
  have hL0 : 0 ≤ L := sq_nonneg _
  have hlogT : Real.log T ≤ 4 * Real.log R := by
    have h1 : T ≤ R ^ 4 := by
      have h0 := log_le_half_self hR10
      have h2 : (2 * Real.log R) ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (by linarith) h0 2
      calc T = R ^ 2 * (2 * Real.log R) ^ 2 := by rw [hT]; ring
        _ ≤ R ^ 2 * R ^ 2 := mul_le_mul_of_nonneg_left h2 (sq_nonneg R)
        _ = R ^ 4 := by ring
    calc Real.log T ≤ Real.log (R ^ 4) := Real.log_le_log hT0 h1
      _ = 4 * Real.log R := by rw [Real.log_pow]; norm_num
  have hlogT0 : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  have hL16 : L ≤ 16 * Real.log R ^ 2 := by
    rw [hL]; nlinarith
  -- the covering set
  let S : Finset (Fin (k + 2) → ℤ) :=
    insert (W ℓ (τ ℓ))
      ((Finset.range (⌊T⌋₊ + 1)).biUnion fun q => ballFin (W ℓ (q : ℝ)) ⌊L⌋₊)
  have hsub : ({x | ∃ s, 0 ≤ s ∧ s ≤ τ ℓ ∧ W ℓ s = x} ∩
      {x | ‖x - P ℓ‖ ≤ R}) ⊆ ↑S := by
    rintro x ⟨⟨s, hs0, hsτ, rfl⟩, hxR⟩
    simp only [Set.mem_ofPred_eq] at hxR
    rcases hsτ.eq_or_lt with heq | hlt
    · rw [heq]; simp [S]
    · have hsT : s < T := escVisitsG_a hτ ℓ hR hs0 hlt hxR
      simp only [S, Finset.coe_insert, Finset.coe_biUnion, Finset.coe_range, Set.mem_insert_iff,
        Set.mem_iUnion, Set.mem_Iio, Finset.mem_coe]
      right
      refine ⟨⌊s⌋₊, ?_, ?_⟩
      · have : ⌊s⌋₊ ≤ ⌊T⌋₊ := Nat.floor_le_floor hsT.le
        omega
      · rcases hs0.eq_or_lt with h0 | hpos
        · subst h0
          apply mem_ballFin hL0
          simpa using hL0
        · apply mem_ballFin hL0
          have hw := window_boundG hτ (ℓ := ℓ) hβ hpos hlt
          have hmax : max s (Real.log β) ≤ T := max_le hsT.le (hlb.trans hRT)
          have hge : Real.exp 2 ≤ max s (Real.log β) := le_trans hβ (le_max_right _ _)
          have hpos2 : 0 < max s (Real.log β) := lt_of_lt_of_le (Real.exp_pos 2) hge
          have hl2 : 0 ≤ Real.log (max s (Real.log β)) := by
            apply Real.log_nonneg; have := Real.add_one_le_exp 2; linarith
          have hlog : Real.log (max s (Real.log β)) ≤ Real.log T := Real.log_le_log hpos2 hmax
          have : Real.log (max s (Real.log β)) ^ 2 ≤ L := by
            rw [hL]; exact pow_le_pow_left₀ hl2 hlog 2
          exact (hw.trans_le this).le
  have hfin : (({x | ∃ s, 0 ≤ s ∧ s ≤ τ ℓ ∧ W ℓ s = x} ∩
      {x | ‖x - P ℓ‖ ≤ R}).ncard) ≤ S.card := by
    calc _ ≤ (↑S : Set (Fin (k + 2) → ℤ)).ncard := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
      _ = S.card := Set.ncard_coe_finset _
  have hcard : S.card ≤ 1 + (⌊T⌋₊ + 1) * (2 * ⌊L⌋₊ + 1) ^ (k + 2) := by
    refine (Finset.card_insert_le _ _).trans ?_
    have h1 : ((Finset.range (⌊T⌋₊ + 1)).biUnion fun q => ballFin (W ℓ (q : ℝ)) ⌊L⌋₊).card ≤
        (⌊T⌋₊ + 1) * (2 * ⌊L⌋₊ + 1) ^ (k + 2) := by
      refine (Finset.card_biUnion_le).trans ?_
      refine le_of_eq ?_
      calc ∑ q ∈ Finset.range (⌊T⌋₊ + 1), (ballFin (W ℓ (q : ℝ)) ⌊L⌋₊).card
          = ∑ q ∈ Finset.range (⌊T⌋₊ + 1), (2 * ⌊L⌋₊ + 1) ^ (k + 2) := by
            simp [card_ballFin]
        _ = (⌊T⌋₊ + 1) * (2 * ⌊L⌋₊ + 1) ^ (k + 2) := by simp
    omega
  -- numerics
  have hlR1 : 1 ≤ Real.log R ^ 2 := by nlinarith
  have hfl : (⌊L⌋₊ : ℝ) ≤ L := Nat.floor_le hL0
  have hbase : ((2 * ⌊L⌋₊ + 1 : ℕ) : ℝ) ≤ 33 * Real.log R ^ 2 := by
    push_cast; nlinarith
  have hpow : ((2 * ⌊L⌋₊ + 1 : ℕ) : ℝ) ^ (k + 2) ≤ 33 ^ (k + 2) * Real.log R ^ (2 * (k + 2)) := by
    calc ((2 * ⌊L⌋₊ + 1 : ℕ) : ℝ) ^ (k + 2) ≤ (33 * Real.log R ^ 2) ^ (k + 2) :=
          pow_le_pow_left₀ (by positivity) hbase _
      _ = 33 ^ (k + 2) * Real.log R ^ (2 * (k + 2)) := by rw [mul_pow, ← pow_mul]
  have hfT : ((⌊T⌋₊ : ℝ) + 1) ≤ 5 * R ^ 2 * Real.log R ^ 2 := by
    have := Nat.floor_le hT0.le
    nlinarith
  have hpos33 : (0 : ℝ) < 33 ^ (k + 2) * Real.log R ^ (2 * (k + 2)) := by positivity
  calc (_ : ℝ) ≤ (S.card : ℝ) := by exact_mod_cast hfin
    _ ≤ 1 + ((⌊T⌋₊ : ℝ) + 1) * ((2 * ⌊L⌋₊ + 1 : ℕ) : ℝ) ^ (k + 2) := by exact_mod_cast hcard
    _ ≤ 1 + (5 * R ^ 2 * Real.log R ^ 2) * (33 ^ (k + 2) * Real.log R ^ (2 * (k + 2))) := by
        gcongr
    _ ≤ _ := by
        have : 1 ≤ R ^ 2 * Real.log R ^ 2 * (33 ^ (k + 2) * Real.log R ^ (2 * (k + 2))) := by
          have h1 : 1 ≤ R ^ 2 := by nlinarith
          have h2 : (1 : ℝ) ≤ 33 ^ (k + 2) * Real.log R ^ (2 * (k + 2)) := by
            have : (1 : ℝ) ≤ 33 ^ (k + 2) := one_le_pow₀ (by norm_num)
            have h3 : (1 : ℝ) ≤ Real.log R ^ (2 * (k + 2)) := one_le_pow₀ (by linarith)
            nlinarith
          nlinarith
        have e : Real.log R ^ (2 * (k + 2) + 2) = Real.log R ^ 2 * Real.log R ^ (2 * (k + 2)) := by
          rw [pow_add]; ring
        rw [e]
        nlinarith

end ElboimSly.Paper.Escape
