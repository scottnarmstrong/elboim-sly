/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycFarCount
public import ElboimSly.Foundations.Cyclic.DrivenMain
public import Mathlib

/-!
# ES22 Lemma 2.2, Steps 2-3 (driven form): the jumps of `w^x` are at most twice those of `x`

ES22 Lemma 2.2, Steps 2 and 3, in the driven construction. By closing for the driven walk
(a), a jump of `w = w^x` at a time `t ≤ treg^x` with no earlier jump in its class `t + βℤ` is a
jump of `x` (D2), and by (d) each class contains at most two jumps of `w` in `(0, t]`. Hence for
`r ≤ treg^x`: `#jumps(w, (0, r]) ≤ 2 · #jumps(x, (0, r])`.
-/

@[expose] public section

open Filter Topology Set MeasureTheory
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

variable {d : ℕ} {x : ℝ≥0 → Fin d → ℤ} {β : ℝ≥0}

/-- Three jumps of one class contradict closing for the driven walk (d). -/
theorem no_three_in_class {w : ℝ≥0 → Fin d → ℤ} {r : ℝ≥0}
    (hD : ∀ t0 : ℝ≥0, {s : ℝ≥0 | s ∈ CDisc w ∧ s ≤ r ∧ ∃ j : ℤ, (s : ℝ) = t0 + j * β}.ncard ≤ 2)
    (hfin : (CDisc w ∩ Iic r).Finite) {p q s : ℝ≥0} (hp : p ∈ CDisc w) (hq : q ∈ CDisc w)
    (hs : s ∈ CDisc w) (hsr : s ≤ r) (hpq : p < q) (hqs : q < s) {a b : ℕ}
    (hqa : (q : ℝ) = p + a * β) (hsb : (s : ℝ) = p + b * β) : False := by
  have hsub : ({p, q, s} : Set ℝ≥0) ⊆
      {s : ℝ≥0 | s ∈ CDisc w ∧ s ≤ r ∧ ∃ j : ℤ, (s : ℝ) = p + j * β} := by
    intro u hu
    simp only [mem_insert_iff, mem_singleton_iff] at hu
    rcases hu with h | h | h
    · rw [h]; exact ⟨hp, (hpq.trans hqs).le.trans hsr, 0, by simp⟩
    · rw [h]; exact ⟨hq, hqs.le.trans hsr, a, by rw [hqa]; push_cast; ring⟩
    · rw [h]; exact ⟨hs, hsr, b, by rw [hsb]; push_cast; ring⟩
  have hfin' : {s : ℝ≥0 | s ∈ CDisc w ∧ s ≤ r ∧ ∃ j : ℤ, (s : ℝ) = p + j * β}.Finite :=
    hfin.subset fun u hu => ⟨hu.1, hu.2.1⟩
  have h3 : ({p, q, s} : Set ℝ≥0).ncard = 3 := by
    rw [Set.ncard_insert_of_notMem, Set.ncard_pair (ne_of_lt hqs)]
    simp only [mem_insert_iff, mem_singleton_iff, not_or]
    exact ⟨hpq.ne, (hpq.trans hqs).ne⟩
  have := Set.ncard_le_ncard hsub hfin'
  have h2 := hD p
  omega

/-- For `r ≤ treg^x`, the walk `w^x` has at most twice as many jumps in `(0, r]` as `x`. -/
theorem card_jumps_driven_le (hx : IsDrivingPath x) (hβ : 0 < β)
    (hi : ∀ s ∈ CDisc x, ∀ s' ∈ CDisc x, ∀ k : ℕ, 1 ≤ k → s' ≠ s + k * β) {r : ℝ≥0}
    (hr : (r : ℝ≥0∞) ≤ drivenTreg β x) :
    (CDisc (drivenWalk β x) ∩ Iic r).ncard ≤ 2 * (CDisc x ∩ Iic r).ncard := by
  classical
  obtain ⟨-, -, hA3, -, -, -, -, hD1, -, -⟩ := drivenWalk_closing hx hβ hi
  have hD : ∀ t0 : ℝ≥0, {s : ℝ≥0 | s ∈ CDisc (drivenWalk β x) ∧ s ≤ r ∧
      ∃ j : ℤ, (s : ℝ) = t0 + j * β}.ncard ≤ 2 := fun t0 => hD1 r hr t0
  set w := drivenWalk β x with hw
  have hwreg : IsRegPath w := drivenWalk_isRegPath hx.toIsRegPath hβ
  have hfin : (CDisc w ∩ Iic r).Finite := hwreg.fin r
  set S := CDisc w ∩ Iic r with hS
  set R : Set ℝ≥0 := {s ∈ S | ∀ k, IsDelayIdx β s k → s - k * β ∉ CDisc w} with hR
  have hRsub : R ⊆ CDisc x ∩ Iic r := fun s hs => by
    refine ⟨hA3 s hs.1.1 ((ENNReal.coe_le_coe.2 hs.1.2).trans hr) hs.2, hs.1.2⟩
  have hRfin : (CDisc x ∩ Iic r).Finite := hx.fin r
  have hRle : R.ncard ≤ (CDisc x ∩ Iic r).ncard := Set.ncard_le_ncard hRsub hRfin
  -- the predecessor in the class
  have hex : ∀ s ∈ S \ R, ∃ k : ℕ, IsDelayIdx β s k ∧ s - k * β ∈ CDisc w := fun s hs => by
    by_contra hc
    push Not at hc
    exact hs.2 ⟨hs.1, fun k hk => hc k hk⟩
  let pred : ℝ≥0 → ℝ≥0 := fun s =>
    if h : s ∈ S \ R then s - (hex s h).choose * β else s
  have hpred : ∀ s (h : s ∈ S \ R), pred s = s - (hex s h).choose * β := fun s h => by
    simp only [pred, dite_eq_left h]
  have hpred_spec : ∀ s (h : s ∈ S \ R), IsDelayIdx β s (hex s h).choose ∧
      s - (hex s h).choose * β ∈ CDisc w := fun s h => (hex s h).choose_spec
  have hcoe : ∀ s (h : s ∈ S \ R), (s : ℝ) = (pred s : ℝ) + (hex s h).choose * β := fun s h => by
    rw [hpred s h]
    have hk := (hpred_spec s h).1
    have : ((hex s h).choose : ℝ≥0) * β ≤ s := hk.2
    rw [NNReal.coe_sub this]
    push_cast
    ring
  have hpos : ∀ s (h : s ∈ S \ R), pred s < s := fun s h => by
    have hk := (hpred_spec s h).1
    rw [hpred s h]
    have hk1 : 0 < ((hex s h).choose : ℝ≥0) * β := by
      have : (0 : ℝ≥0) < (hex s h).choose := by exact_mod_cast hk.1
      positivity
    exact tsub_lt_self (lt_of_lt_of_le hk1 hk.2) hk1
  have hpredS : ∀ s (h : s ∈ S \ R), pred s ∈ S := fun s h => by
    refine ⟨?_, ?_⟩
    · rw [hpred s h]; exact (hpred_spec s h).2
    · exact (hpos s h).le.trans h.1.2
  -- pred maps into R
  have hpredR : ∀ s (h : s ∈ S \ R), pred s ∈ R := fun s h => by
    refine ⟨hpredS s h, fun k hk hmem => ?_⟩
    have hp := hpredS s h
    have hk' := hpred_spec s h
    -- `p' = pred s - kβ` is an earlier jump of the class
    have hp'le : pred s - k * β ≤ pred s := tsub_le_self
    have hp'lt : pred s - k * β < pred s := by
      have hk1 : 0 < (k : ℝ≥0) * β := by
        have : (0 : ℝ≥0) < k := by exact_mod_cast hk.1
        positivity
      exact tsub_lt_self (lt_of_lt_of_le hk1 hk.2) hk1
    refine no_three_in_class hD hfin hmem hp.1 h.1.1 h.1.2 hp'lt (hpos s h) (a := k)
      (b := k + (hex s h).choose) ?_ ?_
    · have : (k : ℝ≥0) * β ≤ pred s := hk.2
      rw [NNReal.coe_sub this]
      push_cast
      ring
    · have : (k : ℝ≥0) * β ≤ pred s := hk.2
      rw [NNReal.coe_sub this, hcoe s h]
      push_cast
      ring
  -- pred is injective on `S \ R`
  have hinj : Set.InjOn pred (S \ R) := fun s1 h1 s2 h2 heq => by
    by_contra hne
    wlog hlt : s1 < s2 generalizing s1 s2
    · exact this s2 h2 s1 h1 heq.symm (Ne.symm hne) (lt_of_le_of_ne (not_lt.1 hlt) (Ne.symm hne))
    have hp := hpredS s1 h1
    have hp2 : pred s2 = pred s1 := heq.symm
    refine no_three_in_class hD hfin hp.1 h1.1.1 h2.1.1 h2.1.2 (hpos s1 h1) hlt
      (a := (hex s1 h1).choose) (b := (hex s2 h2).choose) (hcoe s1 h1) ?_
    rw [hcoe s2 h2, hp2]
  have hle : (S \ R).ncard ≤ R.ncard :=
    Set.ncard_le_ncard_of_injOn pred (fun s h => hpredR s h) hinj (hRfin.subset hRsub)
  have hsplit : S.ncard ≤ R.ncard + (S \ R).ncard := by
    have := Set.ncard_union_le R (S \ R)
    have hSsub : S ⊆ R ∪ (S \ R) := fun s hs => by
      by_cases h : s ∈ R
      · exact Or.inl h
      · exact Or.inr ⟨hs, h⟩
    exact (Set.ncard_le_ncard hSsub ((hRfin.subset hRsub).union (hfin.sdiff))).trans this
  omega

end ElboimSly.Cyclic

end
