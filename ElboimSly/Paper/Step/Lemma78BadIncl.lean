/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Heavy.TauBad
public import ElboimSly.Paper.Step.Lemma78Restart
public import ElboimSly.Paper.Step.Lemma78TauBad
public import ElboimSly.Paper.Step.Lemma78Shift
public import ElboimSly.Paper.Heavy.MeasStop5
public import ElboimSly.Paper.Heavy.Twelve
public import ElboimSly.Frozen.Defs.IndScaleReduced
public import Mathlib

/-!
# Inclusions into the bad blocks of `ℬ*`

Discovered bad blocks for two walks, "Each counted block is bad and near a centre" (ES22 §7), and
the pathwise part of "Counting".  On `Ω ∩ Γ₁₂` (with `ν` good, `W₁ = W^ν_{0,0}`,
`W₂ = W^ν_{u,q}`, `w₂ = W₂ - u = W^{N*}_{0,0}`):

* blocks bad by time `T` for `W₁` lie in `S₁ = {ι ∈ ℬ* : ι bad for ν}`;
* cross-bad blocks lie in `S₁` (failure of (GB3), witness of norm `< 5^n`);
* blocks bad for `w₂` lie in `S₂ = {ι ∈ ℬ* : ι bad for N*}`.

Hence `τ'_bad ≤ T` forces `S₁` or `S₂` to be too large (`step78_det`).
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace ElboimSly.Paper.Step

open ElboimSly ElboimSly.Paper ElboimSly.Paper.Heavy ElboimSly.Cyclic ElboimSly.Interchange

variable {d n₀ n : ℕ} {E : HeavyEscConsts} {β t₀ : ℝ} [Fact (0 < β)] {ν : Measure (RingSpace d β)}

/-- A block within `2^{k+2}` of a point of norm `< 5^n` lies in `ℬ*`. -/
theorem mem_heavyBstar_of_near (hT : HeavyT d n₀ E n) (hd : 5 ≤ d) {ι : Fin d → ℤ}
    {z : Fin d → ℤ} (hz : ‖z‖ < 5 ^ n)
    (hB : latDist z (heavyBlock (heavyLevel d n) ι) ≤ (2 : ℝ) ^ (heavyLevel d n + 2)) :
    ι ∈ heavyBstar d n := by
  have hn : 0 < n := by have := hT.t4; omega
  have hk : heavyLevel d n ≤ n := heavyLevel_le_self (by omega) n
  have h2k : (2 : ℝ) ^ (heavyLevel d n + 2) ≤ 5 ^ n := by
    have h1 : (2 : ℝ) ^ (heavyLevel d n + 2) ≤ 4 ^ (n + 1) := by
      calc (2 : ℝ) ^ (heavyLevel d n + 2) ≤ 2 ^ (n + 2) :=
            pow_le_pow_right₀ (by norm_num) (by omega)
        _ ≤ 4 ^ (n + 1) := by
            rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul]
            exact pow_le_pow_right₀ (by norm_num) (by omega)
    have h3 := hT.t3
    have : (4 : ℝ) ^ (n + 1) ≤ (n : ℝ) ^ 3 * (4 ^ (n + 1) + 1) := by
      have hn1 : (1 : ℝ) ≤ (n : ℝ) ^ 3 := one_le_pow₀ (by exact_mod_cast hn)
      nlinarith [pow_pos (by norm_num : (0 : ℝ) < 4) (n + 1)]
    linarith
  have hne := heavyBlock_nonempty (d := d) (heavyLevel d n) ι
  obtain ⟨a, haB, ha⟩ := exists_le_of_latDist_le (R := 2 ^ (heavyLevel d n + 2)) hne
    (by exact_mod_cast hB)
  have ha' : ‖z - a‖ ≤ (2 : ℝ) ^ (heavyLevel d n + 2) := by exact_mod_cast ha
  show latDist (0 : Fin d → ℤ) (heavyBlock (heavyLevel d n) ι) ≤ ((2 * 5 ^ n : ℕ) : ℝ)
  refine (latDist_le_norm_of_mem haB 0).trans ?_
  have : ‖(0 : Fin d → ℤ) - a‖ ≤ ‖z‖ + ‖z - a‖ := by
    calc ‖(0 : Fin d → ℤ) - a‖ = ‖-(a)‖ := by simp
      _ = ‖-(z) + (z - a)‖ := by congr 1; abel
      _ ≤ ‖-(z)‖ + ‖z - a‖ := norm_add_le _ _
      _ = _ := by rw [norm_neg]
  push_cast
  linarith

omit [Fact (0 < β)] in
/-- `¬ cycClosesBy` gives `T < T(w)` for `w = W_{y,q} - y`. -/
theorem closingTime_gt_of_not_closesBy (hβ : 0 < β) {T : ℝ} (hT : 0 ≤ T) (y : Fin d → ℤ) (q : ℝ)
    (h : ¬ cycClosesBy ν y q T) :
    ENNReal.ofReal T < cycClosingTime β (fun s : ℝ => cycWalk ν y q s - y) := by
  refine lt_of_not_ge fun hle => h ?_
  obtain ⟨ℓ, h1, h2, h3⟩ := (cycClosingTime_le_iff hβ hT).1 hle
  exact ⟨ℓ, h1, h2, sub_eq_zero.1 h3⟩

omit [Fact (0 < β)] in
/-- `Γ` and `T < T(w)`, `T ≤ t_n` give `T < τ_fast`. -/
theorem lt_tfast_of_gamma {w : ℝ → Fin d → ℤ} {T : ℝ} (hTn : T ≤ indScale t₀ n)
    (hcl : ENNReal.ofReal T < cycClosingTime β w) (hΓ : heavyGamma d β t₀ n w) :
    ENNReal.ofReal T < pathTfastCube w n := by
  have h1 : ENNReal.ofReal T ≤ min (cycClosingTime β w) (ENNReal.ofReal (indScale t₀ n)) :=
    le_min hcl.le (ENNReal.ofReal_le_ofReal hTn)
  exact lt_of_le_of_lt h1 (lt_of_lt_of_le hΓ.2 (min_le_left _ _))

/-- Cross-bad blocks lie in `ℬ*` and are bad for `ν`. -/
theorem crossBad_subset_bstar (hd : 5 ≤ d) (hT : HeavyT d n₀ E n) (hν : Good ν) {q T : ℝ}
    {u : Fin d → ℤ} (_hT0 : 0 ≤ T) (hT4 : T ≤ (4 : ℝ) ^ (n + 1)) (htk : 0 ≤ heavyTkPrime d t₀ n)
    (hfast : ENNReal.ofReal T < pathTfastCube (fun s : ℝ => cycWalk ν 0 0 s) n)
    {t : ℝ} {ι : Fin d → ℤ}
    (hbad : Step78CrossBad d β t₀ n q T (fun s : ℝ => cycWalk ν 0 0 s)
      (fun s : ℝ => cycWalk ν u q s) ι t) :
    ι ∈ heavyBstar d n ∧ HeavyBlockBad d β t₀ n ν ι := by
  refine ⟨?_, hν, not_heavyBlockGood_of_crossBad hν hbad⟩
  have hbad' := hbad
  unfold Step78CrossBad at hbad'
  dsimp only at hbad'
  obtain ⟨a, ha, b, hb, h1, -, h3, -⟩ := hbad'
  have ha0 : 0 ≤ a := ha.1
  have haT : a ≤ T := by linarith
  have hnorm : ‖cycWalk ν 0 0 a‖ < 5 ^ n := norm_lt_five_pow_of_lt_pathTfastCube
    (w := fun s : ℝ => cycWalk ν 0 0 s) (isCyclicPath_cycWalk hν) hT.t3
    (by have := hT.t4; omega) ha0 (haT.trans hT4)
    (lt_of_le_of_lt (ENNReal.ofReal_le_ofReal haT) hfast)
  exact mem_heavyBstar_of_near hT hd hnorm h3

/-- Discovered bad blocks for two walks, the pathwise part: on `Ω ∩ Γ₁₂ ∩ {τ'_bad ≤ T}`, one of the two
environments has too many (resp. some) bad blocks in `ℬ*`. -/
theorem step78_det (hd : 5 ≤ d) (ht1 : 1 < t₀) (ht4 : t₀ ≤ 4) (hT : HeavyT d n₀ E n)
    (hν : Good ν) (u : Fin d → ℤ) (q : ℝ)
    (hΩ : cycOmega ν 0 u 0 q (indScaleReduced t₀ n))
    (hΓ₁ : heavyGamma d β t₀ n (fun s : ℝ => cycWalk ν 0 0 s))
    (hΓ₂ : heavyGamma d β t₀ n (fun s : ℝ => cycWalk (stepShiftEnv u (-q) ν) 0 0 s))
    (hτ : step78TauBad d β t₀ n q (indScaleReduced t₀ n) u (fun s : ℝ => cycWalk ν 0 0 s)
      (fun s : ℝ => cycWalk ν u q s) ≤ ENNReal.ofReal (indScaleReduced t₀ n)) :
    (β < indScale t₀ n ^ (5 * indDelta d) →
      n < {ι | ι ∈ heavyBstar d n ∧ HeavyBlockBad d β t₀ n ν ι}.ncard ∨
      n < {ι | ι ∈ heavyBstar d n ∧
        HeavyBlockBad d β t₀ n (stepShiftEnv u (-q) ν) ι}.ncard) ∧
    (¬ β < indScale t₀ n ^ (5 * indDelta d) →
      (∃ ι ∈ heavyBstar d n, HeavyBlockBad d β t₀ n ν ι) ∨
      ∃ ι ∈ heavyBstar d n, HeavyBlockBad d β t₀ n (stepShiftEnv u (-q) ν) ι) := by
  have hβ : 0 < β := Fact.out
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by have := hT.t4; omega : 1 ≤ n)
  have htn0 : 0 ≤ indScale t₀ n := by
    unfold indScale; have : 0 < t₀ := by linarith
    positivity
  set T := indScaleReduced t₀ n with hTdef
  have hT0 : 0 ≤ T := by rw [hTdef]; unfold indScaleReduced; positivity
  have hTn : T ≤ indScale t₀ n := by
    rw [hTdef]; unfold indScaleReduced
    rw [div_le_iff₀ (by positivity)]
    have : (1 : ℝ) ≤ (n : ℝ) ^ 4 := one_le_pow₀ hn1
    nlinarith
  have hT4 : T ≤ (4 : ℝ) ^ (n + 1) := hTn.trans (indScale_le_four_pow ht4 n)
  have htk : 0 ≤ heavyTkPrime d t₀ n := by
    unfold heavyTkPrime indScale; have : 0 < t₀ := by linarith
    positivity
  have hg' := good_stepShiftEnv hν u (-q)
  have hfun : (fun s : ℝ => cycWalk (stepShiftEnv u (-q) ν) 0 0 s) =
      fun s : ℝ => cycWalk ν u q s - u := by
    funext s; exact cycWalk_stepShiftEnv_all hν u q s
  obtain ⟨-, hc1, hc2⟩ := hΩ
  have hcl₁ : ENNReal.ofReal T < cycClosingTime β (fun s : ℝ => cycWalk ν 0 0 s) := by
    simpa using closingTime_gt_of_not_closesBy (ν := ν) hβ hT0 0 0 hc1
  have hcl₂ : ENNReal.ofReal T <
      cycClosingTime β (fun s : ℝ => cycWalk (stepShiftEnv u (-q) ν) 0 0 s) := by
    rw [hfun]; exact closingTime_gt_of_not_closesBy hβ hT0 u q hc2
  have hf₁ := lt_tfast_of_gamma hTn hcl₁ hΓ₁
  have hf₂ := lt_tfast_of_gamma hTn hcl₂ hΓ₂
  have hsub₂ := bad_blocks_subset_Bstar hd ht1 ht4 hT hg' (T' := T) hT0 hTn hf₂
  have hsub₁ := bad_blocks_subset_Bstar hd ht1 ht4 hT hν hT0 hTn hf₁
  have hfin : ∀ ν' : Measure (RingSpace d β),
      {ι | ι ∈ heavyBstar d n ∧ HeavyBlockBad d β t₀ n ν' ι}.Finite := fun ν' =>
    ((Finset.finite_toSet _).subset (heavyBstar_subset d n)).subset fun ι hι => hι.1
  have key := step78_tauBad_gt (d := d) (β := β) (t₀ := t₀) (q := q) (T := T) (n := n) (u := u)
    (W₁ := fun s : ℝ => cycWalk ν 0 0 s) (W₂ := fun s : ℝ => cycWalk ν u q s)
    (S₁ := {ι | ι ∈ heavyBstar d n ∧ HeavyBlockBad d β t₀ n ν ι})
    (S₂ := {ι | ι ∈ heavyBstar d n ∧ HeavyBlockBad d β t₀ n (stepShiftEnv u (-q) ν) ι})
    (hfin _) (hfin _) hT0 ?_ ?_
  · constructor
    · intro hc
      by_contra hno
      push Not at hno
      exact absurd (key (fun _ => ⟨hno.1, hno.2⟩) (fun h => absurd hc h)) (not_lt.2 hτ)
    · intro hc
      by_contra hno
      push Not at hno
      refine absurd (key (fun h => absurd h hc) fun _ => ?_) (not_lt.2 hτ)
      constructor
      · ext ι; simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
        exact fun h => hno.1 ι h.1 h.2
      · ext ι; simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
        exact fun h => hno.2 ι h.1 h.2
  · intro t ht ι hι
    rcases hι with hι | hι
    · exact hsub₁ hι
    · exact crossBad_subset_bstar hd hT hν hT0 hT4 htk hf₁ hι
  · intro t ht ι hι
    have hm : BadByTime d β t₀ n (fun s : ℝ => cycWalk (stepShiftEnv u (-q) ν) 0 0 s) ι T := by
      rw [hfun]; exact hι.mono ht
    exact hsub₂ hm

end ElboimSly.Paper.Step

end
