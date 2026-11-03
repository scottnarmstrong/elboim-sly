/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Heavy.Claim69

/-!
# Lemma 6.8, preparations: segments and Step 1

Properties of discovered bad blocks (b) (segments before closing neither close nor merge) and
ES22 Lemma 6.8, Step 1 (the current segment stays near `B`).
-/

@[expose] public section

open Set
open scoped ENNReal

namespace ElboimSly.Paper

open ElboimSly

variable {d n₀ n : ℕ} {E : HeavyEscConsts} {β t₀ : ℝ} {w : ℝ → Fin d → ℤ} {ι : Fin d → ℤ}

theorem latDist_le_norm_of_mem {A : Set (Fin d → ℤ)} {a : Fin d → ℤ} (ha : a ∈ A)
    (u : Fin d → ℤ) : latDist u A ≤ ‖u - a‖ :=
  ciInf_le ⟨0, fun _ ⟨_, h⟩ => h ▸ norm_nonneg _⟩ (⟨a, ha⟩ : A)

/-- Properties of discovered bad blocks (b): a segment complete by time `t < T(w)` does not close. -/
theorem not_segClosed (hnr : HasNoReturn β w) {tk x t : ℝ} (hx : 0 ≤ x) (hxt : x + tk ≤ t)
    (ht : ENNReal.ofReal t < cycClosingTime β w) : ¬ SegClosed β tk w x := by
  rintro ⟨u, hu0, hutk, ⟨ℓ, hℓ⟩, hwu⟩
  refine hnr (x + u) x hx (by linarith) ?_ ⟨ℓ, by rw [hℓ]; ring⟩ hwu
  exact lt_of_le_of_lt (ENNReal.ofReal_le_ofReal (by linarith)) ht

/-- Properties of discovered bad blocks (b): segments with disjoint time intervals do not merge. -/
theorem not_segMerge (hnr : HasNoReturn β w) {tk x₁ x₂ t : ℝ} (hx₁ : 0 ≤ x₁) (hdisj : x₁ + tk < x₂)
    (hxt : x₂ + tk ≤ t) (ht : ENNReal.ofReal t < cycClosingTime β w) :
    ¬ SegMerge β tk w x₁ x₂ := by
  rintro ⟨u₁, u₂, hu₁, hu₂, hw, ℓ, hℓ⟩
  have hlt : x₁ + u₁ < x₂ + u₂ := by linarith [hu₁.2, hu₂.1]
  refine hnr (x₂ + u₂) (x₁ + u₁) (by linarith [hu₁.1]) hlt ?_ ⟨-ℓ, by push_cast; linarith [hℓ]⟩ hw.symm
  exact lt_of_le_of_lt (ENNReal.ofReal_le_ofReal (by linarith [hu₂.2])) ht

/-- ES22 Lemma 6.8, Step 1. -/
theorem eight_step1 (hd : 5 ≤ d) (ht1 : 1 < t₀) (ht4 : t₀ ≤ 4) (hβ : 0 < β) (hT : HeavyT d n₀ E n) (hw : IsCyclicPath w)
    {t : ℝ} (ht0 : 0 ≤ t) (htf : ENNReal.ofReal t < pathTfastCube w n)
    (hgood : ¬ BadByTime d β t₀ n w ι t) (hwt : w t ∈ heavyBlock (heavyLevel d n) ι)
    {tst : ℝ} (hCI : tst ∈ cycIntTimes β) (h1 : t - heavyTkPrime d t₀ n - 1 < tst)
    (h2 : tst ≤ t - heavyTkPrime d t₀ n) {s : ℝ} (hs1 : tst ≤ s) (hs2 : s ≤ t) :
    latDist (w s) (heavyBlock (heavyLevel d n) ι) ≤
      (2 : ℝ) ^ (heavyLevel d n - 1) + 2 * (n : ℝ) ^ 3 := by
  set k := heavyLevel d n with hk
  set tk := heavyTkPrime d t₀ n with htk
  set B := heavyBlock k ι with hB
  have hBne : B.Nonempty := heavyBlock_nonempty k ι
  have hn4 : 4 ≤ n := hT.t4
  have hn1 : 1 ≤ n := by omega
  have hnR : (4 : ℝ) ≤ n := by exact_mod_cast hn4
  have hn3 : (0 : ℝ) < (n : ℝ) ^ 3 := by positivity
  have hn3le : (n : ℝ) ^ 3 ≤ (n : ℝ) ^ 41 := pow_le_pow_right₀ (by linarith) (by norm_num)
  have h2k : (0 : ℝ) < 2 ^ (k - 1) := by positivity
  have hs0 : 0 ≤ s := hCI.1.trans hs1
  set y := tst + tk with hy
  have hy1 : t - 1 < y := by linarith
  have hyt : y ≤ t := by linarith
  have hk1 : 1 ≤ k := by have := hT.t1.2; omega
  have h2kk : (2 : ℝ) ^ k = 2 * 2 ^ (k - 1) := by rw [← pow_succ']; congr 1; omega
  have hs_t : ∀ s', 0 ≤ s' → s' ≤ t → t ≤ s' + 1 → latDist (w s') B < (n : ℝ) ^ 3 := by
    intro s' hs' h1' h2'
    have := norm_lt_of_close (n := n) hw hn1 htf hs' h1' h2' le_rfl
    rw [norm_sub_rev] at this
    exact lt_of_le_of_lt (latDist_le_norm_of_mem hwt (w s')) this
  by_cases hsy : y < s
  · have := hs_t s hs0 hs2 (by linarith)
    linarith
  · push Not at hsy
    set m := min (s + 1) y with hm
    obtain ⟨hc1, hc2, -, -⟩ := scales_facts_c (d := d) (n := n) ht1 ht4 hT.t1.2
    have htk2 : 2 < tk := by linarith
    have hm0 : 0 ≤ m := le_min (by linarith) (by linarith [hCI.1])
    set x := cycFloor β m with hx
    have hxCI : x ∈ cycIntTimes β := cycFloor_mem hβ hm0
    have hxle : x ≤ m := cycFloor_le hβ
    by_cases hxs : s ≤ x
    · have hxy : x ≤ y := hxle.trans (min_le_right _ _)
      have hxs1 : x ≤ s + 1 := hxle.trans (min_le_left _ _)
      have hyB' : latDist (w y) B < (n : ℝ) ^ 3 := hs_t y (by linarith [hCI.1]) hyt (by linarith)
      have hyB : latDist (w y) B ≤ 2 ^ k + (n : ℝ) ^ 41 := by
        have : (0 : ℝ) ≤ 2 ^ k := by positivity
        linarith
      have hyin : y ≤ min (x + tk) t := le_min (by linarith) hyt
      have key := nofast_b (n₀ := n₀) (E := E) hd hβ hT hw ht0 htf hgood hxCI hxy hyin hyB
      have h2pow : (2 : ℝ) ^ (k + 1) ≤ 2 ^ (k + 2) := by
        rw [pow_succ _ (k + 1)]; nlinarith [pow_pos (show (0 : ℝ) < 2 by norm_num) (k + 1)]
      have ha := nofast_a (n := n) hgood hxCI hxy hyin (key.trans h2pow)
      have hxd : latDist (w x) B ≤ latDist (w y) B + ‖w x - w y‖ := latDist_le_add hBne _ _
      rw [norm_sub_rev] at hxd
      have hl := norm_lt_of_close (n := n) hw hn1 htf hs0 hxs hxs1 (hxy.trans hyt)
      have hsd : latDist (w s) B ≤ latDist (w x) B + ‖w s - w x‖ := latDist_le_add hBne _ _
      rw [norm_sub_rev] at hsd
      linarith
    · push Not at hxs
      have hys : y < s + 1 := by
        by_contra hc
        push Not at hc
        have hmeq : m = s + 1 := min_eq_left hc
        have := lt_cycFloor_add_one (x := m) hβ
        rw [← hx, hmeq] at this
        linarith
      have h1' : latDist (w y) B < (n : ℝ) ^ 3 := hs_t y (by linarith [hCI.1]) hyt (by linarith)
      have hl := norm_lt_of_close (n := n) hw hn1 htf hs0 hsy (by linarith) (hyt.trans le_rfl)
      have hsd : latDist (w s) B ≤ latDist (w y) B + ‖w s - w y‖ := latDist_le_add hBne _ _
      rw [norm_sub_rev] at hsd
      linarith

end ElboimSly.Paper
