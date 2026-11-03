/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Heavy.NoFastMain
public import ElboimSly.Paper.Heavy.Eight1
public import ElboimSly.Paper.Heavy.ThrFinite
public import ElboimSly.Paper.Heavy.Es6FourMain
public import ElboimSly.Paper.Heavy.Cor610Main
public import ElboimSly.Paper.Escape.Blocks

/-!
# Lemma 7.8, far lemma: location of `w₂` (first step)

ES22 Lemma 6.8, "Location of `W₂`" (ES22 §7). For a path `w` that is good
at time `t` for the block `ι` containing `w t`, every `s ∈ [t*, t]`, `t* = max (CI ∩ [0, t - t'_k])`,
satisfies `d(w s, B) ≤ 2^{k-1} + 2 n³`.
-/

@[expose] public section

open Set
open scoped ENNReal

namespace ElboimSly.Paper.Step

open ElboimSly ElboimSly.Paper

variable {d n₀ n : ℕ} {E : HeavyEscConsts} {β t₀ : ℝ} {w : ℝ → Fin d → ℤ} {ι : Fin d → ℤ}

/-- ES22 Lemma 6.8, location of `W₂` (step 1). -/
theorem far_location (hd : 5 ≤ d) (hβ : 0 < β) (hT : HeavyT d n₀ E n) (hw : IsCyclicPath w)
    {t : ℝ} (htk : heavyTkPrime d t₀ n ≤ t) (htf : ENNReal.ofReal t < pathTfastCube w n)
    (hgood : ¬ BadByTime d β t₀ n w ι t) (hwt : w t ∈ heavyBlock (heavyLevel d n) ι)
    {s : ℝ} (hs1 : cycFloor β (t - heavyTkPrime d t₀ n) ≤ s) (hs2 : s ≤ t) :
    latDist (w s) (heavyBlock (heavyLevel d n) ι) ≤
      (2 : ℝ) ^ (heavyLevel d n - 1) + 2 * (n : ℝ) ^ 3 := by
  set k := heavyLevel d n with hk
  set tk := heavyTkPrime d t₀ n with htkdef
  set B := heavyBlock k ι with hB
  have hBne : B.Nonempty := heavyBlock_nonempty k ι
  have hn1 : 1 ≤ n := by have := hT.t4; omega
  have hn3 : (0 : ℝ) < (n : ℝ) ^ 3 := by positivity
  have hn41 : (n : ℝ) ^ 3 ≤ (n : ℝ) ^ 41 :=
    pow_le_pow_right₀ (by exact_mod_cast hn1) (by norm_num)
  have hcf0 : 0 ≤ t - tk := by linarith
  set ts := cycFloor β (t - tk) with hts
  have hts_mem : ts ∈ cycIntTimes β := cycFloor_mem hβ hcf0
  have hts_le : ts ≤ t - tk := cycFloor_le hβ
  have hts_lt : t - tk < ts + 1 := lt_cycFloor_add_one hβ
  have hts0 : 0 ≤ ts := hts_mem.1
  set y := ts + tk with hy
  have hy_le : y ≤ t := by linarith
  have hy_ge : t - 1 < y := by linarith
  have hs0 : 0 ≤ s := le_trans hts0 hs1
  -- the point `w t ∈ B`
  have hdist_t : ∀ r : ℝ, 0 ≤ r → r ≤ t → t ≤ r + 1 → latDist (w r) B < (n : ℝ) ^ 3 := by
    intro r hr0 hrt hr1
    have := norm_lt_of_close (n := n) hw (t := t) hn1 htf hr0 hrt hr1 le_rfl
    exact lt_of_le_of_lt (latDist_le_norm_of_mem hwt (w r) |>.trans_eq (norm_sub_rev _ _)) this
  by_cases hsy : y < s
  · have := hdist_t s hs0 hs2 (by linarith)
    have h2k : (0 : ℝ) ≤ (2 : ℝ) ^ (k - 1) := by positivity
    linarith
  · push Not at hsy
    set x := cycFloor β s with hx
    have hx_mem : x ∈ cycIntTimes β := cycFloor_mem hβ hs0
    have hx_le : x ≤ s := cycFloor_le hβ
    have hx_lt : s < x + 1 := lt_cycFloor_add_one hβ
    have htsx : ts ≤ x := le_cycFloor_of_mem hβ hs0 hts_mem hs1
    have hxy : x ≤ y := hx_le.trans hsy
    have hy2 : y ≤ min (x + tk) t := le_min (by linarith) hy_le
    have hyB : latDist (w y) B ≤ 2 ^ k + (n : ℝ) ^ 41 := by
      have := hdist_t y (by linarith) hy_le (by linarith)
      have h2k : (0 : ℝ) ≤ (2 : ℝ) ^ k := by positivity
      linarith
    have hxB : latDist (w x) B ≤ 2 ^ (k + 1) :=
      nofast_b hd hβ hT hw (by linarith) htf hgood hx_mem hxy hy2 hyB
    have hxB' : latDist (w x) B ≤ 2 ^ (k + 2) := by
      refine hxB.trans ?_
      exact pow_le_pow_right₀ (by norm_num) (by omega)
    have ha := nofast_a (t₀ := t₀) hgood hx_mem hxy hy2 hxB'
    have h1 : latDist (w x) B ≤ latDist (w y) B + ‖w x - w y‖ := latDist_le_add hBne _ _
    have h2 : ‖w x - w y‖ ≤ (2 : ℝ) ^ (k - 1) := by rw [norm_sub_rev]; exact ha
    have h3 : latDist (w y) B < (n : ℝ) ^ 3 := hdist_t y (by linarith) hy_le (by linarith)
    have h4 : latDist (w s) B ≤ latDist (w x) B + ‖w s - w x‖ := latDist_le_add hBne _ _
    have h5 : ‖w s - w x‖ < (n : ℝ) ^ 3 :=
      norm_lt_of_close hw hn1 htf hx_mem.1 hx_le (by linarith) hs2
    linarith

end ElboimSly.Paper.Step

end
