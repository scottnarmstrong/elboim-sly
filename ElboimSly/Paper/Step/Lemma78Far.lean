/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Step.Lemma78FarNear
public import ElboimSly.Paper.Heavy.ThrFinite
public import ElboimSly.Paper.Heavy.Es6FourMain
public import ElboimSly.Paper.Heavy.Cor610Main
public import ElboimSly.Paper.Escape.Blocks

/-!
# Lemma 6.8 for `W₂` relative to `W₁`

ES22 Lemma 6.8 (ES22 §7), deterministic. Given the consequences of
`Ω ∩ ℋ_1 ∩ {τ̂(w₂) > T}` listed below, every `t ∈ [2 t'_k + 4, T]` with `W₂(t) ∉ E_t` has an
`s ∈ [t - t'_k, t]` that is a relaxed time of `w₂ = W₂ - u` and satisfies `d(W₂(s), V) ≥ ρ_k`,
where `V = W₁([0,T])`. The "`n` large" inequalities are explicit hypotheses.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace ElboimSly.Paper.Step

open ElboimSly ElboimSly.Paper

variable {d n₀ n : ℕ} {E : HeavyEscConsts} {β t₀ q T ρ : ℝ} {u : Fin d → ℤ}
  {W₁ W₂ : ℝ → Fin d → ℤ}

/-- ES22 Lemma 6.8. -/
theorem step78_far (hd : 5 ≤ d) (hn0 : 8 * d ≤ n₀) (ht1 : 1 < t₀) (ht4 : t₀ ≤ 4)
    (hβ : 0 < β) (hβt : β < indScale t₀ n) (hT : HeavyT d n₀ E n) (hq0 : 0 ≤ q) (hρ : 0 ≤ ρ)
    (hW₁ : IsCyclicPath W₁) (hw₂ : IsCyclicPath fun s => W₂ s - u)
    (hnr₂ : HasNoReturn β fun s => W₂ s - u)
    (hH₁ : ENNReal.ofReal T < heavyTauHat d β t₀ n W₁)
    (hH₂ : ENNReal.ofReal T < heavyTauHat d β t₀ n fun s => W₂ s - u)
    {t : ℝ} (ht : 2 * heavyTkPrime d t₀ n + 4 ≤ t) (htT : t ≤ T)
    (hTk : heavyTkPrime d t₀ n + 3 ≤ T)
    (hnE : W₂ t ∉ step78Exc d β t₀ n q T u W₁ W₂ t)
    (hcl₁ : ∀ a ∈ cycIntTimes β, a + heavyTkPrime d t₀ n ≤ T →
      ¬ SegClosed β (heavyTkPrime d t₀ n) W₁ a)
    (hcl₂ : ∀ b ∈ step78CIN β q, b + heavyTkPrime d t₀ n ≤ T →
      ¬ SegClosed β (heavyTkPrime d t₀ n) W₂ b)
    (hmg : ∀ a ∈ cycIntTimes β, ∀ b ∈ step78CIN β q, a + heavyTkPrime d t₀ n ≤ T →
      b + heavyTkPrime d t₀ n ≤ T →
      ¬ Step78CrossMerge β (heavyTkPrime d t₀ n) q W₁ W₂ a b)
    (hN₂ : (2 : ℝ) ^ (heavyLevel d n - 1) + 3 * (n : ℝ) ^ 3 + 1 + ρ ≤ 2 ^ heavyLevel d n)
    (hN₃ : ρ + (n : ℝ) ^ 41 ≤ (1.9 : ℝ) ^ heavyLevel d n)
    (hnum : 2 ^ d * heavyL d n * (3.9 : ℝ) ^ heavyLevel d n + 1 <
      (9 / 10 + 4 / (n : ℝ)) * heavyTkPrime d t₀ n) :
    ∃ s ∈ Icc (t - heavyTkPrime d t₀ n) t, s ∈ relaxedTimes β (fun s => W₂ s - u) ∧
      ∀ v ∈ W₁ '' Icc 0 T, ρ ≤ ‖W₂ s - v‖ := by
  classical
  obtain ⟨h2c, h2f, h2j, h2p, -⟩ := tauHat_lt_parts hH₂
  obtain ⟨-, h1f, -, h1p, -⟩ := tauHat_lt_parts hH₁
  have htT' : ENNReal.ofReal t ≤ ENNReal.ofReal T := ENNReal.ofReal_le_ofReal htT
  set w₂ : ℝ → Fin d → ℤ := fun s => W₂ s - u with hw₂def
  -- the block of `w₂ t`, good at time `t`
  set k := heavyLevel d n with hk
  set ι : Fin d → ℤ := heavyBlockIdx k (w₂ t) with hι
  have hwt : w₂ t ∈ heavyBlock k ι := mem_heavyBlock_idx k _
  have hgood : ¬ BadByTime d β t₀ n w₂ ι t := by
    intro hbad
    apply hnE
    right
    refine ⟨w₂ t, ?_, by simp [hw₂def]⟩
    simp only [badUnion, mem_iUnion]
    exact ⟨ι, hbad, hwt⟩
  have hnot : w₂ t ∉ badUnion d β t₀ n w₂ t := by
    intro h
    apply hnE
    right
    exact ⟨w₂ t, h, by simp [hw₂def]⟩
  -- relaxed times
  have hrel := es6_eight hd hn0 ht1 ht4 hβ hβt hT hw₂ hnr₂ ht (lt_of_le_of_lt htT' h2f)
    (lt_of_le_of_lt htT' h2j) (lt_of_le_of_lt htT' h2p) (lt_of_le_of_lt htT' h2c) hnot
  -- the near set
  have hnear := far_near_bound hd hn0 ht1 ht4 hβ hT hq0 hρ hW₁ hw₂ h1f h1p ht htT h2f hTk hnE
    hgood hwt hcl₁ hcl₂ hmg hN₂ hN₃
  by_contra hcon
  push Not at hcon
  have hsub : relaxedTimes β w₂ ∩ Icc (t - heavyTkPrime d t₀ n) t ⊆
      {s : ℝ | s ∈ Icc (t - heavyTkPrime d t₀ n) t ∧ ∃ v ∈ W₁ '' Icc 0 T, ‖W₂ s - v‖ < ρ} := by
    rintro s ⟨hs1, hs2⟩
    obtain ⟨v, hv, hlt⟩ := hcon s hs2 hs1
    exact ⟨hs2, v, hv, hlt⟩
  have h1 := hrel.trans (measure_mono hsub)
  have h2 := h1.trans hnear
  have hL0 : (0 : ℝ) ≤ heavyL d n := by unfold heavyL; positivity
  have h3 := (ENNReal.ofReal_le_ofReal_iff (by
    have : (0 : ℝ) ≤ 2 ^ d * heavyL d n * (3.9 : ℝ) ^ heavyLevel d n :=
      mul_nonneg (mul_nonneg (by positivity) hL0) (by positivity)
    linarith)).1 h2
  linarith

end ElboimSly.Paper.Step

end
