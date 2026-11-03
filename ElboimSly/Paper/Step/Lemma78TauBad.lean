/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Step.Lemma78Setting2

/-!
# `τ'_bad > T` from the block counts

Discovered bad blocks for two walks, "Counting" (ES22 §7): if the blocks counted in `b'_t`
(`t ≤ T`) lie in sets `S₁, S₂ ⊆ ℬ*` of bad blocks of `N` and `N*`, which have at most `n` elements
each (if `t_n^{5δ} > β`) or are empty (otherwise), then `b'_t ≤ 2n` (resp. `0`) for all `t ≤ T`,
so `τ'_bad > T`.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace ElboimSly.Paper.Step

open ElboimSly ElboimSly.Paper

variable {d : ℕ}

/-- Discovered bad blocks for two walks, deterministic part. -/
theorem step78_tauBad_gt {β t₀ q T : ℝ} {n : ℕ} {u : Fin d → ℤ} {W₁ W₂ : ℝ → Fin d → ℤ}
    {S₁ S₂ : Set (Fin d → ℤ)} (hf₁ : S₁.Finite) (hf₂ : S₂.Finite) (_hT : 0 ≤ T)
    (h₁ : ∀ t ≤ T, step78BadBlocks d β t₀ n q T W₁ W₂ t ⊆ S₁)
    (h₂ : ∀ t ≤ T, {ι | BadByTime d β t₀ n (fun s => W₂ s - u) ι t} ⊆ S₂)
    (hc₁ : β < indScale t₀ n ^ (5 * indDelta d) → S₁.ncard ≤ n ∧ S₂.ncard ≤ n)
    (hc₂ : ¬ β < indScale t₀ n ^ (5 * indDelta d) → S₁ = ∅ ∧ S₂ = ∅) :
    ENNReal.ofReal T < step78TauBad d β t₀ n q T u W₁ W₂ := by
  have hcount : ∀ t ≤ T, step78BadCount d β t₀ n q T u W₁ W₂ t ≤ S₁.ncard + S₂.ncard := by
    intro t ht
    unfold step78BadCount badCount
    exact add_le_add (Set.ncard_le_ncard (h₁ t ht) hf₁) (Set.ncard_le_ncard (h₂ t ht) hf₂)
  unfold step78TauBad
  split_ifs with hreg
  · obtain ⟨a, b⟩ := hc₁ hreg
    have : (⨅ (t : ℝ) (_ : t ≤ T ∧ 2 * n < step78BadCount d β t₀ n q T u W₁ W₂ t),
        ENNReal.ofReal t) = ⊤ := by
      simp only [iInf_eq_top]
      intro t ht
      have := hcount t ht.1
      omega
    rw [this]; exact ENNReal.ofReal_lt_top
  · obtain ⟨a, b⟩ := hc₂ hreg
    have hz : S₁.ncard = 0 := by rw [a]; simp
    have hz2 : S₂.ncard = 0 := by rw [b]; simp
    have : (⨅ (t : ℝ) (_ : t ≤ T ∧ 1 ≤ step78BadCount d β t₀ n q T u W₁ W₂ t),
        ENNReal.ofReal t) = ⊤ := by
      simp only [iInf_eq_top]
      intro t ht
      have := hcount t ht.1
      omega
    rw [this]; exact ENNReal.ofReal_lt_top

end ElboimSly.Paper.Step

end
