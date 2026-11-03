/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Avoid.CoreMain
public import Mathlib

/-!
# ES22 §4: Lemma 4.1, the pathwise step from `τ'` to `thit`

ES22 Lemma 4.1 (last paragraph of the proof): `{τ' ≥ 4ⁿ} ⊆ {thit(T) ≥ T + 4ⁿ}`.

By ES22 Lemma 2.1 (c), `thit(t)` is the infimum over `s > t` of the times at which the coupled
walk `W(t) + W̃(s - t)` comes within distance `1` of `W(s')` for some `s' ∈ (s + βℤ) ∩ (α, t)`.
With `r = s - t` this is the hitting time `τ'` of ES22 Lemma 4.1 shifted by `t`.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Paper

variable {d : ℕ}

/-- If `thit` is the shifted infimum of ES22 Lemma 2.1 (c) and `τ' ≥ n4`, then
`thit ≥ t + n4`. -/
theorem ofReal_add_le_of_hitTime {β : ℝ} {w : ℝ → Fin d → ℤ} {X : ℝ≥0 → Fin d → ℤ}
    {α t n4 : ℝ} {thit : ℝ≥0∞}
    (hit : ENNReal.ofReal n4 ≤ hitTime β w α t (fun r => w t + X r.toNNReal))
    (hth : thit = ⨅ s ∈ {s : ℝ | t < s ∧ ∃ s' : ℝ, (∃ kk : ℤ, s' = s + kk * β) ∧
        α < s' ∧ s' < t ∧ ‖w t + X (s - t).toNNReal - w s'‖ ≤ 1}, ENNReal.ofReal s) :
    ENNReal.ofReal (t + n4) ≤ thit := by
  rw [hth]
  refine le_iInf₂ fun s hs => ?_
  obtain ⟨hts, s', ⟨kk, hk⟩, h1, h2, h3⟩ := hs
  have hmem : s - t ∈ {r : ℝ | 0 < r ∧ ∃ s'' : ℝ, (∃ k : ℤ, s'' = t + r + k * β) ∧ α < s'' ∧
      s'' < t ∧ ‖(fun r => w t + X r.toNNReal) r - w s''‖ ≤ 1} :=
    ⟨sub_pos.2 hts, s', ⟨kk, by rw [hk]; ring⟩, h1, h2, h3⟩
  have h4 := hit.trans (iInf₂_le (s - t) hmem)
  have h5 : n4 ≤ s - t := (ENNReal.ofReal_le_ofReal_iff (sub_pos.2 hts).le).1 h4
  exact ENNReal.ofReal_le_ofReal (by linarith)

end ElboimSly.Paper

end
