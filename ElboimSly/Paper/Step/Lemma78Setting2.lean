/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Heavy.TauHat
public import ElboimSly.Paper.Heavy.Lambda
public import ElboimSly.Paper.Step.Lemma78Setting

/-!
# Def 7.8 (setting), part 2: cross violations, `E_t`, `τ'_bad`, `ℋ_1`, `ℋ`

Setting of Lemma 7.8 (ES22 §7), bullets "Integer cyclic times",
"Cross violations" and the definitions of `Osc_1`, `ℋ_1`, `ℋ`.

All objects are functions of the two paths `W₁, W₂ : ℝ → ℤ^d` (the walks `W^N_{0,0}` and
`W^N_{u,q}`), the displacement `u`, the cyclic time `q`, the parameters `(d, β, t₀, n)` and the
horizon `T = t'_n`. The path `w₂ := W₂ - u` is the walk in the frame `N*`.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Step

open ElboimSly ElboimSly.Paper

variable {d : ℕ}

/-- `CI_N(q) = {b ≥ 0 : q + b ∈ CI_β}`. -/
def step78CIN (β q : ℝ) : Set ℝ := {b | 0 ≤ b ∧ q + b ∈ cycIntTimes β}

/-- The segments `W₁(a + ·)|_{[0,t'_k]}` and `W₂(b + ·)|_{[0,t'_k]}` merge (cyclic time of `W₂` is
`q + b + ·`). -/
def Step78CrossMerge (β tk q : ℝ) (W₁ W₂ : ℝ → Fin d → ℤ) (a b : ℝ) : Prop :=
  ∃ u₁ ∈ Icc (0 : ℝ) tk, ∃ u₂ ∈ Icc (0 : ℝ) tk, W₁ (a + u₁) = W₂ (b + u₂) ∧
    ∃ ℓ : ℤ, (a + u₁) - (q + b + u₂) = ℓ * β

/-- The cross proximity set `{u₂ ∈ [0,t'_k] : ∃ u₁ ∈ [0,t'_k], ‖W₁(a+u₁) - W₂(b+u₂)‖ ≤ r}`. -/
def step78CrossProx (tk r : ℝ) (W₁ W₂ : ℝ → Fin d → ℤ) (a b : ℝ) : Set ℝ :=
  {u₂ | u₂ ∈ Icc (0 : ℝ) tk ∧ ∃ u₁ ∈ Icc (0 : ℝ) tk, ‖W₁ (a + u₁) - W₂ (b + u₂)‖ ≤ r}

/-- The block `ι` of `ℬ_k` is *cross-bad by time `t`* (`t ∈ [0, T]`). -/
def Step78CrossBad (d : ℕ) (β t₀ : ℝ) (n : ℕ) (q T : ℝ) (W₁ W₂ : ℝ → Fin d → ℤ)
    (ι : Fin d → ℤ) (t : ℝ) : Prop :=
  let k := heavyLevel d n
  let tk := heavyTkPrime d t₀ n
  let B := heavyBlock k ι
  ∃ a ∈ cycIntTimes β, ∃ b ∈ step78CIN β q, a + tk ≤ T ∧ b + tk ≤ t ∧
    W₁ a ∈ latNbhd B (2 ^ (k + 2)) ∧ W₂ b ∈ latNbhd B (2 ^ (k + 2)) ∧
    ¬ SegClosed β tk W₁ a ∧ ¬ SegClosed β tk W₂ b ∧ ¬ Step78CrossMerge β tk q W₁ W₂ a b ∧
    ENNReal.ofReal ((3.9 : ℝ) ^ k) ≤ volume (step78CrossProx tk ((1.9 : ℝ) ^ k) W₁ W₂ a b)

/-- The set `ℬ'_t`: blocks bad by time `T` for `W₁` or cross-bad by time `t`. -/
def step78BadBlocks (d : ℕ) (β t₀ : ℝ) (n : ℕ) (q T : ℝ) (W₁ W₂ : ℝ → Fin d → ℤ) (t : ℝ) :
    Set (Fin d → ℤ) :=
  {ι | BadByTime d β t₀ n W₁ ι T ∨ Step78CrossBad d β t₀ n q T W₁ W₂ ι t}

/-- `b'_t = |ℬ'_t| + b_t(w₂)`. -/
noncomputable def step78BadCount (d : ℕ) (β t₀ : ℝ) (n : ℕ) (q T : ℝ) (u : Fin d → ℤ)
    (W₁ W₂ : ℝ → Fin d → ℤ) (t : ℝ) : ℕ :=
  (step78BadBlocks d β t₀ n q T W₁ W₂ t).ncard + badCount d β t₀ n (fun s => W₂ s - u) t

/-- `E_t = N(⋃ ℬ'_t, 2^{k+1}) ∪ (u + Λ_t(w₂))`; `N(⋃ ℬ'_t, r)` is written as the union of the
`N(B_ι, r)` (equal to the source's set for `ℬ'_t ≠ ∅`, and empty for `ℬ'_t = ∅`, as in the source,
whereas `latDist u ∅ = 0` would make the neighbourhood of `∅` everything). -/
def step78Exc (d : ℕ) (β t₀ : ℝ) (n : ℕ) (q T : ℝ) (u : Fin d → ℤ) (W₁ W₂ : ℝ → Fin d → ℤ)
    (t : ℝ) : Set (Fin d → ℤ) :=
  (⋃ ι ∈ step78BadBlocks d β t₀ n q T W₁ W₂ t,
      latNbhd (heavyBlock (heavyLevel d n) ι) (2 ^ (heavyLevel d n + 1))) ∪
    (fun x => u + x) '' badUnion d β t₀ n (fun s => W₂ s - u) t

/-- `τ'_bad` (as an extended real): `inf {t ≤ T : b'_t > 2n}` if `t_n^{5δ} > β`, and
`inf {t ≤ T : b'_t ≥ 1}` otherwise. -/
noncomputable def step78TauBad (d : ℕ) (β t₀ : ℝ) (n : ℕ) (q T : ℝ) (u : Fin d → ℤ)
    (W₁ W₂ : ℝ → Fin d → ℤ) : ℝ≥0∞ :=
  if β < indScale t₀ n ^ (5 * indDelta d) then
    ⨅ (t : ℝ) (_ : t ≤ T ∧ 2 * n < step78BadCount d β t₀ n q T u W₁ W₂ t), ENNReal.ofReal t
  else
    ⨅ (t : ℝ) (_ : t ≤ T ∧ 1 ≤ step78BadCount d β t₀ n q T u W₁ W₂ t), ENNReal.ofReal t

/-- `Osc_1`. -/
def Step78Osc (n : ℕ) (T : ℝ) (W₁ : ℝ → Fin d → ℤ) : Prop :=
  ∀ s ∈ Icc (0 : ℝ) T, ∀ s' ∈ Icc (0 : ℝ) T, |s - s'| ≤ (3.6 : ℝ) ^ n →
    ‖W₁ s - W₁ s'‖ ≤ (1.9 : ℝ) ^ n

/-- `ℋ_1 = {τ̂(W₁) > T} ∩ Osc_1`. -/
def Step78H1 (d : ℕ) (β t₀ : ℝ) (n : ℕ) (T : ℝ) (W₁ : ℝ → Fin d → ℤ) : Prop :=
  ENNReal.ofReal T < heavyTauHat d β t₀ n W₁ ∧ Step78Osc n T W₁

end ElboimSly.Paper.Step

end
