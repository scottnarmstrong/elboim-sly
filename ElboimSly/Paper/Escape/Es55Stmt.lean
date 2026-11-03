/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Escape.Es54
public import ElboimSly.Paper.Escape.InclusionRestart
public import ElboimSly.Paper.Escape.ResampleTower
public import ElboimSly.Paper.Escape.LamStopping
public import ElboimSly.Paper.Escape.Plan5Fin
public import ElboimSly.Paper.Escape.EscapeTime
public import Mathlib

/-!
# The statement of ES22 Lemma 5.5, in the form consumed by ES22 Proposition 5.2

t' and escK(β'); 𝒜_i, 𝒜, 𝒢(β'); The connecting plan; ES22 Lemma 5.5.

All events are sets of environments `ν : Measure (CycS ℕ (k+2) β)`; the event for the random
environment `N` is `{N ∈ X}`:

* `escKSet`: `𝒦(β')` (t' and escK(β')), for the regenerated walk `escWalk ν` and the closing time
  `treg` of its first piece, together with `CycGood ν` (which holds almost surely);
* `escASet`: `𝒜_i = {τ_i = 4^n}`, the length of entry `i - 1` of the final record of `𝒫_𝒜`;
* `escConSet`: `Con_i = {t' < treg, W(t') = p_i}`, `t'` the largest cyclic integer `≤ ξ_B + 4^j`
  (together with `CycGood ν`, which holds almost surely; this makes the set measurable).

`Es55Concl k` is the conclusion of ES22 Lemma 5.5: for the connecting plan `𝒫₅(B, β', i)` and the
stopping time `S₂ = Λ_{I+1}`, the canonical version `Φ_{Con_i}(cycRec^{𝒫₅}(S₂))` of
`P(Con_i | ℱ^{(i)}_{S₂})` is at least `2 n^{-γ}` almost surely on `𝒦(β') ∩ 𝒜_i`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace ElboimSly.Paper.Escape

open ElboimSly ElboimSly.Cyclic ElboimSly.Paper

variable {k : ℕ} {β : ℝ} [Fact (0 < β)]

/-- t' and escK(β'): the event `𝒦(β')` as a set of environments. -/
def escKSet (β tn : ℝ) (n β' : ℕ) (u : Fin (k + 2) → ℤ) : Set (Measure (CycS ℕ (k + 2) β)) :=
  {ν | CycGood ν ∧
    EscK β tn (escJ n) (escBlockMinus (escJ n) u) (escWalk ν)
      (escXi (escWalk ν) (escBlock (escJ n) u)) (cycTreg (copyEnv ν 0)) β'}

/-- 𝒜_i, 𝒜, 𝒢(β'): `𝒜_i = {τ_i = 4^n}` (`1 ≤ i`; walk `i` is entry `i - 1` of `𝒫_𝒜`). -/
def escASet (n : ℕ) (u : Fin (k + 2) → ℤ) (β' : ℕ) (hlog : 1 < Real.log β) (i : ℕ) :
    Set (Measure (CycS ℕ (k + 2) β)) :=
  {ν | CycGood ν ∧ (escEntry n u β' hlog ν (i - 1)).len = (4 : ℝ≥0∞) ^ n}

/-- 𝒜_i, 𝒜, 𝒢(β'): `𝒜(β') = ⋃_{i ≤ I} 𝒜_i`. -/
def escAUnion (n : ℕ) (u : Fin (k + 2) → ℤ) (β' : ℕ) (hlog : 1 < Real.log β) :
    Set (Measure (CycS ℕ (k + 2) β)) :=
  {ν | CycGood ν ∧ ∃ ℓ, ℓ < escIstar n (escJ n) ∧
    (escEntry n u β' hlog ν ℓ).len = (4 : ℝ≥0∞) ^ n}

/-- ES22 Lemma 5.5: `Con_i = {t' < treg, W(t') = p_i}`, with `t'` the largest cyclic
integer `≤ ξ_B + 4^j`. -/
def escConSet (β : ℝ) [Fact (0 < β)] (n : ℕ) (u : Fin (k + 2) → ℤ) (i : ℕ) :
    Set (Measure (CycS ℕ (k + 2) β)) :=
  {ν | CycGood ν ∧ escXi (escWalk ν) (escBlock (escJ n) u) ≠ ⊤ ∧
    ENNReal.ofReal (cycFloor β ((escXi (escWalk ν) (escBlock (escJ n) u)).toReal +
      4 ^ escJ n)) < cycTreg (copyEnv ν 0) ∧
    escWalk ν (cycFloor β ((escXi (escWalk ν) (escBlock (escJ n) u)).toReal + 4 ^ escJ n)) =
      escPoint n (escJ n) u i}

/-- **The conclusion of ES22 Lemma 5.5**, as consumed by ES22 Proposition 5.2 Step 1.  There is
`β₅₅ = β₅₅(d, n₀)` such that, under (S1)-(S2) with `β ≥ β₅₅`, for every admissible block `B`
(corner `u`), every `β'` and `1 ≤ i ≤ I`: almost surely on `𝒦(β') ∩ 𝒜_i`,
`Φ_{Con_i}(cycRec^{𝒫₅(B, β', i)}(S₂)) ≥ 2 n^{-γ}`, where `S₂ = Λ_{I+1}`. -/
def Es55Concl (k : ℕ) : Prop :=
  ∃ β55 : ℕ → ℝ, ∀ {β : ℝ} [Fact (0 < β)] {n₀ n : ℕ} {t₀ : ℝ} {Ω : Type}
    {𝒢₀ : MeasurableSpace Ω} [MeasurableSpace Ω] {Pr : Measure Ω}
    {N N' : Ω → Measure (CycS ℕ (k + 2) β)}
    (hS : Es4Setting (k + 2) β n₀ n t₀ 𝒢₀ Pr N N'), β55 n₀ ≤ β →
    ∀ (u : Fin (k + 2) → ℤ), EscAdmissible (escJ n) u → ∀ (β' i : ℕ), 1 ≤ i →
      i ≤ escIstar n (escJ n) →
      ∀ᵐ ω ∂Pr, N ω ∈ escKSet β (indScale t₀ n) n β' u ∩
          escASet n u β' (hlog_of_params hS.params) i →
        2 * ENNReal.ofReal ((n : ℝ) ^ (-escGamma (k + 2))) ≤
          resPhi (plan5 n β (indScale t₀ n) u β' i (hlog_of_params hS.params)) Pr N
            (lamT (plan5 n β (indScale t₀ n) u β' i (hlog_of_params hS.params)) N
              (escIstar n (escJ n) + 1))
            (escConSet β n u i) ω

end ElboimSly.Paper.Escape
