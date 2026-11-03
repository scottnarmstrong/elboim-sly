/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Escape.Es55DetProofC
public import Mathlib

/-!
# `es55DetAll`: the geometry of the first and last entries on `H`

ES22 Lemma 5.5, Step 1.  On `H = 𝒦(β') ∩ 𝒜_i ∩ {exit}`:

* `entEnd e₀ = W(ξ_B) ∈ B⁻ ∩ ∂B` (`ent5_zero_bdry`);
* the backward walk `e_B` exits `𝒬` through `F_B` at its `a`-th jump, at a time `≤ 4^{j-1}`
  (`ent5_back_exit`);
* `t_* = t' - r_i - ξ_B ∈ [4^{j-1}, 4^j]`, from `t' ∈ (ξ_B + 4^j - 1, ξ_B + 4^j]`.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Escape

open ElboimSly ElboimSly.Cyclic ElboimSly.Cyclic.CycSchemeEnv ElboimSly.Paper

/-- **`es55DetAll`**: the geometry of the entries `0` and `I+1` of the record on `H`. -/
theorem es55DetAll (k : ℕ) : Es55DetAll k := by
  refine ⟨fun _ => 0, ?_⟩
  intro β _ n₀ n t₀ Ω 𝒢₀ mΩ Pr N N' hS _ u hadm β' i hi1 hiI ν hν
  have hn : 2 ≤ n := by
    have h1 := hS.params.eight_le
    have h2 := hS.params.lt
    have h3 := hS.params.five_le
    omega
  have hj : 1 ≤ escJ n := by have := escJ_ge_twenty hn; omega
  have hβ : 0 < β := Fact.out
  obtain ⟨⟨⟨hgood, hle, hlt, hBm, -⟩, -⟩, hX⟩ := hν
  obtain ⟨hbd, hbm⟩ := ent5_zero_bdry n (indScale t₀ n) u β' i (hlog_of_params hS.params) ν
    hadm hgood hle hlt hBm
  obtain ⟨a, hD, hjt⟩ := ent5_back_exit n (indScale t₀ n) u β' i (hlog_of_params hS.params) ν
    hgood hj hX
  refine ⟨a, hD, hbd, hbm, ?_⟩
  set e0 := ent5 n (indScale t₀ n) u β' i (hlog_of_params hS.params) ν 0 with he0
  set eB := ent5 n (indScale t₀ n) u β' i (hlog_of_params hS.params) ν
    (escIstar n (escJ n) + 1) with heB
  have hx : 0 ≤ e0.len.toReal := ENNReal.toReal_nonneg
  have hτ0 : 0 ≤ (eB.path.jt a).toReal := ENNReal.toReal_nonneg
  have hτ : (eB.path.jt a).toReal ≤ (4 : ℝ) ^ (escJ n - 1) :=
    ENNReal.toReal_le_of_le_ofReal (by positivity) hjt
  have hfl := cycFloor_le (β := β) (x := e0.len.toReal + 4 ^ escJ n) hβ
  have hfl2 := lt_cycFloor_add_one (β := β) (x := e0.len.toReal + 4 ^ escJ n) hβ
  have h4 : (4 : ℝ) ^ escJ n = 4 * 4 ^ (escJ n - 1) := by
    rw [← pow_succ']; congr 1; omega
  have h41 : (1 : ℝ) ≤ 4 ^ (escJ n - 1) := one_le_pow₀ (by norm_num)
  unfold d55T
  constructor <;> linarith

end ElboimSly.Paper.Escape
