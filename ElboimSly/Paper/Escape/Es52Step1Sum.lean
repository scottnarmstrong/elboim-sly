/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Escape.Es52Step1
public import Mathlib

/-!
# ES22 Proposition 5.2, Step 1: the sum over `β'`

ES22 Proposition 5.2 proof, Step 1, last sentence: summing over the `⌈β⌉ ≤ β + 1` values of `β'`
(t' and escK(β')),
`P(G_B ∩ {W(ξ_B) ∈ B⁻, π_B ≤ n^{-γ}}) ≤ 2 ⌈β⌉ (1 - c/2)^I`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Escape

open ElboimSly ElboimSly.Cyclic ElboimSly.Paper ElboimSly.Brownian

variable {k : ℕ} {β : ℝ} [Fact (0 < β)]

/-- The good environments with `ξ_B ≤ t_n`, `ξ_B < t_reg`, `W(ξ_B) ∈ B⁻` are covered by the
events `𝒦(β')`, `β' < ⌈β⌉`. -/
theorem exists_escKSet {n : ℕ} {tn : ℝ} {u : Fin (k + 2) → ℤ} {ν : Measure (CycS ℕ (k + 2) β)}
    (hν : CycGood ν) (h1 : escXi (escWalk ν) (escBlock (escJ n) u) ≤ ENNReal.ofReal tn)
    (h2 : escXi (escWalk ν) (escBlock (escJ n) u) < cycTreg (copyEnv ν 0))
    (h3 : escWalk ν (escXi (escWalk ν) (escBlock (escJ n) u)).toReal ∈ escBlockMinus (escJ n) u) :
    ∃ β' < ⌈β⌉₊, ν ∈ escKSet β tn n β' u := by
  have hβ : 0 < β := Fact.out
  set x := (escXi (escWalk ν) (escBlock (escJ n) u)).toReal + 4 ^ escJ n with hx
  have hx0 : 0 ≤ x := by positivity
  have hq0 : 0 ≤ cycIntPhase β x := by
    unfold cycIntPhase
    have := Int.floor_le (x / β)
    have h2 : β * (x / β) = x := by field_simp
    nlinarith
  refine ⟨⌊cycIntPhase β x⌋₊, ?_, ?_⟩
  · have hK : EscK β tn (escJ n) (escBlockMinus (escJ n) u) (escWalk ν)
        (escXi (escWalk ν) (escBlock (escJ n) u)) (cycTreg (copyEnv ν 0)) ⌊cycIntPhase β x⌋₊ := by
      refine ⟨h1, h2, h3, ?_⟩
      rw [cycIntPhase_cycFloor, ← Int.natCast_floor_eq_floor hq0]
      simp
    exact hK.phase_lt
  · refine ⟨hν, h1, h2, h3, ?_⟩
    rw [cycIntPhase_cycFloor, ← Int.natCast_floor_eq_floor hq0]
    simp

section main

variable {n₀ n : ℕ} {t₀ : ℝ} {Ω : Type} {𝒢₀ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
  {Pr : Measure Ω} {N N' : Ω → Measure (CycS ℕ (k + 2) β)}

/-- **Step 1 of ES22 Proposition 5.2**: the sum over `β'`. -/
theorem es52_step1_sum (hS : Es4Setting (k + 2) β n₀ n t₀ 𝒢₀ Pr N N') (hn : 2000 ≤ n)
    (hlb : Real.log β ≤ (n : ℝ) ^ 40) (u : Fin (k + 2) → ℤ) (hadm : EscAdmissible (escJ n) u)
    (H55 : ∀ β' i, 1 ≤ i → i ≤ escIstar n (escJ n) →
      ∀ᵐ ω ∂Pr, N ω ∈ escKSet β (indScale t₀ n) n β' u ∩
          escASet n u β' (hlog_of_params hS.params) i →
        2 * ENNReal.ofReal ((n : ℝ) ^ (-escGamma (k + 2))) ≤
          resPhi (plan5 n β (indScale t₀ n) u β' i (hlog_of_params hS.params)) Pr N
            (lamT (plan5 n β (indScale t₀ n) u β' i (hlog_of_params hS.params)) N
              (escIstar n (escJ n) + 1))
            (escConSet β n u i) ω)
    (h54 : ∀ β', 1 - (1 - ENNReal.ofReal (cline (k + 2) / 2)) ^ escIstar n (escJ n) ≤
          Pr {ω | ∃ ℓ, ℓ < escIstar n (escJ n) ∧
            (escEntry n u β' (hlog_of_params hS.params) (cycNgood N ω) ℓ).len =
              (4 : ℝ≥0∞) ^ n}) :
    Pr {ω | CycGood (N ω) ∧
        escXi (escWalk (N ω)) (escBlock (escJ n) u) ≤ ENNReal.ofReal (indScale t₀ n) ∧
        escXi (escWalk (N ω)) (escBlock (escJ n) u) < cycTreg (copyEnv (N ω) 0) ∧
        escWalk (N ω) (escXi (escWalk (N ω)) (escBlock (escJ n) u)).toReal ∈
          escBlockMinus (escJ n) u ∧
        escPiG Pr N n (indScale t₀ n) u ω ≤ ENNReal.ofReal ((n : ℝ) ^ (-escGamma (k + 2)))} ≤
      ⌈β⌉₊ * (2 * (1 - ENNReal.ofReal (cline (k + 2) / 2)) ^ escIstar n (escJ n)) := by
  calc _ ≤ Pr (⋃ β' ∈ Finset.range ⌈β⌉₊, {ω | N ω ∈ escKSet β (indScale t₀ n) n β' u ∧
        escPiG Pr N n (indScale t₀ n) u ω ≤ ENNReal.ofReal ((n : ℝ) ^ (-escGamma (k + 2)))}) := by
        refine measure_mono fun ω hω => ?_
        obtain ⟨hg, h1, h2, h3, h4⟩ := hω
        obtain ⟨β', hβ', hK⟩ := exists_escKSet hg h1 h2 h3
        simp only [mem_iUnion, Finset.mem_range, mem_ofPred_eq]
        exact ⟨β', hβ', hK, h4⟩
    _ ≤ ∑ β' ∈ Finset.range ⌈β⌉₊, Pr {ω | N ω ∈ escKSet β (indScale t₀ n) n β' u ∧
        escPiG Pr N n (indScale t₀ n) u ω ≤ ENNReal.ofReal ((n : ℝ) ^ (-escGamma (k + 2)))} :=
        measure_biUnion_finset_le _ _
    _ ≤ ∑ β' ∈ Finset.range ⌈β⌉₊,
        (2 * (1 - ENNReal.ofReal (cline (k + 2) / 2)) ^ escIstar n (escJ n)) :=
        Finset.sum_le_sum fun β' _ =>
          es52_step1_core hS hn hlb u hadm β' (H55 β') (h54 β')
    _ = _ := by simp

end main

end ElboimSly.Paper.Escape
