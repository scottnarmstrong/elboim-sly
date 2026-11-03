/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.SRW.EscapePath
public import ElboimSly.Foundations.SRW.KernelDef
public import Mathlib

/-!
# Probability of the escape event
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Real

namespace ElboimSly
namespace SRW

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {Y : Ω → PathSpace 1}

theorem IsSRW.prob_gam0 (hY : IsSRW P Y) :
    Real.exp (-2) / (72 : ℕ).factorial ≤ P.real {ω | Y ω ∈ gam0} := by
  obtain ⟨Ω', mΩ', P', N, hP, hN, -⟩ := exists_isPoissonPointProcess_clockIntensity (Dir 1)
  have hZ := canonical_isSRW hN
  have h := hY.prob_regSet_eq hZ (isRegSet_gamK 0)
  have := prob_gam0_canonical hN
  simp only [measureReal_def]
  have e : P {ω | Y ω ∈ gam0} = P' {ω | canonical 1 N ω ∈ gam0} := h
  rw [e]
  exact this

theorem IsSRW.prob_G (hY : IsSRW P Y) (n : ℕ) :
    Real.exp (-2) / (72 : ℕ).factorial * (1 / 1100) ^ n ≤
      P.real {ω | Y ω ∈ Gfrom win gamV 0 (n + 1)} := by
  have := hY.isProbabilityMeasure
  rw [hY.real_Gfrom (fun k => measurableSet_gamV k) (n + 1) 0]
  have hf : ∀ i, P.real {ω | stopPath (win (0 + i)) (Y ω) ∈ gamV (0 + i)} =
      P.real {ω | Y ω ∈ gamK i} := by
    intro i
    congr 1
    ext ω
    simp only [zero_add, mem_ofPred_eq]
    exact stop_mem_gamV_iff i (hY.2.1 ω)
  simp_rw [hf]
  rw [Finset.prod_range_succ']
  have h0 := hY.prob_gam0
  have h1 : ∀ i ∈ Finset.range n, (1 / 1100 : ℝ) ≤ P.real {ω | Y ω ∈ gamK (i + 1)} := by
    intro i _
    exact hY.prob_gamWin (rhoN_ge i)
  have h2 : (1 / 1100 : ℝ) ^ n ≤ ∏ i ∈ Finset.range n, P.real {ω | Y ω ∈ gamK (i + 1)} := by
    calc (1 / 1100 : ℝ) ^ n = ∏ _i ∈ Finset.range n, (1 / 1100 : ℝ) := by simp
      _ ≤ _ := by
        gcongr with i hi
        exact h1 i hi
  calc Real.exp (-2) / (72 : ℕ).factorial * (1 / 1100) ^ n
      = (1 / 1100) ^ n * (Real.exp (-2) / (72 : ℕ).factorial) := mul_comm _ _
    _ ≤ _ := mul_le_mul h2 h0 (by positivity)
        (Finset.prod_nonneg fun i _ => measureReal_nonneg)

end SRW
end ElboimSly
