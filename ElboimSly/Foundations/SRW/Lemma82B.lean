/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.SRW.Lemma82C
public import ElboimSly.Foundations.SRW.LatticeSumFin
public import Mathlib

/-!
# The SRW content of Lemma 8.2: part (b)

SRW content of Lemma 8.2 (b).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal Real

namespace ElboimSly
namespace SRW

variable {d : ℕ}

theorem IsRegSet.compl' {Γ : Set (PathSpace d)} (h : IsRegSet Γ) : IsRegSet Γᶜ := by
  obtain ⟨V, hVm, hV⟩ := h
  exact ⟨Vᶜ, hVm.compl, fun γ hγ => by simp only [mem_compl_iff, hV γ hγ]⟩

theorem isRegSet_exists_le (K : Set (Fin d → ℤ)) (T : ℝ≥0) :
    IsRegSet {β : PathSpace d | ∃ s : ℝ≥0, s ≤ T ∧ β s ∈ K} := by
  have h := (isRegSet_evalForall (d := d) Set.univ Kᶜ T).compl'
  obtain ⟨V, hVm, hV⟩ := h
  refine ⟨V, hVm, fun γ hγ => ?_⟩
  rw [← hV γ hγ]
  simp only [evalForall, mem_univ, true_and, mem_compl_iff, mem_ofPred_eq, not_forall, not_not]
  constructor
  · rintro ⟨s, hs, hK⟩; exact ⟨s, hs, hK⟩
  · rintro ⟨s, hs, hK⟩; exact ⟨s, hs, hK⟩

theorem latConst_nonneg {c : ℝ} (hc : 0 < c) (d : ℕ) : 0 ≤ latConst c d := by
  unfold latConst
  apply div_nonneg (by positivity)
  have : Real.exp (-c / 2) < 1 := (Real.exp_lt_one_iff.2 (by linarith))
  linarith

end SRW
end ElboimSly
