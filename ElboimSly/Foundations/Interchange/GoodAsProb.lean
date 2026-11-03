/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Interchange.GoodAsMecke
public import ElboimSly.Foundations.Interchange.GoodAsCount
public import ElboimSly.Foundations.Interchange.RingPathN
public import ElboimSly.Foundations.PPP.Mecke
public import ElboimSly.Frozen.Defs.IsPoissonPointProcess
public import Mathlib

/-!
# The Mecke bound for ring paths

Configurations are a.s. good (proof of (G3)), factorial moment measures.

For a Poisson point process `N` with intensity `μ_β`, the probability that a ring path of length `n`
in the window `I_j` starts at `y` is at most `K ^ n * Leb^n{t₁ < ⋯ < tₙ ∈ I_j}`, where `K = 2d`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace ElboimSly.Interchange

variable {d : ℕ} {β : ℝ} [Fact (0 < β)] {Ω : Type*} [MeasurableSpace Ω]
  {N : Ω → Measure (RingSpace d β)} {P : Measure Ω}

theorem measure_exists_ringPath_le (h : IsPoissonPointProcess N (ringIntensity d β) P)
    (y : Fin d → ℤ) {a p q : ℝ} (ha : a < p) (hq : q ≤ a + β) (n : ℕ) :
    P {ω | ¬ NoPathFrom (N ω) (Set.Icc p q) y n} ≤
      (stepCount d : ℝ≥0∞) ^ n * volume (orderedSimplex n p q) := by
  classical
  obtain ⟨F, hcard, hF⟩ := exists_finset_paths (d := d) y n
  have hD := ringSeq_isDissecting (Edge d) β
  have hdiff : ∀ x, ringIntensity d β {x} = 0 := ring_singleton (Edge d) β
  have hsub : {ω | ¬ NoPathFrom (N ω) (Set.Icc p q) y n} ⊆ ⋃ v ∈ F,
      ({ω | N ω ∉ (ringSeq (Edge d) β).bSimple} ∪
        {ω | 1 ≤ meckePhi (ringSeq (Edge d) β) n (N ω) (pathBox β v a p q)}) := by
    intro ω hω
    rw [Set.mem_ofPred_eq, noPathFrom_iff, not_not] at hω
    obtain ⟨v, t, hv0, hp⟩ := hω
    have hvF : v ∈ F := hF v hv0 fun i => by
      obtain ⟨e, he, -⟩ := hp.2.2 i
      exact latticeAdj_of_edge he
    simp only [Set.mem_iUnion, Set.mem_union, Set.mem_ofPred_eq]
    refine ⟨v, hvF, ?_⟩
    by_cases hs : N ω ∈ (ringSeq (Edge d) β).bSimple
    · exact Or.inr (one_le_meckePhi_pathBox hs ha hq hp)
    · exact Or.inl hs
  refine (measure_mono hsub).trans ((measure_biUnion_finset_le F _).trans ?_)
  calc ∑ v ∈ F, _ ≤ ∑ v ∈ F, volume (orderedSimplex n p q) := by
        refine Finset.sum_le_sum fun v _ => ?_
        exact (h.measure_not_simple_or_distinct_atoms_le _ hD hdiff n
          (measurableSet_pathBox v a p q)).trans (pi_ringIntensity_pathBox_le v a p q)
    _ = F.card * volume (orderedSimplex n p q) := by simp
    _ ≤ (stepCount d : ℝ≥0∞) ^ n * volume (orderedSimplex n p q) := by
        gcongr
        exact_mod_cast hcard

end ElboimSly.Interchange
