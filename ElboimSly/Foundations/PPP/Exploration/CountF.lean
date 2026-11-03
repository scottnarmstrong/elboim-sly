/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.PPP.Exploration.ThmInf
import Mathlib

/-!
# Count events of finite mass

Sequential first-point exploration, Step 5. The family `𝓒_f` of count events
`{ν | (ν(B₁), …, ν(B_l)) ∈ C}` with `μ(B_i) < ∞` is a `π`-system containing `𝓜(S)` that generates the
Giry `σ`-algebra.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal NNReal

namespace ElboimSly

variable {S : Type*} [MeasurableSpace S] (μ : Measure S) [SigmaFinite μ]

/-- Count events built from sets of finite `μ`-mass. -/
def countEventsFin : Set (Set (Measure S)) :=
  {F | ∃ (l : ℕ) (B : Fin l → Set S) (C : Set (Fin l → ℝ≥0∞)),
    (∀ i, MeasurableSet (B i)) ∧ (∀ i, μ (B i) < ∞) ∧ MeasurableSet C ∧
      F = {ν | (fun i => ν (B i)) ∈ C}}

variable {μ}

omit [SigmaFinite μ] in
theorem countEventsFin_subset : countEventsFin μ ⊆ countEvents S := by
  rintro _ ⟨l, B, C, hB, -, hC, rfl⟩
  exact ⟨l, B, C, hB, hC, rfl⟩

omit [SigmaFinite μ] in
theorem univ_mem_countEventsFin : (Set.univ : Set (Measure S)) ∈ countEventsFin μ :=
  ⟨1, fun _ => ∅, Set.univ, fun _ => MeasurableSet.empty, fun _ => by simp, MeasurableSet.univ,
    by simp⟩

omit [SigmaFinite μ] in
theorem isPiSystem_countEventsFin : IsPiSystem (countEventsFin μ) := by
  rintro _ ⟨l, B, C, hB, hf, hC, rfl⟩ _ ⟨l', B', C', hB', hf', hC', rfl⟩ -
  refine ⟨l + l', Fin.append B B', {x | (fun i => x (Fin.castAdd l' i)) ∈ C ∧
    (fun j => x (Fin.natAdd l j)) ∈ C'}, ?_, ?_, ?_, ?_⟩
  · intro i
    refine Fin.addCases (fun i => ?_) (fun j => ?_) i <;> simp [hB, hB']
  · intro i
    refine Fin.addCases (fun i => ?_) (fun j => ?_) i <;> simp [hf, hf']
  · exact (hC.preimage (Measurable.of_eval fun i => measurable_pi_apply _)).inter
      (hC'.preimage (Measurable.of_eval fun i => measurable_pi_apply _))
  · ext ν
    simp [Fin.append_left, Fin.append_right]

theorem generateFrom_countEventsFin :
    MeasurableSpace.generateFrom (countEventsFin μ) =
      (Measure.instMeasurableSpace : MeasurableSpace (Measure S)) := by
  apply le_antisymm
  · exact MeasurableSpace.generateFrom_le fun F hF =>
      countEvents_measurableSet (countEventsFin_subset hF)
  · refine iSup_le fun s => iSup_le fun hs => ?_
    rw [MeasurableSpace.comap_le_iff_le_map]
    intro C hC
    have hterm : ∀ k (C : Set ℝ≥0∞), MeasurableSet C →
        MeasurableSet[MeasurableSpace.generateFrom (countEventsFin μ)]
          ((fun ν : Measure S => ν (s ∩ ppartition μ k)) ⁻¹' C) := by
      intro k C hC
      refine MeasurableSpace.measurableSet_generateFrom ⟨1, fun _ => s ∩ ppartition μ k,
        {x | x 0 ∈ C}, fun _ => hs.inter (measurableSet_ppartition μ k), fun _ =>
          lt_of_le_of_lt (measure_mono Set.inter_subset_right) (measure_ppartition_lt_top μ k),
        (measurable_pi_apply 0) hC, ?_⟩
      ext ν; simp
    have hm : @Measurable _ _ (MeasurableSpace.generateFrom (countEventsFin μ)) _
        (fun ν : Measure S => ∑' k, ν (s ∩ ppartition μ k)) := by
      exact @Measurable.tsum (Measure S) ℝ≥0∞ ℕ (MeasurableSpace.generateFrom (countEventsFin μ))
        _ _ _ _ _ _ _ _ _ _ _ (fun k ν => ν (s ∩ ppartition μ k)) fun k C hC => hterm k C hC
    have e : (fun ν : Measure S => ν s) = fun ν => ∑' k, ν (s ∩ ppartition μ k) := by
      funext ν
      conv_lhs => rw [← Set.inter_univ s, ← iUnion_ppartition μ, Set.inter_iUnion]
      rw [measure_iUnion]
      · intro i j hij
        exact (pairwise_disjoint_ppartition μ hij).mono Set.inter_subset_right
          Set.inter_subset_right
      · exact fun k => hs.inter (measurableSet_ppartition μ k)
    rw [e]
    exact hm hC

end ElboimSly
