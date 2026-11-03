/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Step.Lemma78CoupleRegion
public import ElboimSly.Paper.Step.Lemma78Stop
public import ElboimSly.Foundations.Cyclic.CPathCount
public import Mathlib

/-!
# Regularity of the second walk of Lemma 7.8

Measurability (hypotheses of structure of relaxed times; stopping times): the cyclic walk
`W^N_{u,q}` is right-continuous with finitely many jumps in bounded intervals, so its events
(with `α ≡ 0`) are locally finite.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Step

open ElboimSly ElboimSly.Cyclic ElboimSly.Paper

set_option linter.unusedSectionVars false

variable {d : ℕ}

/-- A regular path (right-continuous, finitely many jumps in bounded intervals) has locally
finite events, with `α ≡ 0`. -/
theorem stepEventsFiniteW_of_isRegPath {f : ℝ≥0 → Fin d → ℤ} (hf : IsRegPath f) :
    StepEventsFiniteW (stepExt f) (fun _ => ((0 : ℝ≥0) : ℝ)) := by
  classical
  refine ⟨fun e he => ⟨le_rfl, by simpa using he⟩, fun M => ?_⟩
  set M' : ℝ≥0 := (max M 0 + 1).toNNReal with hM'
  have hM'r : (M' : ℝ) = max M 0 + 1 := Real.coe_toNNReal _ (by positivity)
  set Eset : Set ℝ≥0 := {0, M'} ∪ (CDisc f ∩ Iic M') with hEset
  have hEfin : Eset.Finite := ((Set.finite_singleton _).insert _).union (hf.fin M')
  refine ⟨hEfin.toFinset.image (fun r : ℝ≥0 => (r : ℝ)), ?_, ?_, ?_, ?_⟩
  · simp [hEset]
  · intro y hy
    simp only [Finset.mem_image] at hy
    obtain ⟨r, -, rfl⟩ := hy
    exact r.2
  · refine ⟨(M' : ℝ), ?_, by rw [hM'r]; linarith [le_max_left M 0]⟩
    simp [hEset]
  · intro e he s hes hsM hno
    simp only [Finset.mem_image, Set.Finite.mem_toFinset] at he hno
    obtain ⟨r, hr, rfl⟩ := he
    have hs0 : 0 ≤ s := (NNReal.coe_nonneg r).trans hes
    have hsM' : s.toNNReal ≤ M' := by
      rw [hM']
      exact Real.toNNReal_le_toNNReal (by linarith [le_max_left M 0])
    have hrs : r ≤ s.toNNReal := by
      rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hs0]; exact hes
    have hno' : ∀ q ∈ Eset, q ≤ r ∨ s.toNNReal < q := by
      intro q hq
      have := hno q ⟨q, hq, rfl⟩
      rcases this with h | h
      · exact Or.inl (by exact_mod_cast h)
      · exact Or.inr (by rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hs0]; exact h)
    have hWs : f s.toNNReal = f r := by
      refine eq_of_no_disc hf.rc hrs (fun q hq hqd => ?_)
      have hqE : q ∈ Eset := Or.inr ⟨hqd, hq.2.trans hsM'⟩
      rcases hno' q hqE with h | h
      · exact absurd h (not_le.2 hq.1)
      · exact absurd hq.2 (not_le.2 h)
    exact ⟨by simp only [stepExt, Real.toNNReal_coe]; exact hWs, rfl⟩

variable {β : ℝ} [Fact (0 < β)]

/-- The cyclic walk `W^ν_{u,q}` of a good configuration is a regular path. -/
theorem step78_isRegPath_cycWalk {ν : Measure (Unit × RingSpace d β)} (hν : CycGood ν)
    (u : Fin d → ℤ) (q : ℝ) (Tn : ℝ≥0) :
    IsRegPath (fun s : ℝ≥0 => cycWalk (cycSlice () ν) u q (s : ℝ)) := by
  have h := ((step78Plan d β u q Tn).E (step78Rule u q Tn ν) 1).path.isRegPath
  have e : (fun s : ℝ≥0 => cycWalk (cycSlice () ν) u q (s : ℝ)) =
      ((step78Plan d β u q Tn).E (step78Rule u q Tn ν) 1).path.fn := by
    funext s
    exact (step78_E_one_path_fn u q Tn hν s).symm
  rw [e]
  exact h

end ElboimSly.Paper.Step

end
