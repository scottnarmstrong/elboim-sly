/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Step.WeakEvents
public import ElboimSly.Paper.Step.StopAlpha
public import ElboimSly.Paper.Step.AvoidStopping
public import ElboimSly.Foundations.Cyclic.CPathCount
public import Mathlib

/-!
# The events of the regenerated walk are locally finite

Structure of relaxed times; stopping times (hypothesis "finitely many jumps in bounded intervals").

For a driving path `x`, `W = W_reg^x` and `α` (the last regeneration time) satisfy
`StepEventsFiniteW`: the events are the discontinuities of `W` and the regeneration times `σ_i`,
and there are finitely many of each in every bounded interval.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ElboimSly.Cyclic
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Step

open ElboimSly.Paper

variable {d : ℕ}

theorem drivenSigma_ge (b : ℝ≥0) (x : ℝ≥0 → Fin d → ℤ) (i : ℕ) :
    (i : ℝ≥0∞) * b ≤ drivenSigma b x i := by
  induction i with
  | zero => simp [drivenSigma_zero]
  | succ i ih =>
    rw [drivenSigma_succ, Nat.cast_succ, add_mul, one_mul]
    exact add_le_add ih (le_pathTreg b _)

theorem sigmaSet_finite {b : ℝ≥0} (hb : 0 < b) (x : ℝ≥0 → Fin d → ℤ) (M : ℝ≥0) :
    {r : ℝ≥0 | ∃ i, drivenSigma b x i = (r : ℝ≥0∞) ∧ r ≤ M}.Finite := by
  have hfin : (((Finset.range (⌈M / b⌉₊ + 1)).image
      fun i => (drivenSigma b x i).toNNReal : Finset ℝ≥0) : Set ℝ≥0).Finite :=
    Finset.finite_toSet _
  refine hfin.subset ?_
  rintro r ⟨i, hi, hrM⟩
  simp only [Finset.coe_image, Finset.coe_range, mem_image, mem_Iio]
  refine ⟨i, ?_, by rw [hi, ENNReal.toNNReal_coe]⟩
  have h1 : (i : ℝ≥0∞) * b ≤ r := hi ▸ drivenSigma_ge b x i
  have h2 : (i : ℝ≥0) * b ≤ r := by exact_mod_cast h1
  have h3 : (i : ℝ≥0) ≤ M / b := by
    rw [le_div_iff₀ hb]; exact h2.trans hrM
  have h4 : i ≤ ⌈M / b⌉₊ := Nat.cast_le.1 (h3.trans (Nat.le_ceil _))
  omega

theorem stepEventsFiniteW_stepReg {β : ℝ} [Fact (0 < β)] {x : ℝ≥0 → Fin d → ℤ}
    (hx : x ∈ StepPath d) :
    StepEventsFiniteW (stepExt fun s => stepReg β x s)
      (fun r => (stepAlpha β x r.toNNReal : ℝ)) := by
  classical
  have hb : 0 < β.toNNReal := toNNReal_pos'
  have hreg : IsRegPath (stepReg β x) := isRegPath_stepReg hx.toIsRegPath
  refine ⟨fun e he => ⟨NNReal.coe_nonneg _, ?_⟩, fun M => ?_⟩
  · have := stepAlpha_le (β := β) hx e.toNNReal
    calc (stepAlpha β x e.toNNReal : ℝ) ≤ (e.toNNReal : ℝ) := by exact_mod_cast this
      _ = e := Real.coe_toNNReal _ he
  set M' : ℝ≥0 := (max M 0 + 1).toNNReal with hM'
  have hM'r : (M' : ℝ) = max M 0 + 1 := Real.coe_toNNReal _ (by positivity)
  set Eset : Set ℝ≥0 := {0, M'} ∪ (CDisc (stepReg β x) ∩ Iic M') ∪
    {r : ℝ≥0 | ∃ i, drivenSigma β.toNNReal x i = (r : ℝ≥0∞) ∧ r ≤ M'} with hEset
  have hEfin : Eset.Finite :=
    (((Set.finite_singleton _).insert _).union (hreg.fin M')).union (sigmaSet_finite hb x M')
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
    have hWs : stepReg β x s.toNNReal = stepReg β x r :=
      eq_of_no_disc hreg.rc hrs (fun q hq hqd => by
        have hqM : q ≤ M' := hq.2.trans hsM'
        have hqE : q ∈ Eset := Or.inl (Or.inr ⟨hqd, hqM⟩)
        rcases hno' q hqE with h | h
        · exact absurd h (not_le.2 hq.1)
        · exact absurd hq.2 (not_le.2 h))
    have hAs : stepAlpha β x s.toNNReal = stepAlpha β x r := by
      set t := s.toNNReal with ht
      have hrt : (r : ℝ≥0∞) ≤ t := by exact_mod_cast hrs
      obtain ⟨hs1, hs2⟩ := gluedCount_spec' hb x t
      obtain ⟨he1, he2⟩ := gluedCount_spec' hb x r
      set Ns := gluedCount (drivenSigma β.toNNReal x) t
      set Ne := gluedCount (drivenSigma β.toNNReal x) r
      have hmono := drivenSigma_mono β.toNNReal x
      have hle : drivenSigma β.toNNReal x Ns ≤ r := by
        by_contra hlt
        rw [not_le] at hlt
        have hfin : drivenSigma β.toNNReal x Ns < ⊤ := lt_of_le_of_lt hs1 ENNReal.coe_lt_top
        have hcoe : drivenSigma β.toNNReal x Ns = ((drivenSigma β.toNNReal x Ns).toNNReal : ℝ≥0∞) :=
          (ENNReal.coe_toNNReal hfin.ne).symm
        set q := (drivenSigma β.toNNReal x Ns).toNNReal
        have hqt : q ≤ t := by rw [hcoe] at hs1; exact_mod_cast hs1
        have hqE : q ∈ Eset := Or.inr ⟨Ns, hcoe, hqt.trans hsM'⟩
        rcases hno' q hqE with h | h
        · rw [hcoe] at hlt; exact absurd (by exact_mod_cast h) (not_le.2 hlt)
        · exact absurd hqt (not_le.2 h)
      have h1 : Ns ≤ Ne := by
        by_contra hgt
        rw [not_le] at hgt
        exact absurd he2 (not_lt.2 ((hmono hgt).trans hle))
      have h2 : Ne ≤ Ns := by
        by_contra hgt
        rw [not_le] at hgt
        exact absurd hs2 (not_lt.2 ((hmono hgt).trans (he1.trans hrt)))
      have : Ns = Ne := le_antisymm h1 h2
      show (drivenSigma β.toNNReal x Ns).toNNReal = (drivenSigma β.toNNReal x Ne).toNNReal
      rw [this]
    refine ⟨?_, ?_⟩
    · simp only [stepExt, Real.toNNReal_coe]; exact hWs
    · show ((stepAlpha β x s.toNNReal : ℝ≥0) : ℝ) = ((stepAlpha β x (r : ℝ).toNNReal : ℝ≥0) : ℝ)
      rw [Real.toNNReal_coe, hAs]

end ElboimSly.Paper.Step
