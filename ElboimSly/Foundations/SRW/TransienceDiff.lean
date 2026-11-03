/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.SRW.TransienceMain
public import ElboimSly.Foundations.SRW.Difference
public import Mathlib

/-!
# Transience for the difference of two independent SRWs

Transience: escape from the unit box, second statement.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Real

namespace ElboimSly
namespace SRW

variable {d : ℕ}

theorem diff_event_eq {Ω1 : Type*} [MeasurableSpace Ω1] {Q : Measure Ω1} {A B : Ω1 → PathSpace d}
    (hA : IsSRW Q A) (hB : IsSRW Q B) (x : Fin d → ℤ)
    {V : Set ((Fin d → ℤ) × PathSpace d)}
    (hV : ∀ z γ, IsRegularPath γ →
      ((∃ s : ℝ≥0, ‖fun i => ((z i + γ s i : ℤ) : ℝ)‖ < 2) ↔ (z, γ) ∈ V)) :
    Q {ω | ∀ s : ℝ≥0, 2 ≤ ‖fun i => ((x i + (A ω s i - B ω s i) : ℤ) : ℝ)‖} =
      Q {ω | (A ω, B ω) ∈ {p : PathSpace d × PathSpace d | (x, p.1 - p.2) ∉ V}} := by
  congr 1
  ext ω
  have hreg : IsRegularPath (A ω - B ω) := (hA.2.1 ω).sub (hB.2.1 ω)
  simp only [mem_ofPred_eq]
  rw [← hV x _ hreg]
  simp only [not_exists, not_lt]
  rfl

/-- Transience: escape from the unit box: the difference of two independent SRWs. -/
theorem escape_diff {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X X' : Ω → PathSpace d}
    (hX : IsSRW P X) (hX' : IsSRW P X') (hind : IndepFun X X' P) (hd : 3 ≤ d)
    {x : Fin d → ℤ} (hx : 2 ≤ ‖x‖) :
    Real.exp (-(2 * d)) / (2 * (escR d).factorial) ≤
      P.real {ω | ∀ s : ℝ≥0, 2 ≤ ‖fun i => ((x i + (X ω s i - X' ω s i) : ℤ) : ℝ)‖} := by
  classical
  have := hX.isProbabilityMeasure
  obtain ⟨Ω0, mΩ0, P0, Ñ, hP0, hÑ, -⟩ :=
    exists_isPoissonPointProcess_clockIntensity (Dir d × Bool)
  have := hP0
  set N := subProcess Ñ true with hN
  set N' := subProcess Ñ false with hN'
  have hNp := subProcess_ppp hÑ true
  have hNp' := subProcess_ppp hÑ false
  have hindN : IndepFun N N' P0 :=
    (iIndepFun_subProcess hÑ).indepFun (by simp)
  have hXo : IsSRW P0 (canonical d N) := canonical_isSRW hNp
  have hXo' : IsSRW P0 (canonical d N') := canonical_isSRW hNp'
  have hindC : IndepFun (canonical d N) (canonical d N') P0 :=
    (iIndepFun_canonical_subProcess hÑ).indepFun (by simp)
  have hK := difference_avoid hNp hNp' hindN x {z : Fin d → ℤ | ‖fun i => ((z i : ℤ) : ℝ)‖ < 2}
  have hbase := escape_unit hXo hd hx
  obtain ⟨V, hVm, hV⟩ := exists_version_bad (d := d)
  set W : Set (PathSpace d × PathSpace d) := {p | (x, p.1 - p.2) ∉ V} with hW
  have hsubm : Measurable fun p : PathSpace d × PathSpace d => (x, p.1 - p.2) := by
    refine measurable_const.prodMk ?_
    refine measurable_pi_iff.2 fun s => ?_
    exact ((measurable_pi_apply s).comp measurable_fst).sub
      ((measurable_pi_apply s).comp measurable_snd)
  have hWm : MeasurableSet W := (hsubm hVm).compl
  have hjoint : P.map (fun ω => (X ω, X' ω)) =
      P0.map (fun ω => (canonical d N ω, canonical d N' ω)) := by
    rw [(indepFun_iff_map_prod_eq_prod_map_map hX.1.aemeasurable hX'.1.aemeasurable).1 hind,
      (indepFun_iff_map_prod_eq_prod_map_map hXo.1.aemeasurable hXo'.1.aemeasurable).1 hindC,
      hX.map_eq_model, hX'.map_eq_model, hXo.map_eq_model, hXo'.map_eq_model]
  have e1 : P {ω | (X ω, X' ω) ∈ W} = P0 {ω | (canonical d N ω, canonical d N' ω) ∈ W} := by
    have m1 : Measurable fun ω => (X ω, X' ω) := hX.1.prodMk hX'.1
    have m2 : Measurable fun ω => (canonical d N ω, canonical d N' ω) := hXo.1.prodMk hXo'.1
    have := congrArg (fun μ => μ W) hjoint
    simp only [Measure.map_apply m1 hWm, Measure.map_apply m2 hWm] at this
    exact this
  have e2 := diff_event_eq hXo hXo' x hV
  have e3 := diff_event_eq hX hX' x hV
  have e4 : {ω | ∀ s, x + (canonical d N ω s - canonical d N' ω s) ∉
        {z : Fin d → ℤ | ‖fun i => ((z i : ℤ) : ℝ)‖ < 2}} =
      {ω | ∀ s : ℝ≥0, 2 ≤ ‖fun i => ((x i + (canonical d N ω s i - canonical d N' ω s i) : ℤ) : ℝ)‖} := by
    ext ω; simp [not_lt]
  have e5 : {ω | ∀ s, x + canonical d N ω s ∉
        {z : Fin d → ℤ | ‖fun i => ((z i : ℤ) : ℝ)‖ < 2}} =
      {ω | ∀ s : ℝ≥0, 2 ≤ ‖fun i => ((x i + canonical d N ω s i : ℤ) : ℝ)‖} := by
    ext ω; simp [not_lt]
  rw [e4, e5] at hK
  have : P {ω | ∀ s : ℝ≥0, 2 ≤ ‖fun i => ((x i + (X ω s i - X' ω s i) : ℤ) : ℝ)‖} =
      P0 {ω | ∀ s : ℝ≥0, 2 ≤ ‖fun i => ((x i + canonical d N ω s i : ℤ) : ℝ)‖} := by
    rw [e3, e1, ← e2, hK]
  rw [measureReal_def, this]
  exact hbase

end SRW
end ElboimSly
