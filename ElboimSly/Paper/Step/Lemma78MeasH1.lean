/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Step.Lemma78Adapt
public import ElboimSly.Paper.Heavy.TauHat
public import ElboimSly.Paper.Heavy.MeasPath
public import ElboimSly.Paper.Heavy.BadMeasMain
public import ElboimSly.Paper.Heavy.MeasFast
public import ElboimSly.Paper.Heavy.MeasJump2
public import ElboimSly.Paper.Heavy.MeasStop4
public import ElboimSly.Paper.Heavy.MeasStop5
public import ElboimSly.Paper.Heavy.PiecesPath
public import Mathlib

/-!
# Measurability of `ℋ₁` (Lemma 7.8), part 1: `{τ̂(W) > T}`

For a family of cyclic paths `W ω` whose values `W ω s`, `s ≤ T`, are `m`-measurable, the event
`{T < τ̂(W)}` is `m`-measurable (`measurableSet_tauHat_gt`): `τ̂` is a stopping time of the
canonical filtration of the cyclic-path space and `ω ↦ W ω` is measurable into its time-`T`
σ-algebra.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Step

open ElboimSly ElboimSly.Paper

variable {d : ℕ} {Ω : Type*}

/-- `ω ↦ W ω`, as a map into the cyclic-path space, is measurable for the time-`T` σ-algebra. -/
theorem measurable_cycPathSpace_mk {m : MeasurableSpace Ω} {W : Ω → ℝ → Fin d → ℤ}
    (hW : ∀ ω, IsCyclicPath (W ω)) {Tn : ℝ≥0}
    (hmeas : ∀ s : ℝ≥0, s ≤ Tn → Measurable[m] (fun ω => W ω (s : ℝ))) :
    Measurable[m, (cycPathFiltration d) Tn] (fun ω => (⟨W ω, hW ω⟩ : CycPathSpace d)) := by
  rw [measurable_iff_comap_le]
  show MeasurableSpace.comap _ (⨆ s : {s : ℝ≥0 // s ≤ Tn},
    MeasurableSpace.comap (fun p : CycPathSpace d => p.1 s) inferInstance) ≤ m
  rw [MeasurableSpace.comap_iSup]
  refine iSup_le fun s => ?_
  rw [MeasurableSpace.comap_comp]
  exact (hmeas s s.2).comap_le

/-- `τ̂` is a stopping time of the canonical filtration of the cyclic-path space. -/
theorem isStoppingTime_heavyTauHat_cycPath {β : ℝ} (t₀ : ℝ) {n : ℕ} (hβ : 0 < β)
    (htk : 0 ≤ heavyTkPrime d t₀ n) (hn : 1 ≤ n) :
    IsStoppingTime (cycPathFiltration d)
      (fun p : CycPathSpace d => (heavyTauHat d β t₀ n p.1 : WithTop ℝ≥0)) := by
  have hL : (0 : ℝ) < (n : ℝ) ^ 3 := by positivity
  have hA := adaptedCyclic_cycPathSpace (d := d)
  unfold heavyTauHat heavyTauCheck pathTfastCube pathTjumpCube
  exact (isStoppingTime_const _ (indScale t₀ n).toNNReal).min
    ((hA.isStoppingTime_cycClosingTime hβ).min ((hA.isStoppingTime_pathTfast hL).min
      ((hA.isStoppingTime_pathTjump hL).min ((hA.isStoppingTime_heavyTauPrime hn).min
        (hA.isStoppingTime_heavyTauBad hβ htk)))))

/-- `{T < τ̂(W)}` is `m`-measurable when `W ω s`, `s ≤ T`, is. -/
theorem measurableSet_tauHat_gt {m : MeasurableSpace Ω} {W : Ω → ℝ → Fin d → ℤ}
    (hW : ∀ ω, IsCyclicPath (W ω)) {Tn : ℝ≥0}
    (hmeas : ∀ s : ℝ≥0, s ≤ Tn → Measurable[m] (fun ω => W ω (s : ℝ)))
    {β : ℝ} (t₀ : ℝ) {n : ℕ} (hβ : 0 < β) (ht₀ : 0 < t₀) (hn : 1 ≤ n) :
    MeasurableSet[m] {ω | ENNReal.ofReal (Tn : ℝ) < heavyTauHat d β t₀ n (W ω)} := by
  have htk : 0 ≤ heavyTkPrime d t₀ n := by
    unfold heavyTkPrime indScale; positivity
  have hst := isStoppingTime_heavyTauHat_cycPath (d := d) (β := β) t₀ hβ htk hn Tn
  have hΦ := measurable_cycPathSpace_mk hW hmeas
  have hpre := hΦ hst.compl
  convert hpre using 1
  ext ω
  simp only [mem_ofPred_eq, mem_compl_iff, mem_preimage]
  rw [ENNReal.ofReal_coe_nnreal]
  exact (not_le (a := heavyTauHat d β t₀ n (W ω)) (b := (Tn : ℝ≥0∞))).symm

end ElboimSly.Paper.Step

end
