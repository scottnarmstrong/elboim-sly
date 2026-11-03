/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Step.TravelLaw
public import ElboimSly.Paper.Step.TravelCat
public import ElboimSly.Paper.Step.TransAux
public import Mathlib

/-!
# The two-block natural coupling in Lemma 7.7

ES22 Lemma 7.7; Laws in the natural coupling. In the natural coupling with offset `0` and
lengths `(s₁, r)`, `W̃(s₁ + r) = W_1(s₁) + W_2(r)` with `W_1(s₁)` and `W_2(r)` independent, with the
laws of `W(s₁)` and `W(r)` (`map_stepWj_ppLaw`). `trans_key` is the estimate
`ℙ(W̃(t) = v) ≤ ℙ(‖W(r)‖ > ρ) + q ℙ(‖W(s₁) - v‖ ≤ ρ)` from `ℙ(W(r) = x) ≤ q`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology ElboimSly.Cyclic ElboimSly.SRW
open scoped NNReal ENNReal

namespace ElboimSly.Paper.Step

open ElboimSly.Paper

variable {d : ℕ} {β : ℝ} [Fact (0 < β)] {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {Y : Ω → PathSpace d} {Ωe : Type} [MeasurableSpace Ωe] {Pe : Measure Ωe}
  {N : Ωe → Measure (ℕ × RingSpace d β)}

/-- The law of the end value of the `j`-th stopped walk is that of the regenerated walk. -/
theorem measure_stepWj_end (hY : IsSRW P Y) (hYp : ∀ ω, Y ω ∈ StepPath d)
    (hN : IsPoissonPointProcess N ((Measure.count : Measure ℕ).prod (ringIntensity d β)) Pe)
    (a : ℝ≥0) (s : ℕ → ℝ≥0) (j : ℕ) (E : Set (Fin d → ℤ)) :
    P {ω | stepWj β a s (Y ω) j (s j) ∈ E} =
      Pe {ω | regenWalk (fun k => copyEnv (N ω) k) ((s j : ℝ≥0) : ℝ) ∈ E} := by
  have hEm : MeasurableSet {w : ℝ≥0 → Fin d → ℤ | w (s j) ∈ E} :=
    (measurable_pi_apply (s j)) (E.to_countable.measurableSet)
  have hW := measurable_stepWj (β := β) hY hYp a s j
  have h1 : P {ω | stepWj β a s (Y ω) j (s j) ∈ E} =
      (P.map fun ω => stepWj β a s (Y ω) j) {w | w (s j) ∈ E} := by
    rw [Measure.map_apply hW hEm]; rfl
  have hae := aemeasurable_ppPath hN
  have hae' : AEMeasurable (fun ω => SRW.stopPath (s j) (ppPath N ω)) Pe :=
    (SRW.measurable_stopPath _).comp_aemeasurable hae
  rw [h1, map_stepWj_ppLaw (β := β) hY hYp hN a s j, ppLaw_eq hN,
    Measure.map_apply_of_aemeasurable hae' hEm]
  congr 1
  ext ω
  simp [ppPath, SRW.stopPath]

/-- **`ℙ(W̃(t) = v)` in ES22 Lemma 7.7.** -/
theorem trans_key (hY : IsSRW P Y) (hYp : ∀ ω, Y ω ∈ StepPath d)
    (hN : IsPoissonPointProcess N ((Measure.count : Measure ℕ).prod (ringIntensity d β)) Pe)
    {s₁ r : ℝ≥0} (hr : 0 < r) {q : ℝ≥0∞}
    (hq : ∀ x : Fin d → ℤ, Pe {ω | regenWalk (fun k => copyEnv (N ω) k) (r : ℝ) = x} ≤ q)
    (v : Fin d → ℤ) (ρ : ℝ) :
    P {ω | stepNatTilde β 0 (fun j => if j = 0 then s₁ else r) 2 (Y ω) (s₁ + r) = v} ≤
      Pe {ω | ρ < ‖regenWalk (fun k => copyEnv (N ω) k) (r : ℝ)‖} +
        q * Pe {ω | ‖regenWalk (fun k => copyEnv (N ω) k) (s₁ : ℝ) - v‖ ≤ ρ} := by
  have := hY.isProbabilityMeasure
  set s : ℕ → ℝ≥0 := fun j => if j = 0 then s₁ else r with hs
  have hs0 : s 0 = s₁ := by simp [hs]
  have hs1' : s 1 = r := by simp [hs]
  set a : Ω → Fin d → ℤ := fun ω => stepWj β 0 s (Y ω) 0 (s 0) with ha
  set b : Ω → Fin d → ℤ := fun ω => stepWj β 0 s (Y ω) 1 (s 1) with hb
  have hsum : ∀ ω, stepNatTilde β 0 s 2 (Y ω) (s₁ + r) = a ω + b ω := by
    intro ω
    have hP : stepPartial s 1 = s₁ := by simp [stepPartial, hs0]
    have hlt : stepPartial s 1 < s₁ + r := by rw [hP]; exact lt_add_of_pos_right _ hr
    rw [stepNatTilde_apply β 0 s 2 (Y ω) 1 (s₁ + r) (by norm_num) (Or.inr hlt)
      (fun h => absurd h (by norm_num))]
    simp only [Finset.sum_range_one, hP, add_tsub_cancel_left, ha, hb, stepWj, min_self]
    rw [hs0, hs1']
  have hWm := measurable_stepWj (β := β) hY hYp 0 s
  have ham : Measurable a := (measurable_pi_apply (s 0)).comp (hWm 0)
  have hbm : Measurable b := (measurable_pi_apply (s 1)).comp (hWm 1)
  have hind : IndepFun a b P := by
    have h01 := (iIndepFun_stepWj (β := β) hY hYp 0 s).indepFun (i := 0) (j := 1) (by norm_num)
    exact h01.comp (measurable_pi_apply (s 0)) (measurable_pi_apply (s 1))
  have hend : ∀ (j : ℕ) (E : Set (Fin d → ℤ)),
      P {ω | stepWj β 0 s (Y ω) j (s j) ∈ E} =
        Pe {ω | regenWalk (fun k => copyEnv (N ω) k) ((s j : ℝ≥0) : ℝ) ∈ E} :=
    fun j E => measure_stepWj_end hY hYp hN 0 s j E
  have e1 : ∀ x, P {ω | b ω = x} ≤ q := fun x => by
    have := hend 1 {x}
    rw [hs1'] at this
    calc P {ω | b ω = x} = P {ω | stepWj β 0 s (Y ω) 1 (s 1) ∈ ({x} : Set (Fin d → ℤ))} := rfl
      _ = _ := this
      _ ≤ q := hq x
  have key := measure_add_eq_le ham hind e1 v ρ
  have e2 : P {ω | ρ < ‖b ω‖} = Pe {ω | ρ < ‖regenWalk (fun k => copyEnv (N ω) k) (r : ℝ)‖} := by
    have := hend 1 {x | ρ < ‖x‖}
    rw [hs1'] at this
    exact this
  have e3 : P {ω | ‖a ω - v‖ ≤ ρ} =
      Pe {ω | ‖regenWalk (fun k => copyEnv (N ω) k) (s₁ : ℝ) - v‖ ≤ ρ} := by
    have := hend 0 {x | ‖x - v‖ ≤ ρ}
    rw [hs0] at this
    exact this
  calc P {ω | stepNatTilde β 0 s 2 (Y ω) (s₁ + r) = v} = P {ω | a ω + b ω = v} := by
        congr 1; ext ω; show stepNatTilde β 0 s 2 (Y ω) (s₁ + r) = v ↔ a ω + b ω = v
        rw [hsum ω]
    _ ≤ _ := key
    _ = _ := by rw [e2, e3]

end ElboimSly.Paper.Step
