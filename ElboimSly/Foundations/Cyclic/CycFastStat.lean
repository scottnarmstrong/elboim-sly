/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycFastPath
public import ElboimSly.Foundations.Cyclic.CycStationary
public import ElboimSly.Foundations.Cyclic.CycSrwShortLaw
public import Mathlib

/-!
# ES22 Claim 2.3, Step 2: the probability of a unit-window deviation of one piece

ES22 Claim 2.3, Step 2. For a Poisson environment `N` on `ℕ × S_β`, a piece `j`, a
time `a ≥ 0`, `L ≥ 1` and `d ≥ 1`, the event that the shifted cyclic walk
`s ↦ Ŵ_j(a + s) - Ŵ_j(a)` has sup norm `≥ L/4` over `[0, 2]` (expressed at the check times of
`farSet`) has probability at most `e² e^{-L/(40d)}` (`window_prob`). Proof: stationarity
(`cyc_stationary`), the equality in law of the slices, and ES22 Lemma 2.2 with time `2` and
`L' = L/(80d)`, using that after `treg` the cyclic walk repeats itself.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

open ElboimSly.Interchange ElboimSly.SRW

variable {d : ℕ} {β : ℝ} [Fact (0 < β)]
  {Ω : Type*} [MeasurableSpace Ω] {Pe : Measure Ω}
  {N : Ω → Measure (ℕ × RingSpace d β)}

/-- The forward trajectory from `(0, 0)` as a path. -/
noncomputable def trajFn (ν : Measure (RingSpace d β)) : ℝ≥0 → Fin d → ℤ := fun s =>
  trajProc ν 0 0 s

theorem measurable_trajFn : Measurable (trajFn (d := d) (β := β)) :=
  measurable_trajProc 0 0

/-- The shifted trajectory `s ↦ Ŵ(a + s) - Ŵ(a)`. -/
noncomputable def shiftTraj (a : ℝ≥0) (ν : Measure (RingSpace d β)) : ℝ≥0 → Fin d → ℤ :=
  fun s => trajProc ν 0 0 (a + s) - trajProc ν 0 0 a

theorem measurable_shiftTraj (a : ℝ≥0) : Measurable (shiftTraj (d := d) (β := β) a) :=
  measurable_pi_iff.2 fun s =>
    ((measurable_pi_apply (a + s)).comp (measurable_trajProc 0 0)).sub
      ((measurable_pi_apply a).comp (measurable_trajProc 0 0))

variable (hN : IsPoissonPointProcess N ((Measure.count : Measure ℕ).prod (ringIntensity d β)) Pe)
include hN

/-- The slices have the same law, hence so do any measurable functionals of them. -/
theorem slice_prob_eq {F : Set (ℝ≥0 → Fin d → ℤ)} (hF : MeasurableSet F)
    {g : Measure (RingSpace d β) → ℝ≥0 → Fin d → ℤ} (hg : Measurable g) (j : ℕ) :
    Pe ((fun ω => g (cycSlice j (N ω))) ⁻¹' F) = Pe ((fun ω => g (cycSlice 0 (N ω))) ⁻¹' F) := by
  have h0 := isPoissonPointProcess_slice hN 0
  have hj := isPoissonPointProcess_slice hN j
  have hlaw : Pe.map (fun ω => cycSlice j (N ω)) = Pe.map (fun ω => cycSlice 0 (N ω)) :=
    h0.map_eq_map hj
  have e1 : ∀ k (h : IsPoissonPointProcess (fun ω => cycSlice k (N ω)) (ringIntensity d β) Pe),
      Pe ((fun ω => g (cycSlice k (N ω))) ⁻¹' F) =
        (Pe.map (fun ω => cycSlice k (N ω))) (g ⁻¹' F) := fun k h => by
    rw [Measure.map_apply h.measurable (hg hF)]; rfl
  rw [e1 j hj, e1 0 h0, hlaw]

/-- The window event for the first piece: probability at most `e² e^{-L/(40d)}`. -/
theorem slice_far_prob (hd : 1 ≤ d) {L : ℝ} (hL : 1 ≤ L) :
    Pe.real {ω | trajFn (cycSlice 0 (N ω)) ∈ farSet (d := d) (L / 4) 2} ≤
      Real.exp 2 * Real.exp (-(L / (40 * d))) := by
  have := hN.isProbabilityMeasure
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hdpos : (0 : ℝ) < d := by linarith
  by_cases hbig : L < 80 * d
  · refine (measureReal_le_one).trans ?_
    rw [← Real.exp_add]
    apply Real.one_le_exp
    have : L / (40 * d) ≤ 2 := by
      rw [div_le_iff₀ (by positivity)]; nlinarith
    linarith
  · rw [not_lt] at hbig
    set L' : ℝ := L / (80 * d) with hL'
    have hL'1 : 1 ≤ L' := by rw [hL', le_div_iff₀ (by positivity)]; linarith
    have hfar := cyc_far hd hN hL'1 (t := 2) (by norm_num)
    have hexp : -(L' * 2) = -(L / (40 * d)) := by rw [hL']; field_simp; ring
    have hR : 10 * (d : ℝ) * L' * 2 = L / 4 := by rw [hL']; field_simp; ring
    refine le_trans (measureReal_mono_ae' ?_) (hfar.trans ?_)
    · filter_upwards [ae_cycGood hN] with ω hω hmem
      obtain ⟨q, hq, hRq⟩ := mem_iUnion₂.1 hmem
      have hqle : q ≤ 2 := by
        rcases hq with rfl | ⟨h, -⟩
        · exact le_rfl
        · exact h
      have hgood : Good (cycSlice 0 (N ω)) := hω 0
      obtain ⟨u, huq, hutreg, hueq⟩ := exists_lt_treg_eq hgood q
      refine ⟨u, by exact_mod_cast huq.trans hqle, ?_⟩
      rw [hR, regenWalk_of_lt_treg (fun k => cycSlice k (N ω)) hutreg, hueq,
        cycWalk_eq_trajProc hgood]
      exact hRq
    · rw [hexp]
      calc Real.exp (-(L / (40 * d))) = 1 * Real.exp (-(L / (40 * d))) := (one_mul _).symm
        _ ≤ Real.exp 2 * Real.exp (-(L / (40 * d))) :=
          mul_le_mul_of_nonneg_right (Real.one_le_exp (by norm_num)) (Real.exp_pos _).le

/-- The shifted window event for piece `j` at time `a`. -/
theorem window_prob (hd : 1 ≤ d) {L : ℝ} (hL : 1 ≤ L) (j : ℕ) (a : ℝ≥0) :
    Pe.real {ω | shiftTraj a (cycSlice j (N ω)) ∈ farSet (d := d) (L / 4) 2} ≤
      Real.exp 2 * Real.exp (-(L / (40 * d))) := by
  have hF := measurableSet_farSet (d := d) (L / 4) 2
  have hj := isPoissonPointProcess_slice hN j
  have h1 : Pe ((fun ω => shiftTraj a (cycSlice j (N ω))) ⁻¹' farSet (d := d) (L / 4) 2) =
      Pe ((fun ω => trajFn (cycSlice j (N ω))) ⁻¹' farSet (d := d) (L / 4) 2) := by
    have hst : Pe.map (fun ω => shiftTraj a (cycSlice j (N ω))) =
        Pe.map (fun ω => trajFn (cycSlice j (N ω))) := cyc_stationary hj a
    have hm1 : Measurable fun ω => shiftTraj a (cycSlice j (N ω)) :=
      (measurable_shiftTraj a).comp hj.measurable
    have hm2 : Measurable fun ω => trajFn (cycSlice j (N ω)) :=
      measurable_trajFn.comp hj.measurable
    rw [← Measure.map_apply hm1 hF, ← Measure.map_apply hm2 hF, hst]
  have h2 := slice_prob_eq hN hF measurable_trajFn j
  have h3 : Pe.real {ω | shiftTraj a (cycSlice j (N ω)) ∈ farSet (d := d) (L / 4) 2} =
      Pe.real {ω | trajFn (cycSlice 0 (N ω)) ∈ farSet (d := d) (L / 4) 2} := by
    simp only [Measure.real]
    exact congrArg ENNReal.toReal (h1.trans h2)
  rw [h3]
  exact slice_far_prob hN hd hL

end ElboimSly.Cyclic

end
