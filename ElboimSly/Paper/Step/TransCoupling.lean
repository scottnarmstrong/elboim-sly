/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Step.Lemma76Stmt
public import ElboimSly.Paper.Step.RegenMeas
public import ElboimSly.Paper.Step.WalkPathAux
public import ElboimSly.Paper.Bridge.WienerBridge
public import ElboimSly.Foundations.Brownian.Density
public import Mathlib

/-!
# The Brownian ball bound in Lemma 7.7

ES22 Lemma 7.7; Density bounds (c). If the regenerated walk admits a
`(σ, ε)`-coupling up to time `T` with failure probability `η`, then for `0 < s ≤ T`, a lattice point
`v` and `ρ ≥ 0`,
`ℙ(‖W(s) - v‖ ≤ ρ) ≤ η + (2(ρ + ε))^d (2π σ² s)^{-d/2}`
(`coupling_ball_bound`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace ElboimSly.Paper.Step

open ElboimSly.Paper ElboimSly.Bridge

variable {d : ℕ} {β : ℝ} [Fact (0 < β)]

theorem coupling_ball_bound {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {N : Ω → Measure (ℕ × RingSpace d β)}
    (hN : IsPoissonPointProcess N ((Measure.count : Measure ℕ).prod (ringIntensity d β)) P)
    {T : ℝ≥0} {σ ε η : ℝ} (hσ : 0 < σ) (hε : 0 ≤ ε)
    (h : AdmitsBMCoupling d T
      (P.map (fun ω (t : Set.Icc (0 : ℝ≥0) T) =>
        regenWalk (fun k => copyEnv (N ω) k) ((t : ℝ≥0) : ℝ))) σ ε η)
    {s : ℝ≥0} (hs : s ≤ T) (hs0 : s ≠ 0) (v : Fin d → ℤ) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    P {ω | ‖regenWalk (fun k => copyEnv (N ω) k) (s : ℝ) - v‖ ≤ ρ} ≤
      ENNReal.ofReal η +
        ENNReal.ofReal ((2 * (ρ + ε)) ^ d * (2 * Real.pi * (σ ^ 2 * s)) ^ (-(d : ℝ) / 2)) := by
  obtain ⟨Q, hQ, hlaw, hB, -, hbad⟩ := exists_standardBrownianMotion_of_admitsBMCoupling h
  set B := zeroMod (Prod.snd : WalkPath d T × C(ℝ≥0, Fin d → ℝ) → _) with hBdef
  set E' : Set (Set.Icc (0 : ℝ≥0) T → Fin d → ℤ) :=
    {w | ‖w ⟨s, zero_le, hs⟩ - v‖ ≤ ρ} with hE'
  have hE'm : MeasurableSet E' := by
    have : Measurable fun w : Set.Icc (0 : ℝ≥0) T → Fin d → ℤ => w ⟨s, zero_le, hs⟩ - v :=
      (measurable_pi_apply _).sub measurable_const
    exact measurableSet_le (measurable_of_countable (fun x : Fin d → ℤ => ‖x‖) |>.comp this)
      measurable_const
  have hF := aemeasurable_regenWalk_Icc hN T
  have e1 : P {ω | ‖regenWalk (fun k => copyEnv (N ω) k) (s : ℝ) - v‖ ≤ ρ} =
      Q {p | ‖p.1.1 ⟨s, zero_le, hs⟩ - v‖ ≤ ρ} := by
    have h1 : P {ω | ‖regenWalk (fun k => copyEnv (N ω) k) (s : ℝ) - v‖ ≤ ρ} =
        (P.map (fun ω (t : Set.Icc (0 : ℝ≥0) T) =>
          regenWalk (fun k => copyEnv (N ω) k) ((t : ℝ≥0) : ℝ))) E' := by
      rw [Measure.map_apply_of_aemeasurable hF hE'm]; rfl
    rw [h1, ← hlaw, Measure.map_apply (by fun_prop) hE'm]; rfl
  rw [e1]
  set A : Set (WalkPath d T × C(ℝ≥0, Fin d → ℝ)) :=
    {p | ENNReal.ofReal ε ≤ ⨆ t : Set.Icc (0 : ℝ≥0) T,
      ENNReal.ofReal ‖(fun i => ((p.1.1 t i : ℤ) : ℝ)) - σ • B (t : ℝ≥0) p‖} with hA
  set Bl : Set (WalkPath d T × C(ℝ≥0, Fin d → ℝ)) :=
    {p | ‖(0 : Fin d → ℝ) + σ • B s p - (fun i => ((v i : ℤ) : ℝ))‖ ≤ ρ + ε} with hBl
  have hsub : {p : WalkPath d T × C(ℝ≥0, Fin d → ℝ) | ‖p.1.1 ⟨s, zero_le, hs⟩ - v‖ ≤ ρ} ⊆ A ∪ Bl := by
    intro p hp
    by_cases hpA : p ∈ A
    · exact Or.inl hpA
    · refine Or.inr ?_
      have hlt : ‖(fun i => ((p.1.1 ⟨s, zero_le, hs⟩ i : ℤ) : ℝ)) - σ • B s p‖ < ε := by
        by_contra hcon
        rw [not_lt] at hcon
        apply hpA
        refine le_trans (ENNReal.ofReal_le_ofReal hcon) ?_
        exact le_iSup (fun t : Set.Icc (0 : ℝ≥0) T =>
          ENNReal.ofReal ‖(fun i => ((p.1.1 t i : ℤ) : ℝ)) - σ • B (t : ℝ≥0) p‖)
            ⟨s, zero_le, hs⟩
      have hv : ‖(fun i => ((p.1.1 ⟨s, zero_le, hs⟩ i : ℤ) : ℝ)) - (fun i => ((v i : ℤ) : ℝ))‖ ≤ ρ := by
        have : (fun i => ((p.1.1 ⟨s, zero_le, hs⟩ i : ℤ) : ℝ)) - (fun i => ((v i : ℤ) : ℝ)) =
            fun i => (((p.1.1 ⟨s, zero_le, hs⟩ - v) i : ℤ) : ℝ) := by
          funext i; simp
        rw [this, norm_intCast_pi]; exact hp
      show ‖(0 : Fin d → ℝ) + σ • B s p - (fun i => ((v i : ℤ) : ℝ))‖ ≤ ρ + ε
      calc ‖(0 : Fin d → ℝ) + σ • B s p - (fun i => ((v i : ℤ) : ℝ))‖
          = ‖(σ • B s p - (fun i => ((p.1.1 ⟨s, zero_le, hs⟩ i : ℤ) : ℝ))) +
              ((fun i => ((p.1.1 ⟨s, zero_le, hs⟩ i : ℤ) : ℝ)) - (fun i => ((v i : ℤ) : ℝ)))‖ := by
            congr 1; simp
        _ ≤ ‖σ • B s p - (fun i => ((p.1.1 ⟨s, zero_le, hs⟩ i : ℤ) : ℝ))‖ +
              ‖(fun i => ((p.1.1 ⟨s, zero_le, hs⟩ i : ℤ) : ℝ)) - (fun i => ((v i : ℤ) : ℝ))‖ :=
            norm_add_le _ _
        _ ≤ ε + ρ := by
            rw [norm_sub_rev]; exact add_le_add hlt.le hv
        _ = ρ + ε := add_comm _ _
  have hs0' : s ≠ 0 := hs0
  have hball := hB.measure_closedBall_le (P := Q) hs0' 0 (fun i => ((v i : ℤ) : ℝ)) hσ
    (r := ρ + ε) (by linarith)
  calc Q {p | ‖p.1.1 ⟨s, zero_le, hs⟩ - v‖ ≤ ρ} ≤ Q (A ∪ Bl) := measure_mono hsub
    _ ≤ Q A + Q Bl := measure_union_le _ _
    _ ≤ _ := add_le_add hbad hball

end ElboimSly.Paper.Step
