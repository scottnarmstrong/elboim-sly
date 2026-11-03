/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Heavy.TauHatInterface
public import ElboimSly.Paper.Heavy.Es4Canon

/-!
# `P(W ∉ Γ_n)` for a single Poisson environment

Discovered bad blocks for two walks, first bound (ES22 §7): for a Poisson point process `N₀` of
intensity `μ_β` (a single, non-regenerated environment), `W^{N₀}_{0,0}` is the first piece of
construction (i) for `N = (N₀, ·)`, so `P(W^{N₀}_{0,0} ∉ Γ_n) ≤ A_n e^{-c_♭ n³}` by mathbbP(𝒢(i))ge1-e^-cn^3,
up to the interface `HeavyEscInterface`. The transfer between the two probability spaces uses
uniqueness in law of Poisson point processes.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Step

open ElboimSly ElboimSly.Paper ElboimSly.Paper.Heavy ElboimSly.Cyclic ElboimSly.Interchange

variable {d : ℕ} {β : ℝ} [Fact (0 < β)]

/-- mathbbP(𝒢(i))ge1-e^-cn^3 for a single environment, up to the interface. -/
theorem heavyGamma_single {E : HeavyEscConsts} {n₀ n : ℕ} {t₀ : ℝ}
    (hI : HeavyEscInterface d β E n₀ n t₀) (hp : Es4Params d β n₀ n t₀)
    (hT : HeavyT d n₀ E n) (hβ5 : E.beta5 ≤ β) (ht0 : 0 < t₀) (hn : 1 ≤ n)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {N₀ : Ω → Measure (RingSpace d β)}
    (hN₀ : IsPoissonPointProcess N₀ (ringIntensity d β) P) :
    P {ω | ¬ heavyGamma d β t₀ n (fun s => cycWalk (N₀ ω) 0 0 s)} ≤
      ENNReal.ofReal (heavyA d n * Real.exp (-(heavyc d E * (n : ℝ) ^ 3))) := by
  obtain ⟨Ω', mΩ', P', N, hP', hN, -⟩ :=
    exists_isPoissonPointProcess ((Measure.count : Measure ℕ).prod (ringIntensity d β))
  have h := es6_tauhat_of_params (Pe := P') (N := N) hI hN hp hT hβ5 0
  obtain ⟨S, hS, hSX⟩ :=
    exists_measurableSet_val (measurableSet_gammaSet (d := d) (β := β) ht0 hn)
  set B : Set (Measure (RingSpace d β)) := (fun ν => trajProc ν 0 0) ⁻¹' Sᶜ with hB
  have hBm : MeasurableSet B := (measurable_trajProc 0 0) hS.compl
  have key : ∀ ν : Measure (RingSpace d β), Good ν →
      (ν ∈ B ↔ ¬ heavyGamma d β t₀ n (fun s => cycWalk ν 0 0 s)) := by
    intro ν hg
    have hcyc := isCyclicPath_cycWalk hg
    have hmem : (⟨fun s : ℝ => cycWalk ν 0 0 s, hcyc⟩ : CycPathSpace d) ∈ gammaSet d β t₀ n ↔
        heavyGamma d β t₀ n (fun s => cycWalk ν 0 0 s) := Iff.rfl
    have hval : (fun (p : CycPathSpace d) (s : ℝ≥0) => p.1 (s : ℝ))
        ⟨fun s : ℝ => cycWalk ν 0 0 s, hcyc⟩ = trajProc ν 0 0 := by
      funext s; exact cycWalk_eq_trajProc hg 0 0 s
    have k2 : (trajProc ν 0 0 ∈ S) ↔ heavyGamma d β t₀ n (fun s => cycWalk ν 0 0 s) := by
      rw [← hval, ← hmem, ← hSX]; rfl
    simp only [hB, mem_preimage, mem_compl_iff, k2]
  have hae₀ : {ω | ¬ heavyGamma d β t₀ n (fun s => cycWalk (N₀ ω) 0 0 s)} =ᵐ[P]
      N₀ ⁻¹' B := by
    filter_upwards [ae_good hN₀] with ω hω
    exact propext (key _ hω).symm
  have hae₁ : (fun ω => cycSlice 0 (N ω)) ⁻¹' B =ᵐ[P']
      {ω | ¬ heavyGamma d β t₀ n (heavyPiece (geoSlices N ω) 0)} := by
    filter_upwards [ae_cycGood hN] with ω hω
    exact propext (key _ (hω 0))
  have h0 := isPoissonPointProcess_slice hN 0
  have hlaw : P'.map (fun ω => cycSlice 0 (N ω)) = P.map N₀ := hN₀.map_eq_map h0
  have := hN₀.isProbabilityMeasure
  calc P {ω | ¬ heavyGamma d β t₀ n (fun s => cycWalk (N₀ ω) 0 0 s)}
      = P (N₀ ⁻¹' B) := measure_congr hae₀
    _ = (P.map N₀) B := (Measure.map_apply hN₀.measurable hBm).symm
    _ = (P'.map (fun ω => cycSlice 0 (N ω))) B := by rw [hlaw]
    _ = P' ((fun ω => cycSlice 0 (N ω)) ⁻¹' B) := Measure.map_apply h0.measurable hBm
    _ = P' {ω | ¬ heavyGamma d β t₀ n (heavyPiece (geoSlices N ω) 0)} := measure_congr hae₁
    _ ≤ _ := h

end ElboimSly.Paper.Step

end
