/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycLawTransfer
public import ElboimSly.Foundations.Cyclic.CycRegenLawMeas2
public import ElboimSly.Foundations.Cyclic.CycRegenEnvAe
public import ElboimSly.Foundations.Cyclic.CycDrivenLawBridge
public import ElboimSly.Foundations.Cyclic.CycFirstEvents2
public import Mathlib

/-!
# The three constructions of the regenerated walk have the same law

The constructions of the regenerated walk. The regenerated walk of regenerated cyclic walk, built (i) from the
copies of a Poisson environment on `ℕ × S_β`, (ii) from the sub-processes of a Poisson driver on
`(𝒟 × ℕ) × ℝ` (i.i.d. canonical SRWs, independent families), or (iii) from one canonical SRW cut at the
regeneration times, has the same law, as a process `ℝ≥0 → ℤᵈ` with the product `σ`-algebra. The
a.s. identities with `W_reg` of the final record of `𝒫_reg` are `ae_regRecWalk_envFinal`,
`ae_regRecWalk_indep` and `ae_regRecWalk_cut`; the law identity is several walks explored one after another (b)
(`law_transfer`), with `W_reg` measurable in the record (`measurable_regRecWalk`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

open SRW

variable {d : ℕ} {β : ℝ} [Fact (0 < β)]

/-- The regenerated walk of a record, as a process. -/
noncomputable def regRecProc (ρ : CycRec ℕ d) : ℝ≥0 → Fin d → ℤ := fun t => regRecWalk ρ t

theorem measurable_regRecProc : Measurable (regRecProc (d := d)) := by
  have : Nonempty (CycEntry ℕ d) := ⟨(regPlan d 1).junk⟩
  exact measurable_pi_iff.2 fun t => measurable_regRecWalk t

omit [Fact (0 < β)] in
theorem hK_regPlan : 0 < (regPlan d β).K := by
  show (0 : ℕ∞) < ⊤
  exact lt_of_lt_of_le zero_lt_one le_top

/-- Construction (iii): almost surely `W_reg` of the driven final record is `W^x_reg`. -/
theorem regen_cut_ae {Ω' : Type*} [MeasurableSpace Ω'] {Pd : Measure Ω'}
    {N₀ : Ω' → Measure (Dir d × ℝ)}
    (hN₀ : IsPoissonPointProcess N₀ (clockIntensity (Dir d)) Pd) :
    ∀ᵐ Ñ ∂(Pd.map fun ω => drvUnit (N₀ ω)),
      regRecProc ((regPlan d β).drivenFinal (J := Unit) (fun _ _ => ())
        (fun j => srwPath Ñ j)) =
        fun t => drivenRegenFrom β.toNNReal (srwPath Ñ ()).1.fn t := by
  have hb : 0 < β.toNNReal := Real.toNNReal_pos.2 Fact.out
  have hWd : IsPoissonPointProcess (fun Ñ : Measure ((Dir d × Unit) × ℝ) => Ñ)
      (drvIntensity d Unit) (Pd.map fun ω => drvUnit (N₀ ω)) := (isPPP_drvUnit hN₀).isPPPLaw_map
  have hae := ae_regRecWalk_cut (β := β) (N := fun Ñ : Measure ((Dir d × Unit) × ℝ) =>
    subProcess (fun Ñ => Ñ) () Ñ) (subProcess_ppp (ι := Unit) hWd ())
  filter_upwards [hae] with Ñ h
  have h0 : (srwPath Ñ ()).1.fn 0 = 0 := (walkPath_isDriving _).zero
  funext t
  rw [← drivenRegenWalkCut_eq_drivenRegenFrom hb h0 t]
  exact h t

theorem drivenRegenFrom_drvUnit (N₀ : Measure (Dir d × ℝ)) :
    (fun t : ℝ≥0 => drivenRegenFrom β.toNNReal (srwPath (drvUnit N₀) ()).1.fn t) =
      fun t : ℝ≥0 => drivenRegenWalkCut β.toNNReal (fun s : ℝ≥0 => walk d N₀ (s : ℝ)) t := by
  have hb : 0 < β.toNNReal := Real.toNNReal_pos.2 Fact.out
  have hfn : (srwPath (drvUnit N₀) ()).1.fn = fun s : ℝ≥0 => walk d N₀ (s : ℝ) :=
    funext (srwPath_drvUnit_fn N₀)
  have h0 : (fun s : ℝ≥0 => walk d N₀ (s : ℝ)) 0 = 0 := by simp [walk_zero]
  funext t
  rw [hfn, drivenRegenWalkCut_eq_drivenRegenFrom hb h0 t]

/-- Construction (i): the regenerated walk of the slices is `W_reg` of the environment record. -/
theorem regen_env_ae {Ω : Type*} [MeasurableSpace Ω] {Pe : Measure Ω}
    {N : Ω → Measure (ℕ × RingSpace d β)}
    (hN : IsPoissonPointProcess N ((Measure.count : Measure ℕ).prod (ringIntensity d β)) Pe) :
    ∀ᵐ ω ∂Pe, (fun t : ℝ≥0 => ElboimSly.regenWalk (fun k => cycSlice k (N ω)) ((t : ℝ≥0) : ℝ)) =
      regRecProc ((regPlan d β).envFinalOr CycRec.empty (N ω)) := by
  filter_upwards [ae_regRecWalk_envFinal hN, ae_cycGood hN] with ω h1 h2
  funext t
  rw [(regPlan d β).envFinalOr_of_good _ h2]
  exact (h1 t).symm

/-- **the constructions of the regenerated walk, (i) = (iii)**, after a measurable functional `T` of the path. -/
theorem regen_law_env_cut_map {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {Pe : Measure Ω} {Pd : Measure Ω'} {N : Ω → Measure (ℕ × RingSpace d β)}
    {N₀ : Ω' → Measure (Dir d × ℝ)}
    (hN : IsPoissonPointProcess N ((Measure.count : Measure ℕ).prod (ringIntensity d β)) Pe)
    (hN₀ : IsPoissonPointProcess N₀ (clockIntensity (Dir d)) Pd)
    {γ : Type*} [MeasurableSpace γ] {T : (ℝ≥0 → Fin d → ℤ) → γ} (hT : Measurable T) :
    Pe.map (fun ω => T (fun t : ℝ≥0 =>
        ElboimSly.regenWalk (fun k => cycSlice k (N ω)) ((t : ℝ≥0) : ℝ))) =
      Pd.map (fun ω => T (fun t : ℝ≥0 =>
        drivenRegenWalkCut β.toNNReal (canonical d N₀ ω) t)) := by
  have hb : 0 < β.toNNReal := Real.toNNReal_pos.2 Fact.out
  have : Nonempty (CycEntry ℕ d) := ⟨(regPlan d β).junk⟩
  have hNd := isPPP_drvUnit hN₀
  have hmenv := (regPlan d β).measurable_envFinalOr CycRec.empty
  have hB : Measurable fun Ñ : Measure ((Dir d × Unit) × ℝ) =>
      T (fun t => drivenRegenFrom β.toNNReal (srwPath Ñ ()).1.fn t : ℝ≥0 → Fin d → ℤ) :=
    hT.comp (measurable_pi_iff.2 fun t => measurable_drivenRegenFrom_at hb
      (X := fun Ñ => (srwPath Ñ ()).1) (measurable_srwPath ()) t)
  have hBd : ∀ᵐ Ñ ∂(Pd.map fun ω => drvUnit (N₀ ω)),
      (T ∘ regRecProc) ((regPlan d β).drivenFinal (J := Unit) (fun _ _ => ())
        (fun j => srwPath Ñ j)) =
      T (fun t => drivenRegenFrom β.toNNReal (srwPath Ñ ()).1.fn t) := by
    filter_upwards [regen_cut_ae (β := β) hN₀] with Ñ h
    exact congrArg T h
  have key := law_transfer (jx := fun _ _ => ()) () (regPlan d β) (fun _ => measurable_const)
    hK_regPlan hN hNd (ae_cycGood hN) (Φ := T ∘ regRecProc) (hT.comp measurable_regRecProc)
    (A := fun ν => T (regRecProc ((regPlan d β).envFinalOr CycRec.empty ν)))
    (hT.comp (measurable_regRecProc.comp hmenv)) hB
    (fun ν hν => by
      show T (regRecProc ((regPlan d β).envFinal ν)) = _
      rw [(regPlan d β).envFinalOr_of_good _ hν]) hBd
  have e1 : Pe.map (fun ω => T (fun t : ℝ≥0 =>
        ElboimSly.regenWalk (fun k => cycSlice k (N ω)) ((t : ℝ≥0) : ℝ))) =
      Pe.map (fun ω => T (regRecProc ((regPlan d β).envFinalOr CycRec.empty (N ω)))) := by
    refine Measure.map_congr ?_
    filter_upwards [regen_env_ae hN] with ω h
    exact congrArg T h
  rw [e1, ← key]
  refine Measure.map_congr (Filter.Eventually.of_forall fun ω => ?_)
  exact congrArg T (drivenRegenFrom_drvUnit (N₀ ω))

/-- **the constructions of the regenerated walk, (i) = (iii)**. -/
theorem regen_law_env_cut {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {Pe : Measure Ω} {Pd : Measure Ω'} {N : Ω → Measure (ℕ × RingSpace d β)}
    {N₀ : Ω' → Measure (Dir d × ℝ)}
    (hN : IsPoissonPointProcess N ((Measure.count : Measure ℕ).prod (ringIntensity d β)) Pe)
    (hN₀ : IsPoissonPointProcess N₀ (clockIntensity (Dir d)) Pd) :
    Pe.map (fun ω (t : ℝ≥0) => ElboimSly.regenWalk (fun k => cycSlice k (N ω)) ((t : ℝ≥0) : ℝ)) =
      Pd.map (fun ω (t : ℝ≥0) =>
        drivenRegenWalkCut β.toNNReal (canonical d N₀ ω) t) :=
  regen_law_env_cut_map hN hN₀ (T := id) measurable_id

end ElboimSly.Cyclic

end
