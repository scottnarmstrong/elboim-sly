/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycSchemeEnvUpd
public import ElboimSly.Foundations.Cyclic.CycSchemeRegionZ
public import ElboimSly.Foundations.PPP.DissectingExamples
public import ElboimSly.Foundations.PPP.Exploration.ThmDirac
public import ElboimSly.Foundations.PPP.ExistenceExamples
public import Mathlib

/-!
# The environment scheme (b): the exploration theorem for the environment scheme

The environment scheme (b), the use of sequential first-point exploration (d), (f). `ae_stepGood`: for a run of
the scheme `cycScheme P sc U`, almost surely, at every unfinished step the outcome satisfies
`StepGood` (`CycSchemeEnvCore`): `V = N|_{R̃ ≤ ρ}`, `ρ ≤ h`, `R̃ = ρ` `V`-a.e., `V` is a Dirac
mass at a front point or `0`, and `V = 0` forces `ρ = h`. The explored region is
`cycReg(ρ_j)` by `Z_eq_region`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ElboimSly.Circle
open scoped ENNReal NNReal

namespace ElboimSly

section Generic

variable {S : Type*} [MeasurableSpace S] {U : Type*} [MeasurableSpace U] {μ : Measure S}
  [SigmaFinite μ] {sch : ExplScheme μ U} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- Almost surely, if the revealed measure of step `k` is `0`, the entrance time is the horizon. -/
theorem ExplRun.ae_rho_eq_h (run : ExplRun sch P) (k : ℕ) :
    ∀ᵐ ω ∂P, (run.H (k + 1) ω).last.2 Set.univ = 0 →
      (run.H (k + 1) ω).last.1 = (sch.h k (run.H k ω) : ℝ≥0∞) := by
  let B : Set (Hist U S k × Outcome S) := {q | q.2.2 Set.univ = 0 ∧ q.2.1 ≠ (sch.h k q.1 : ℝ≥0∞)}
  have hm : Measurable fun q : Hist U S k × Outcome S => q.2.2 Set.univ :=
    (Measure.measurable_coe MeasurableSet.univ).comp (measurable_snd.comp measurable_snd)
  have hm2 : Measurable fun q : Hist U S k × Outcome S => q.2.1 := measurable_fst.comp measurable_snd
  have hm3 : Measurable fun q : Hist U S k × Outcome S => (sch.h k q.1 : ℝ≥0∞) :=
    measurable_coe_nnreal_ennreal.comp ((sch.measurable_h k).comp measurable_fst)
  have hB : MeasurableSet B :=
    (measurableSet_eq_fun hm measurable_const).inter (measurableSet_eq_fun hm2 hm3).compl
  have := run.ae_last_not_mem (k := k) hB fun η => by
    filter_upwards [ae_goodSet run.isPPPLaw (sch.isProbe_Rt k η) (B := Set.univ)
      MeasurableSet.univ] with ν hν hmem
    obtain ⟨hlf, hreg, -, -⟩ := hν
    obtain ⟨hz, hne⟩ := hmem
    have hR := (sch.isProbe_Rt k η).measurable
    change probeV μ (sch.Rt k η) (sch.h k η) ν Set.univ = 0 at hz
    change probeRho μ (sch.Rt k η) (sch.h k η) ν ≠ (sch.h k η : ℝ≥0∞) at hne
    have hlt : probeRho μ (sch.Rt k η) (sch.h k η) ν < (sch.h k η : ℝ≥0∞) :=
      lt_of_le_of_ne probeRho_le_h hne
    have h1 := (probeRho_le_iff hR hlf hreg hlt).1 le_rfl
    rw [probeV_univ hlf] at hz
    rw [hz] at h1
    exact absurd h1 (by simp)
  filter_upwards [this] with ω hω hz
  by_contra hne
  exact hω ⟨hz, hne⟩

end Generic

namespace Cyclic
namespace CycSchemeEnv

variable {I : Type*} [MeasurableSpace I] [Countable I] [MeasurableSingletonClass I] {d : ℕ} {β : ℝ}
  [Fact (0 < β)]

theorem cycSeq_isDissecting : (cycSeq I d β).IsDissecting (cycIntensity I d β) :=
  SepPartSeq.prodCount_isDissecting (ringSeq (Edge d) β) (ringIntensity d β)
    (ringSeq_isDissecting (Edge d) β)

instance sigmaFinite_cycIntensity : SigmaFinite (cycIntensity I d β) := by
  unfold cycIntensity
  have : SigmaFinite (ringIntensity d β) := inferInstance
  infer_instance

omit [Countable I] [MeasurableSingletonClass I] in
theorem cycIntensity_singleton (x : CycS I d β) : cycIntensity I d β {x} = 0 := by
  have : ({x} : Set (CycS I d β)) = ({x.1} : Set I) ×ˢ ({x.2} : Set (RingSpace d β)) := by
    ext ⟨a, b⟩; simp [Prod.ext_iff]
  rw [this]
  unfold cycIntensity
  rw [Measure.prod_prod]
  have h2 : ringIntensity d β {x.2} = 0 := ring_singleton (E := Edge d) β x.2
  rw [h2, mul_zero]

variable {P : CycPlan I d β} {sc : ℝ≥0∞} {U : Type*} [MeasurableSpace U]

theorem Rt_eq_Rm (k : ℕ) (η : Hist U (CycS I d β) k)
    (hst : (CycScheme.stateAt P sc k η).2 = false) :
    (cycScheme P sc U).Rt k η = Rm P sc (CycScheme.stateAt P sc k η).1 := by
  funext y
  have hZ := CycScheme.Z_eq_region P sc (cycScheme P sc U) (fun _ _ => rfl) (fun _ _ => rfl) k η
  have hs : CycScheme.stateAt P sc k η = ((CycScheme.stateAt P sc k η).1, false) :=
    Prod.ext rfl hst
  unfold Rm
  by_cases hy : y ∈ (CycScheme.stateAt P sc k η).1.region β
  · rw [ite_eq_left hy]; exact (cycScheme P sc U).Rt_of_mem (hZ ▸ hy)
  · rw [ite_eq_right hy, (cycScheme P sc U).Rt_of_notMem (hZ ▸ hy)]
    show CycScheme.probeR P sc (CycScheme.stateAt P sc k η) y = _
    rw [← hs]

variable {Ω : Type*} [MeasurableSpace Ω] {Pr : Measure Ω}

/-- The environment scheme (b), the input from sequential first-point exploration: almost surely, at every
unfinished step the outcome is a good outcome (`StepGood`) for the configuration. -/
theorem ae_stepGood (run : ExplRun (cycScheme P sc U) Pr) :
    ∀ᵐ ω ∂Pr, ∀ j : ℕ, (CycScheme.stateAt P sc j (run.H j ω)).2 = false →
      StepGood P sc (run.N ω) (CycScheme.stateAt P sc j (run.H j ω)).1
        (run.H (j + 1) ω).last := by
  rw [ae_all_iff]
  intro j
  filter_upwards [run.ae_front j, run.ae_dirac_front (cycSeq I d β) cycSeq_isDissecting
    cycIntensity_singleton j, run.ae_rho_eq_h j] with ω hfront hdirac hzero hst
  set η := run.H j ω with hη
  have hRt := Rt_eq_Rm (P := P) (sc := sc) j η hst
  have hs' : CycScheme.stateAt P sc j η = ((CycScheme.stateAt P sc j η).1, false) :=
    Prod.ext rfl hst
  have hhs : ((cycScheme P sc U).h j η : ℝ≥0∞) =
      (CycScheme.hOf P sc ((CycScheme.stateAt P sc j η).1, false) : ℝ≥0∞) := by
    rw [← hs']; rfl
  have hl : (run.H (j + 1) ω).last = (cycScheme P sc U).stepAt j η (run.N ω) :=
    (cycScheme P sc U).Hfun_last j _
  have h1 : (run.H (j + 1) ω).last.1 =
      probeRho (cycIntensity I d β) ((cycScheme P sc U).Rt j η) ((cycScheme P sc U).h j η)
        (run.N ω) := by rw [hl]; rfl
  have h2 : (run.H (j + 1) ω).last.2 = (run.N ω).restrict
      (probeRegion ((cycScheme P sc U).Rt j η) (run.H (j + 1) ω).last.1) := by
    rw [h1, hl]
    show probeV _ _ _ _ = _
    unfold probeV
    rw [tau_of_mem (cycIntensity I d β) (run.lf ω)]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [h2, hRt]; rfl
  · rw [h1, ← hhs]; exact probeRho_le_h
  · rw [← hRt]; exact hfront
  · intro hne
    obtain ⟨x, hx1, -, hx3⟩ := hdirac hne
    exact ⟨x, hx1, by rw [← hRt]; exact hx3⟩
  · intro hz; rw [← hhs]; exact hzero hz

end CycSchemeEnv
end Cyclic

end ElboimSly

end
