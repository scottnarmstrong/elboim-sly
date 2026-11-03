/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycSchemeEnvEnded
public import ElboimSly.Foundations.Cyclic.CycSchemeEnvKappa
public import ElboimSly.Foundations.Cyclic.CycSchemeEnvPureExt2
public import ElboimSly.Foundations.Cyclic.CycRecLimitMeas
public import ElboimSly.Foundations.PPP.Exploration.ThmStop
public import Mathlib

/-!
# The environment scheme (c): the explored region at the ending index

The environment scheme (c). Let `run` be a run of `cycScheme P s_∘ U` (`K ≥ 1`), and `κ`
the ending index (`kappa`).

* `Zkappa run ω` is `𝒵_κ`: `𝒵_κ` on `{κ < ∞}`, and `𝒵_∞ = ⋃_j 𝒵_j` on `{κ = ∞}`.
* `ae_Zkappa_eq`: almost surely `𝒵_κ = R^𝒫_{s_∘}`, the region of `cycRec^𝒫(s_∘)` (`cycRecAt`).
* `recPhi`: the limit map `Φ : ℋ_∞ → Rec` of the records `ρ_j(π_j y)` of the pure scheme
  (measurability of record functionals (e) applies on all of `ℋ_∞`, by `CycScheme.extends_stateAt_trunc`); it is
  measurable (`measurable_recPhi`).
* `recKappa run junk ω` is the record at the ending index: `ρ_κ(H_κ)` if `κ < ∞` and
  `Φ(H_∞)` if `κ = ∞`. Almost surely it is `cycRec^𝒫(s_∘)` (`ae_recKappa_eq`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic
namespace CycSchemeEnv
variable {I : Type*} [MeasurableSpace I] [Countable I] [MeasurableSingletonClass I] {d : ℕ} {β : ℝ}
  [Fact (0 < β)] {P : CycPlan I d β} {sc : ℝ≥0∞}
variable {U : Type*} [MeasurableSpace U] {Ω : Type*} [MeasurableSpace Ω] {Pr : Measure Ω}

/-- The records `ρ_j(π_j y)` of the pure scheme along an element `y` of `ℋ_∞`. -/
noncomputable abbrev recSeqY (P : CycPlan I d β) (sc : ℝ≥0∞) (U : Type*) [MeasurableSpace U] (j : ℕ)
    (y : U × (ℕ → Outcome (CycS I d β))) : CycRec I d :=
  (CycScheme.stateAt P sc j (truncHist j y)).1

/-- The limit map `Φ : ℋ_∞ → Rec` of the records of the pure scheme. -/
noncomputable def recPhi (P : CycPlan I d β) (sc : ℝ≥0∞) (U : Type*) [MeasurableSpace U]
    (junk : CycEntry I d) : U × (ℕ → Outcome (CycS I d β)) → CycRec I d :=
  recLim (ρ := recSeqY P sc U) junk fun j y => CycScheme.extends_stateAt_trunc P sc j y

theorem measurable_recPhi (junk : CycEntry I d) : Measurable (recPhi P sc U junk) :=
  measurable_recLim (ρ := recSeqY P sc U) (fun j =>
    ((CycScheme.measurable_stateAt P sc j).fst).comp (measurable_truncHist j)) junk _

/-- `𝒵_κ`: the explored region at the ending index (`𝒵_∞ = ⋃_j 𝒵_j` on `{κ = ∞}`). -/
noncomputable def Zkappa (run : ExplRun (cycScheme P sc U) Pr) (ω : Ω) : Set (CycS I d β) :=
  (kappa run ω).recTopCoe ((cycScheme P sc U).Zinf (run.Hinf ω))
    (fun j => (cycScheme P sc U).Z j (run.H j ω))

/-- The record at the ending index: `ρ_κ(H_κ)`, and `Φ(H_∞)` on `{κ = ∞}`. -/
noncomputable def recKappa (run : ExplRun (cycScheme P sc U) Pr) (junk : CycEntry I d) (ω : Ω) :
    CycRec I d :=
  (kappa run ω).recTopCoe (recPhi P sc U junk (run.Hinf ω))
    (fun j => (CycScheme.stateAt P sc j (run.H j ω)).1)

variable (run : ExplRun (cycScheme P sc U) Pr)

theorem Z_eq_region' (j : ℕ) (ω : Ω) :
    (cycScheme P sc U).Z j (run.H j ω) = (CycScheme.stateAt P sc j (run.H j ω)).1.region β :=
  CycScheme.Z_eq_region P sc (cycScheme P sc U) (fun _ _ => rfl) (fun _ _ => rfl) j _

theorem Zinf_eq_iUnion (ω : Ω) :
    (cycScheme P sc U).Zinf (run.Hinf ω) = ⋃ j, (CycScheme.stateAt P sc j (run.H j ω)).1.region β := by
  unfold ExplScheme.Zinf
  refine iUnion_congr fun j => ?_
  rw [← run.H_eq_trunc j ω]
  exact Z_eq_region' run j ω

/-- On the good event, the limit map `Φ` at `H_∞(ω)` is the limit of the records of the trajectory. -/
theorem recPhi_eq_recLim (junk : CycEntry I d) (hK : 0 < P.K) {ω : Ω} (hω : GoodEv run ω) :
    recPhi P sc U junk (run.Hinf ω) =
      recLim junk ((trajOf run ω hω).hext hω.1 hK rfl) () := by
  unfold recPhi
  rw [recLim_point (ρ := recSeqY P sc U)]
  refine recLim_congr_seq ?_ junk _ _
  funext j _
  show (CycScheme.stateAt P sc j (truncHist j (run.Hinf ω))).1 =
    (CycScheme.stateAt P sc j (run.H j ω)).1
  rw [run.H_eq_trunc j ω]

/-- The environment scheme (c): almost surely `𝒵_κ = R^𝒫_{s_∘}`. -/
theorem ae_Zkappa_eq (hK : 0 < P.K) :
    ∀ᵐ ω ∂Pr, Zkappa run ω = (cycRecAt P (run.N ω) sc).region β := by
  filter_upwards [goodEv_ae run] with ω hω
  have hT := (trajOf run ω hω).recLim_eq_cycRecAt P.junk hω.1 hK rfl
  unfold Zkappa
  induction hκ : kappa run ω using ENat.recTopCoe with
  | top =>
    simp only [ENat.recTopCoe_top]
    rw [Zinf_eq_iUnion, ← hT, (trajOf run ω hω).region_recLim_eq P.junk hω.1 hK rfl]
    rfl
  | coe j =>
    simp only [ENat.recTopCoe_natCast]
    have hend := ((kappa_eq_iff run ω j).1 hκ).1
    rw [Z_eq_region', ← hT, (trajOf run ω hω).recLim_eq_of_ended P.junk hω.1 hK rfl hend]
    rfl

/-- Almost surely the record at the ending index is `cycRec^𝒫(s_∘)`. -/
theorem ae_recKappa_eq (junk : CycEntry I d) (hK : 0 < P.K) :
    ∀ᵐ ω ∂Pr, recKappa run junk ω = cycRecAt P (run.N ω) sc := by
  filter_upwards [goodEv_ae run] with ω hω
  have hT := (trajOf run ω hω).recLim_eq_cycRecAt junk hω.1 hK rfl
  unfold recKappa
  induction hκ : kappa run ω using ENat.recTopCoe with
  | top =>
    simp only [ENat.recTopCoe_top]
    rw [recPhi_eq_recLim run junk hK hω, hT]
  | coe j =>
    simp only [ENat.recTopCoe_natCast]
    have hend := ((kappa_eq_iff run ω j).1 hκ).1
    rw [← hT, (trajOf run ω hω).recLim_eq_of_ended junk hω.1 hK rfl hend]
    rfl

end CycSchemeEnv
end ElboimSly.Cyclic

end
