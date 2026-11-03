/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Base.IdentLaw
public import ElboimSly.Foundations.SRW.KernelDef
public import ElboimSly.Foundations.Interchange.LawInvariance
public import Mathlib

/-!
# Cyclic walks within one lap: one walk

Cyclic walks within one lap (a).

For `T ≤ β` the cyclic walk `W^ν_{a,r}` of a Poisson environment, translated by `-a` and stopped
at `T`, has the law of a stopped SRW (`one_lap_a_model`, `one_lap_a`).  The path is the process
`trajProc ν a r`, which agrees with the cyclic walk on good environments.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Paper

open ElboimSly.SRW ElboimSly.Cyclic ElboimSly.Interchange

variable {d : ℕ} {β : ℝ} [Fact (0 < β)]

/-- **cyclic walks within one lap (a)**, against the model SRW law. -/
theorem one_lap_a_model {Ω : Type} [MeasurableSpace Ω] {Pe : Measure Ω}
    {ν : Ω → Measure (RingSpace d β)}
    (hν : IsPoissonPointProcess ν (ringIntensity d β) Pe) (a : Fin d → ℤ) (r : ℝ) {T : ℝ≥0}
    (hT : (T : ℝ) ≤ β) :
    Pe.map (fun ω (s : ℝ≥0) => trajProc (ν ω) a r (min s T) - a) =
      (srwP d).map (fun ω s => srwZ d ω (min s T)) := by
  obtain ⟨Ωd, mΩd, Pd, N₀, hPd, hN₀, -⟩ := exists_isPoissonPointProcess_clockIntensity (Dir d)
  have hcan := canonical_isSRW hN₀
  have hTb : T ≤ β.toNNReal := by
    rw [← NNReal.coe_le_coe]; simpa [Real.coe_toNNReal _ (Fact.out : 0 < β).le] using hT
  set b := β.toNNReal with hb
  have hgood : ∀ᵐ ω ∂Pe, Good (ν ω) := ae_good hν
  have hlaw := cyc_srw_short_law hν hN₀ a r
  have hE := measurable_extStop (d := d) b T hTb
  have hlaw' : Pe.map (fun ω => restrictIic b (fun s : ℝ≥0 => trajProc (ν ω) a r s - a)) =
      Pd.map (fun ω => restrictIic b (canonical d N₀ ω)) := by
    rw [← hlaw]
    refine Measure.map_congr ?_
    filter_upwards [hgood] with ω hω
    funext s
    show trajProc (ν ω) a r s.1 - a = ElboimSly.cycWalk (ν ω) a r (s.1 : ℝ) - a
    rw [cycWalk_eq_trajProc hω]
  have hmeas1 : Measurable fun ω => restrictIic b (fun s : ℝ≥0 => trajProc (ν ω) a r s - a) := by
    refine measurable_pi_iff.2 fun s => ?_
    exact (measurable_of_countable (fun x : Fin d → ℤ => x - a)).comp
      ((measurable_pi_apply s.1).comp ((measurable_trajProc a r).comp hν.measurable))
  have hmeas2 : Measurable fun ω => restrictIic b (canonical d N₀ ω) :=
    (measurable_restrictIic b).comp (measurable_canonical hN₀.measurable)
  have e1 : Pe.map (fun ω (s : ℝ≥0) => trajProc (ν ω) a r (min s T) - a) =
      (Pe.map (fun ω => restrictIic b (fun s : ℝ≥0 => trajProc (ν ω) a r s - a))).map
        (extStop b T hTb) := by
    rw [Measure.map_map hE hmeas1]
    rfl
  have e2 : (srwP d).map (fun ω s => srwZ d ω (min s T)) =
      (Pd.map (fun ω => restrictIic b (canonical d N₀ ω))).map (extStop b T hTb) := by
    rw [Measure.map_map hE hmeas2]
    have h1 : (srwP d).map (fun ω s => srwZ d ω (min s T)) =
        ((srwP d).map (srwZ d)).map (stopPath T) :=
      (Measure.map_map (measurable_stopPath T) (srwZ_isSRW d).1).symm
    rw [h1, ← hcan.map_eq_model, Measure.map_map (measurable_stopPath T)
      (measurable_canonical hN₀.measurable)]
    refine Measure.map_congr (Filter.Eventually.of_forall fun ω => ?_)
    exact (extStop_restrict b T hTb _).symm
  rw [e1, e2, hlaw']

/-- **cyclic walks within one lap (a)**: for `T ≤ β`, `(W^ν_{a,r}(s ∧ T) - a)_s` has the law of
`(X(s ∧ T))_s` for every SRW `X`. -/
theorem one_lap_a {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω'] {Pe : Measure Ω}
    {Pd : Measure Ω'} {ν : Ω → Measure (RingSpace d β)}
    (hν : IsPoissonPointProcess ν (ringIntensity d β) Pe) {X : Ω' → PathSpace d}
    (hX : IsSRW Pd X) (a : Fin d → ℤ) (r : ℝ) {T : ℝ≥0} (hT : (T : ℝ) ≤ β) :
    Pe.map (fun ω (s : ℝ≥0) => trajProc (ν ω) a r (min s T) - a) =
      Pd.map (fun ω (s : ℝ≥0) => X ω (min s T)) := by
  rw [one_lap_a_model hν a r hT]
  have h1 : (srwP d).map (fun ω s => srwZ d ω (min s T)) =
      ((srwP d).map (srwZ d)).map (stopPath T) :=
    (Measure.map_map (measurable_stopPath T) (srwZ_isSRW d).1).symm
  have h2 : Pd.map (fun ω (s : ℝ≥0) => X ω (min s T)) = (Pd.map X).map (stopPath T) :=
    (Measure.map_map (measurable_stopPath T) hX.1).symm
  rw [h1, h2, hX.map_eq_model]

end ElboimSly.Paper

end
