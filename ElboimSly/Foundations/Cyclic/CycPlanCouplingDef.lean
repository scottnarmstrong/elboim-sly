/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycHitDef
public import ElboimSly.Foundations.Cyclic.CycEnvLocality
public import ElboimSly.Foundations.Cyclic.CycEnvMeas
public import ElboimSly.Foundations.Cyclic.CycMultiGood
public import ElboimSly.Foundations.Cyclic.CycSchemeEnvAe
public import ElboimSly.Foundations.Interchange.LawInvariance
public import Mathlib

/-!
# Environment paths of fixed data

Plan-level coupling after a stopping time, proof of (b) ("for every fixed datum
`δ' = (ι', u', q', σ')`, `Law(P^N_{δ'} - u') = Law(W)`").

* `envWalk ν δ`: the environment path `P^ν_δ` as a function `ℝ≥0 → ℤᵈ` (`≡ u` off good `ν`);
* `measurable_envWalk`: `(ν, δ) ↦ P^ν_δ` is measurable;
* `isPoissonPointProcess_envMeasure`: `N^{ι,σ}` is a `PPP(μ_β)`;
* `law_envWalk`: `Law(P^N_{δ'} - u') = Law(W)` for a `PPP(μ_β)`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set ElboimSly.Interchange
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

set_option linter.unusedSectionVars false

variable {I : Type*} [MeasurableSpace I] [Countable I] [MeasurableSingletonClass I] {d : ℕ}
  {β : ℝ} [Fact (0 < β)]

open scoped Classical in
/-- The environment path `P^ν_δ` of world-lines of a plan; joint exploration filtration (a), as a function `ℝ≥0 → ℤᵈ`; it is the constant
`u` if `ν` is not good. -/
@[irreducible] noncomputable def envWalk (ν : Measure (CycS I d β)) (δ : CycData I d) : ℝ≥0 → Fin d → ℤ :=
  if CycGood ν then envFn ν δ else fun _ => δ.start

theorem measurable_envFn_ngood (r : ℝ≥0) :
    Measurable fun q : Measure (CycS I d β) × CycData I d =>
      envFn (cycNgood (fun ν => ν) q.1) q.2 r := by
  have hng : Measurable fun ν : Measure (CycS I d β) => cycNgood (fun ν => ν) ν :=
    measurable_cycNgood measurable_id
  have h1 : Measurable fun q : Measure (CycS I d β) × CycData I d =>
      (⟨cycNgood (fun ν => ν) q.1, cycGood_cycNgood _ _⟩ : CycGoodSet I d β) :=
    Measurable.subtype_mk (hng.comp measurable_fst)
  have h2 : Measurable fun q : Measure (CycS I d β) × CycData I d =>
      ((⟨cycNgood (fun ν => ν) q.1, cycGood_cycNgood _ _⟩ : CycGoodSet I d β), q.2) :=
    h1.prodMk measurable_snd
  have h3 := (measurable_envFn (I := I) (d := d) (β := β) r).comp h2
  exact h3

theorem measurable_envWalk :
    Measurable fun q : Measure (CycS I d β) × CycData I d => envWalk q.1 q.2 := by
  classical
  refine measurable_pi_iff.2 fun r => ?_
  have hs : MeasurableSet {q : Measure (CycS I d β) × CycData I d | CycGood q.1} :=
    measurable_fst measurableSet_cycGood
  have hf := measurable_envFn_ngood (I := I) (d := d) (β := β) r
  have hg : Measurable fun q : Measure (CycS I d β) × CycData I d => q.2.start :=
    measurable_fst.comp (measurable_snd.comp measurable_snd)
  have : (fun q : Measure (CycS I d β) × CycData I d => envWalk q.1 q.2 r) =
      fun q => if CycGood q.1 then envFn (cycNgood (fun ν => ν) q.1) q.2 r else q.2.start := by
    funext q
    unfold envWalk
    by_cases h : CycGood q.1
    · simp [h, cycNgood]
    · simp [h]
  rw [this]
  exact Measurable.ite hs hf hg

theorem isPoissonPointProcess_envMeasure {Ω : Type*} [MeasurableSpace Ω] {Pr : Measure Ω}
    {N : Ω → Measure (CycS I d β)} (hN : IsPoissonPointProcess N (cycIntensity I d β) Pr)
    (δ : CycData I d) :
    IsPoissonPointProcess (fun ω => envMeasure (N ω) δ) (ringIntensity d β) Pr := by
  have h := CycSchemeEnv.isPoissonPointProcess_slice' hN δ.copy
  unfold envMeasure
  by_cases hf : δ.fwd = true
  · simpa [hf] using h
  · simp only [hf, Bool.false_eq_true, ite_false]
    exact h.of_map_eq ((measurable_reflectMeasure (d := d) (β := β)).comp h.measurable)
      (law_reflectMeasure h)

end ElboimSly.Cyclic

end
