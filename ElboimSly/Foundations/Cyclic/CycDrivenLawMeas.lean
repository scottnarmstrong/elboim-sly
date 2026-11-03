/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycDrivenLawRegion
public import ElboimSly.Foundations.Cyclic.DrivenMeas
public import ElboimSly.Foundations.Cyclic.CycEnvMeas
public import ElboimSly.Foundations.Cyclic.CycTruncMeas
public import Mathlib

/-!
# Measurable representatives

Driven and environment walks agree in law; Well-definedness and measurability of the driven construction (b), measurability.

* `measurable_srwPath`: `Ñ ↦ X_j(Ñ)` is a measurable map into `CPath`;
* `measurable_drivenPair`: `Ñ ↦ (t_reg^{X_j}, w^{X_j}(· ∧ t_reg^{X_j}))` is measurable;
* `CycPlan.envFinalOr`: the environment final record on the good environments and a fixed record
  elsewhere, a measurable map on all environments.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

open SRW

variable {d : ℕ}

/-- The pair `(t_reg^x, w^x(· ∧ t_reg^x))` of a driving path. -/
noncomputable def drivenPair (b : ℝ≥0) (x : ℝ≥0 → Fin d → ℤ) : ℝ≥0∞ × (ℝ≥0 → Fin d → ℤ) :=
  (drivenTreg b x, fun s => drivenStopped b x s)

/-- The pair `(t_reg, W(· ∧ t_reg))` of an environment. -/
noncomputable def cycPair {β : ℝ} [Fact (0 < β)] (ν : Measure (RingSpace d β)) :
    ℝ≥0∞ × (ℝ≥0 → Fin d → ℤ) :=
  (ElboimSly.cycTreg ν, fun s => cycStopped ν s)

section Driven

variable {J : Type} [MeasurableSpace J] [MeasurableSingletonClass J] [Countable J]

theorem measurable_srwPath (j : J) :
    Measurable fun Ñ : Measure ((Dir d × J) × ℝ) => (srwPath Ñ j).1 := by
  refine (CPath.measurable_iff _).2 ⟨measurable_const, fun s => ?_⟩
  exact (measurable_walk d (s : ℝ)).comp
    (measurable_relabel {x : Dir d × J | x.2 = j}
      (measurableSet_eq_fun measurable_snd measurable_const) Prod.fst)

theorem measurable_drivenPair {b : ℝ≥0} (hb : 0 < b) (j : J) :
    Measurable fun Ñ : Measure ((Dir d × J) × ℝ) => drivenPair b (srwPath Ñ j).1.fn := by
  refine ((measurable_drivenTreg hb).comp (measurable_srwPath j)).prodMk
    (measurable_pi_iff.2 fun s => ?_)
  exact (measurable_drivenStopped hb s).comp (measurable_srwPath j)

end Driven

section Env

variable {I : Type*} [MeasurableSpace I] [MeasurableSingletonClass I] [Countable I]
  {β : ℝ} [Fact (0 < β)]

open scoped Classical in
/-- The environment final record on the good environments, and `r₀` elsewhere. -/
noncomputable def CycPlan.envFinalOr (P : CycPlan I d β) (r₀ : CycRec I d)
    (ν : Measure (I × RingSpace d β)) : CycRec I d :=
  if ν ∈ {ν : Measure (I × RingSpace d β) | CycGood ν} then P.envFinal ν else r₀

omit [MeasurableSingletonClass I] [Countable I] [Fact (0 < β)] in
theorem CycPlan.envFinalOr_of_good (P : CycPlan I d β) (r₀ : CycRec I d)
    {ν : Measure (I × RingSpace d β)} (h : CycGood ν) : P.envFinalOr r₀ ν = P.envFinal ν := by
  unfold CycPlan.envFinalOr
  exact ite_eq_left (show ν ∈ {ν : Measure (I × RingSpace d β) | CycGood ν} from h)

theorem CycPlan.measurable_envFinalOr (P : CycPlan I d β) (r₀ : CycRec I d) :
    Measurable (P.envFinalOr r₀) := by
  classical
  have h : Measurable fun ν : CycGoodSet I d β => P.envFinal ν.1 := P.measurable_envFinal
  have := Measurable.dite (s := {ν : Measure (I × RingSpace d β) | CycGood ν})
    (f := fun ν : ↥{ν : Measure (I × RingSpace d β) | CycGood ν} => P.envFinal ν.1)
    (g := fun _ => r₀) h measurable_const measurableSet_cycGood
  convert this using 2 with ν
  unfold CycPlan.envFinalOr
  split_ifs <;> rfl

end Env

end ElboimSly.Cyclic

end
