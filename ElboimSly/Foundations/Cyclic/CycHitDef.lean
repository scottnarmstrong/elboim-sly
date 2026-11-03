/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycMarkov
public import ElboimSly.Foundations.Cyclic.CycHitCov
public import ElboimSly.Foundations.Cyclic.CycHitFreeze
public import ElboimSly.Foundations.Cyclic.CycHitNull
public import ElboimSly.Foundations.Cyclic.CycMultiCond
public import ElboimSly.Foundations.SRW.Stopping
public import Mathlib

/-!
# ES22 Lemma 2.1: the environment `M` after the stopping time

ES22 Lemma 2.1, Step 1. With `Ñ = N|_{S_β∖ℛ_T} + N'|_{ℛ_T}` and
`Z = (W(T), T)`, the environment `M = (φ_Z)_* Ñ` on `{T < ∞}` and `M = N'` on `{T = ∞}`.
For measurability, `N`, `N'` are replaced by `τ(N)`, `τ(N')` (`tau`), which agree almost surely.

* `walkMap ν = (s ↦ W^ν_{0,0}(s))` for `ν` good (and `0` otherwise), a measurable map into
  `(ℤᵈ)^{[0,∞)}`;
* `hitZ`, `hitYtil`, `hitM`: `Z`, `τ(Ñ)`, `M`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

set_option linter.unusedSectionVars false

variable {d : ℕ} {β : ℝ} [Fact (0 < β)]

open scoped Classical in
/-- The walk of a configuration, as a function on `ℝ≥0` (junk-free: `0` replaces non-good ones). -/
noncomputable def walkMap (ν : Measure (RingSpace d β)) : ℝ≥0 → Fin d → ℤ :=
  fun s => ElboimSly.cycWalk (if Good ν then ν else 0) 0 0 (s : ℝ)

theorem measurable_walkMap :
    Measurable (walkMap : Measure (RingSpace d β) → ℝ≥0 → Fin d → ℤ) := by
  classical
  refine measurable_pi_iff.2 fun s => ?_
  have h1 : Measurable fun ν : Measure (RingSpace d β) =>
      (⟨if Good ν then ν else 0, by split_ifs with h; exacts [h, good_zero]⟩ : GoodSet d β) :=
    Measurable.subtype_mk (Measurable.ite measurableSet_good measurable_id measurable_const)
  exact (measurable_cycWalk 0 0 (NNReal.coe_nonneg s)).comp h1

variable {Ω : Type*} [MeasurableSpace Ω]

/-- `Z = (W(T), T)` (junk `(W(0), 0)` on `{T = ∞}`). -/
noncomputable def hitZ (N : Ω → Measure (RingSpace d β)) (T : Ω → WithTop ℝ≥0) (ω : Ω) :
    (Fin d → ℤ) × ℝ :=
  (markovW N ω (ElboimSly.SRW.stopReal T ω), ((ElboimSly.SRW.stopReal T ω : ℝ≥0) : ℝ))

/-- `τ(Ñ)` for `Ñ = N|_{S∖ℛ_T} + N'|_{ℛ_T}`. -/
noncomputable def hitYtil (N N' : Ω → Measure (RingSpace d β)) (T : Ω → WithTop ℝ≥0) (ω : Ω) :
    Measure (RingSpace d β) :=
  tildeMeasure (fun ω => tau (ringIntensity d β) (N ω)) (fun ω => tau (ringIntensity d β) (N' ω))
    (markovRegion N T) ω

open scoped Classical in
/-- The environment `M` after the stopping time. -/
noncomputable def hitM (N N' : Ω → Measure (RingSpace d β)) (T : Ω → WithTop ℝ≥0) (ω : Ω) :
    Measure (RingSpace d β) :=
  if T ω ≠ ⊤ then hitShift (hitZ N T ω) (hitYtil N N' T ω) else N' ω

end ElboimSly.Cyclic

end
