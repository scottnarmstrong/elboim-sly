/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycMultiGood
public import Mathlib

/-!
# Lifting the single-copy environment to the one-copy cyclic space

Markov property of the environment at walk stopping times (proof: "consider the plan `𝒫_W` with `I = {1}`").

The environment of Markov property of the environment at walk stopping times is a PPP on `S_β = Ed × 𝕋`. The multi-exploration theorem is
stated on `𝒮 = I × S_β`; we use `I = Unit` and the lift `liftU ν = (Prod.mk )_* ν`, whose inverse on
the image is the slice `cycSlice  = (Prod.mk )^*`.

* `liftU`, `cycSlice_liftU`, `measurable_liftU`, `cycGood_liftU_iff`, `liftU_restrict`;
* `cycIntensity_unit'`, `isPoissonPointProcess_liftU`;
* `markovNgood N`: `N` where good and `0` elsewhere ("given fixed values off `{N ∈ Good}`"), and
  `liftU_markovNgood`: `liftU ∘ markovNgood N = cycNgood (liftU ∘ N)`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

set_option linter.unusedSectionVars false

variable {d : ℕ} {β : ℝ} [Fact (0 < β)] {Ω : Type*} [MeasurableSpace Ω] {Pr : Measure Ω}

/-- The lift of a measure on `S_β` to `Unit × S_β`. -/
noncomputable def liftU (ν : Measure (RingSpace d β)) : Measure (Unit × RingSpace d β) :=
  ν.map (Prod.mk ())

theorem measurable_liftU :
    Measurable (liftU : Measure (RingSpace d β) → Measure (Unit × RingSpace d β)) :=
  measurable_map_measure measurable_prodMk_left

@[simp] theorem cycSlice_liftU (ν : Measure (RingSpace d β)) : cycSlice () (liftU ν) = ν := by
  unfold cycSlice liftU
  exact (measurableEmbedding_prodMk_left ()).comap_map ν

@[simp] theorem liftU_zero : liftU (0 : Measure (RingSpace d β)) = 0 := by
  unfold liftU; exact Measure.map_zero _

theorem liftU_injective : Function.Injective (liftU : Measure (RingSpace d β) → _) :=
  fun a b h => by simpa using congrArg (cycSlice ()) h

theorem cycGood_liftU_iff (ν : Measure (RingSpace d β)) : CycGood (liftU ν) ↔ Good ν := by
  unfold CycGood
  exact ⟨fun h => by simpa using h (), fun h ι => by cases ι; simpa using h⟩

theorem liftU_restrict (ν : Measure (RingSpace d β)) (A : Set (RingSpace d β)) :
    liftU (ν.restrict A) = (liftU ν).restrict ({()} ×ˢ A) := by
  unfold liftU
  rw [(measurableEmbedding_prodMk_left ()).restrict_map]
  have : Prod.mk () ⁻¹' ({()} ×ˢ A : Set (Unit × RingSpace d β)) = A := by
    ext x; simp
  rw [this]

theorem cycSlice_restrict_liftU (ν : Measure (RingSpace d β)) (A : Set (RingSpace d β)) :
    cycSlice () ((liftU ν).restrict ({()} ×ˢ A)) = ν.restrict A := by
  rw [← liftU_restrict, cycSlice_liftU]

theorem cycIntensity_unit' :
    cycIntensity Unit d β = (ringIntensity d β).map (Prod.mk ()) := by
  unfold cycIntensity
  have : (Measure.count : Measure Unit) = Measure.dirac () := by
    ext s hs
    by_cases h : () ∈ s
    · have : s = univ := by ext x; simp [h]
      subst this; simp
    · have : s = ∅ := by ext x; simp [h]
      subst this; simp
  rw [this, Measure.dirac_prod]

/-- The lift of a PPP is a PPP on the one-copy cyclic space. -/
theorem isPoissonPointProcess_liftU {N : Ω → Measure (RingSpace d β)}
    (hN : IsPoissonPointProcess N (ringIntensity d β) Pr) :
    IsPoissonPointProcess (fun ω => liftU (N ω)) (cycIntensity Unit d β) Pr := by
  rw [cycIntensity_unit']
  exact hN.map_measure measurable_prodMk_left

open scoped Classical in
/-- `N` where it is good, and `0` elsewhere. -/
noncomputable def markovNgood (N : Ω → Measure (RingSpace d β)) (ω : Ω) : Measure (RingSpace d β) :=
  if Good (N ω) then N ω else 0

theorem good_markovNgood (N : Ω → Measure (RingSpace d β)) (ω : Ω) : Good (markovNgood N ω) := by
  unfold markovNgood
  split_ifs with h
  · exact h
  · exact good_zero

theorem measurable_markovNgood {N : Ω → Measure (RingSpace d β)} (hN : Measurable N) :
    Measurable (markovNgood N) := by
  classical
  exact Measurable.ite (hN measurableSet_good) hN measurable_const

theorem liftU_markovNgood (N : Ω → Measure (RingSpace d β)) (ω : Ω) :
    liftU (markovNgood N ω) = cycNgood (fun ω => liftU (N ω)) ω := by
  unfold markovNgood cycNgood
  by_cases h : Good (N ω)
  · simp [h, cycGood_liftU_iff]
  · simp [h, cycGood_liftU_iff]

end ElboimSly.Cyclic

end
