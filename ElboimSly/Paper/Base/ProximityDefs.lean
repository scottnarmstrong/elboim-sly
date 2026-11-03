/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Base.HitSeq
public import ElboimSly.Paper.Base.Drivers
public import ElboimSly.Foundations.SRW.Lemma82E2
public import ElboimSly.Foundations.SRW.Lemma82C
public import Mathlib

/-!
# The proximity set of an independent walk: set-up

Proximity times of an independent walk (ES22 §8).

With `X₁ = drvX Ñ 0` and `X₂ = drvX Ñ 1`, the set `U = {s ∈ [0, T] : d(b + X₂(s), V) ≤ ρ}` with
`V = {a + X₁(s') : s' ∈ [0, L]}` is `baseProxSet`.  Because `V` is finite, `d(z, V) ≤ ρ` is the
statement `∃ v ∈ V, ‖z - v‖ ≤ ρ`.  This file collects the filtration and measurability facts used
in the proof of the probability bound.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Paper

open ElboimSly.SRW ElboimSly.Paper.Base

variable {d : ℕ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {Ñ : Ω → Measure ((Dir d × Fin 2) × ℝ)}

/-- Proximity times of an independent walk: the set `U = {s ∈ [0, T] : d(b + X₂(s), V) ≤ ρ}`,
where `V = {a + X₁(s') : s' ∈ [0, L]}`. -/
def baseProxSet (Ñ : Ω → Measure ((Dir d × Fin 2) × ℝ)) (a b : Fin d → ℤ) (T L : ℝ≥0) (ρ : ℝ)
    (ω : Ω) : Set ℝ :=
  {x | 0 ≤ x ∧ x ≤ T ∧ ∃ y : ℝ≥0, y ≤ L ∧ ‖b + drvX Ñ 1 ω x.toNNReal - (a + drvX Ñ 0 ω y)‖ ≤ ρ}

/-- The random set `K = {z : d(z, V) ≤ ρ}` of the stopping times `ζ_i`. -/
def proxK (Ñ : Ω → Measure ((Dir d × Fin 2) × ℝ)) (a : Fin d → ℤ) (L : ℝ≥0) (ρ : ℝ)
    (ω : Ω) : Set (Fin d → ℤ) :=
  {z | ∃ y : ℝ≥0, y ≤ L ∧ ‖z - (a + drvX Ñ 0 ω y)‖ ≤ ρ}

/-- The independent walk `b + X₂`. -/
noncomputable def proxY (Ñ : Ω → Measure ((Dir d × Fin 2) × ℝ)) (b : Fin d → ℤ) (ω : Ω)
    (t : ℝ≥0) : Fin d → ℤ := b + drvX Ñ 1 ω t

theorem one_sub_one_fin2 : (1 : Fin 2) - 1 = 0 := by decide

omit [MeasurableSpace Ω] in
theorem drvFil_one (Ñ : Ω → Measure ((Dir d × Fin 2) × ℝ)) (t : ℝ≥0) :
    drvFil Ñ 1 t = MeasurableSpace.comap (drvX Ñ 0) inferInstance ⊔ natFil (drvX Ñ 1) t := by
  unfold drvFil; rw [one_sub_one_fin2]

theorem min_sub_min_le (s s' L : ℝ≥0) (h : s ≤ s') : min s' L - min s L ≤ s' - s := by
  rw [tsub_le_iff_right]
  rcases le_total s L with h1 | h1
  · rcases le_total s' L with h2 | h2
    · rw [min_eq_left h1, min_eq_left h2]; exact (tsub_add_cancel_of_le h).ge
    · rw [min_eq_left h1, min_eq_right h2]
      exact h2.trans (tsub_add_cancel_of_le h).ge
  · rw [min_eq_right h1]
    exact (min_le_right _ _).trans le_add_self

section

omit [MeasurableSpace Ω] in
theorem measurable_drvX0_comap (s : ℝ≥0) :
    Measurable[drvFil Ñ 1 0] (fun ω => drvX Ñ 0 ω s) := by
  have h1 : Measurable[MeasurableSpace.comap (drvX Ñ 0) inferInstance]
      (fun ω => drvX Ñ 0 ω s) := (measurable_pi_apply s).comp (comap_measurable (drvX Ñ 0))
  rw [drvFil_one]
  exact h1.mono le_sup_left le_rfl

omit [MeasurableSpace Ω] in
theorem measurable_proxY (t : ℝ≥0) (b : Fin d → ℤ) :
    Measurable[drvFil Ñ 1 t] (fun ω => proxY Ñ b ω t) := by
  have h0 : Measurable[natFil (drvX Ñ 1) t] (fun ω => drvX Ñ 1 ω t) :=
    measurable_natFil (drvX Ñ 1) le_rfl
  have h1 : Measurable[drvFil Ñ 1 t] (fun ω => drvX Ñ 1 ω t) := by
    rw [drvFil_one]; exact h0.mono le_sup_right le_rfl
  let : MeasurableSpace Ω := drvFil Ñ 1 t
  exact measurable_add_discrete measurable_const h1

omit [MeasurableSpace Ω] in
theorem isStepPath_proxY (b : Fin d → ℤ) (ω : Ω) : IsStepPath (proxY Ñ b ω) := by
  have hs := (drivers_isDrivingPath (Ñ := Ñ) 1 ω).step
  refine ⟨fun s => ?_, fun T => ?_⟩
  · filter_upwards [hs.rc s] with u hu
    simp only [proxY, hu]
  · refine (hs.fin T).subset fun r hr => ?_
    obtain ⟨hr1, hr2⟩ := hr
    exact ⟨⟨hr1.1, fun hc => hr1.2 (hc.mono fun u hu => by simp only [proxY, hu])⟩, hr2⟩

end

end ElboimSly.Paper
