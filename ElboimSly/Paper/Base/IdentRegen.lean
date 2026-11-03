/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Base.IdentLaw
public import Mathlib

/-!
# Regular events of the regenerated walk below `β`

* `regenPath`: the regenerated walk of the copies of `N` as a path.
* `regenPath_prob_eq_srw`: a regular `T`-local event (`T ≤ β`) has the same probability for the
  regenerated walk as for any SRW.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Paper

open ElboimSly.SRW ElboimSly.Cyclic ElboimSly.Interchange

variable {d : ℕ} {β : ℝ} [Fact (0 < β)]

/-- The regenerated walk of the copies of an environment, as a path on `[0, ∞)`. -/
noncomputable def regenPath (N : Measure (ℕ × RingSpace d β)) : PathSpace d :=
  fun s => regenWalk (fun k => copyEnv N k) (s : ℝ)

theorem ae_good_copyEnv {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {N : Ω → Measure (ℕ × RingSpace d β)}
    (hN : IsPoissonPointProcess N ((Measure.count : Measure ℕ).prod (ringIntensity d β)) P)
    (k : ℕ) : ∀ᵐ ω ∂P, Good (copyEnv (N ω) k) :=
  ae_good (Roots.isPoissonPointProcess_copyEnv hN k)

/-- Below `β`, the regenerated walk is the cyclic walk of the first copy. -/
theorem stopPath_regenPath {N : Measure (ℕ × RingSpace d β)} (h0 : Good (copyEnv N 0))
    (h1 : Good (copyEnv N 1)) {T : ℝ≥0} (hT : (T : ℝ) ≤ β) :
    stopPath T (regenPath N) = stopPath T (cycPath (copyEnv N 0)) := by
  funext s
  exact regenWalk_eq_cycPath h0 h1 ((NNReal.coe_le_coe.2 (min_le_right s T)).trans hT)

/-- **identification of the regenerated walk below β (b)**, event form for the regenerated walk. -/
theorem regenPath_prob_eq_srw {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'} {N : Ω → Measure (ℕ × RingSpace d β)}
    (hN : IsPoissonPointProcess N ((Measure.count : Measure ℕ).prod (ringIntensity d β)) P)
    {T : ℝ≥0} (hT : (T : ℝ) ≤ β) {Γ : Set (PathSpace d)} (hΓ : IsRegSet Γ)
    (hloc : ∀ γ, γ ∈ Γ ↔ stopPath T γ ∈ Γ) {Z' : Ω' → PathSpace d} (hZ' : IsSRW P' Z') :
    P {ω | regenPath (N ω) ∈ Γ} = P' {ω | Z' ω ∈ Γ} := by
  rw [← cycPath_prob_eq_srw (Roots.isPoissonPointProcess_copyEnv hN 0) hT hΓ hloc hZ']
  refine measure_congr ?_
  filter_upwards [ae_good_copyEnv hN 0, ae_good_copyEnv hN 1] with ω h0 h1
  have := stopPath_regenPath h0 h1 hT
  have e : (regenPath (N ω) ∈ Γ) = (cycPath (copyEnv (N ω) 0) ∈ Γ) := by
    rw [eq_iff_iff, hloc (regenPath (N ω)), hloc (cycPath (copyEnv (N ω) 0)), this]
  simpa using congrArg (fun p : Prop => p) e

/-- (H2) at the base. -/
theorem base_H2 {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {N : Ω → Measure (ℕ × RingSpace d β)}
    (hN : IsPoissonPointProcess N ((Measure.count : Measure ℕ).prod (ringIntensity d β)) P)
    {t : ℝ} (ht1 : 1 ≤ t) (htβ : t ≤ β) (u : Fin d → ℤ) :
    P {ω | regenWalk (fun k => copyEnv (N ω) k) t = u} ≤
      ENNReal.ofReal (t ^ (-(d : ℝ) / 2 + 1 / 10)) := by
  obtain ⟨Ω', mΩ', P', Z', hZ'⟩ := exists_srw d
  set T : ℝ≥0 := t.toNNReal with hT
  have hTt : (T : ℝ) = t := Real.coe_toNNReal _ (by linarith)
  have hmeas : MeasurableSet {γ : PathSpace d | γ T = u} :=
    (show MeasurableSet ((fun γ : PathSpace d => γ T) ⁻¹' {u}) from
      (measurable_pi_apply T) (MeasurableSet.of_discrete))
  have key := regenPath_prob_eq_srw (T := T) hN (hTt.le.trans htβ)
    (Γ := {γ : PathSpace d | γ T = u}) ⟨_, hmeas, fun _ _ => Iff.rfl⟩
    (fun γ => by simp [SRW.stopPath]) hZ'
  have e : {ω | regenWalk (fun k => copyEnv (N ω) k) t = u} =
      {ω | regenPath (N ω) ∈ {γ : PathSpace d | γ T = u}} := by
    ext ω; simp [regenPath, hTt]
  rw [e, key]
  have h := (hZ'.prob_eq_le_H2 (t := T) (by rw [hTt]; exact ht1) u)
  rw [hTt] at h
  exact h.1.trans h.2

end ElboimSly.Paper

end
