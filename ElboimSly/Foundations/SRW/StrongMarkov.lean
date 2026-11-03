/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.SRW.Dyadic
public import Mathlib

/-!
# Strong Markov property

Strong Markov property; Hitting times and stopped positions (b).

The proof discretises the stopping time along dyadic times (`gset`), applies the fixed-time
Markov property on each slice, and passes to the limit on cylinder sets.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

namespace ElboimSly
namespace SRW

variable {d : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {Z : Ω → PathSpace d}
  {F : ℝ≥0 → MeasurableSpace Ω}

open Classical in
/-- The shifted process `θ_T Z`, with `θ_T Z ≡ 0` on `{T = ∞}`. -/
noncomputable def thetaAt (T : Ω → WithTop ℝ≥0) (Z : Ω → PathSpace d) (ω : Ω) : PathSpace d :=
  if T ω = ⊤ then 0 else theta (stopReal T ω) (Z ω)

theorem IsRegularPath.eventually_near {γ : PathSpace d} (hγ : IsRegularPath γ) {x : ℝ≥0}
    {s : ℕ → ℝ≥0} (h1 : ∀ m, x ≤ s m) (h2 : ∀ m, s m ≤ x + 1 / 2 ^ m) :
    ∀ᶠ m in atTop, γ (s m) = γ x := by
  obtain ⟨δ, hδ, h⟩ := hγ x
  have hlim : Tendsto (fun m : ℕ => x + 1 / (2 : ℝ≥0) ^ m) atTop (𝓝 x) := by
    have : Tendsto (fun m : ℕ => 1 / (2 : ℝ≥0) ^ m) atTop (𝓝 0) := by
      have := tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity : (0 : ℝ≥0) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ≥0) < 1)
      simpa [one_div, inv_pow] using this
    simpa using tendsto_const_nhds.add this
  have : ∀ᶠ m in atTop, x + 1 / (2 : ℝ≥0) ^ m < x + δ :=
    hlim.eventually (gt_mem_nhds (lt_add_of_pos_right x hδ))
  filter_upwards [this] with m hm
  exact h _ (h1 m) ((h2 m).trans_lt hm)

theorem measurable_thetaAt {f : Filtration ℝ≥0 mΩ} {T : Ω → WithTop ℝ≥0}
    (hT : IsStoppingTime f T) (hZm : ∀ s, Measurable fun ω => Z ω s)
    (hreg : ∀ ω, IsRegularPath (Z ω)) : Measurable (thetaAt T Z) := by
  refine measurable_pi_iff.2 fun s => ?_
  have hr := hT.measurable_stopReal
  have h1 : Measurable fun ω => Z ω (stopReal T ω) := measurable_eval_regular hZm hreg hr
  have h2 : Measurable fun ω => Z ω (stopReal T ω + s) :=
    measurable_eval_regular hZm hreg (hr.add_const s)
  have : (fun ω => thetaAt T Z ω s) = fun ω =>
      if T ω = ⊤ then (0 : Fin d → ℤ) else Z ω (stopReal T ω + s) - Z ω (stopReal T ω) := by
    funext ω
    unfold thetaAt theta
    by_cases h : T ω = ⊤ <;> simp [h, add_comm]
  rw [this]
  exact Measurable.ite hT.measurableSet_top measurable_const (h2.sub h1)

/-- Fixed-time Markov property on an admissible filtration. -/
theorem IsSRW.fixed_time (hZ : IsSRW P Z) (hF : IsAdmissible P Z F) (t : ℝ≥0) {B : Set Ω}
    (hB : MeasurableSet[F t] B) {Γ : Set (PathSpace d)} (hΓ : MeasurableSet Γ) :
    P (B ∩ {ω | theta t (Z ω) ∈ Γ}) = P B * P.map Z Γ := by
  have hind := ((Indep_iff _ _ _).1 (hF.indep t)) ((fun ω => theta t (Z ω)) ⁻¹' Γ) B
    ⟨Γ, hΓ, rfl⟩ hB
  have hmeas : Measurable fun ω => theta t (Z ω) := (measurable_theta t).comp hZ.1
  have hm : P ((fun ω => theta t (Z ω)) ⁻¹' Γ) = P.map Z Γ := by
    rw [← Measure.map_apply hmeas hΓ, hZ.map_theta t]
  rw [inter_comm, show {ω | theta t (Z ω) ∈ Γ} = (fun ω => theta t (Z ω)) ⁻¹' Γ from rfl, hind,
    hm, mul_comm]

end SRW
end ElboimSly
