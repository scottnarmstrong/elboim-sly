/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.SRW.SrwLaw
public import Mathlib

/-!
# Evaluation of regular paths at variable times

Evaluation at variable times (a), hitting times and stopped positions.

For a process with regular paths, `ω ↦ Z ω (r ω)` is measurable for every measurable time `r`:
it is the eventually constant limit of the evaluations at the dyadic upper approximations
`dy m (r ω)`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

namespace ElboimSly
namespace SRW
/-- The dyadic upper approximation `2^{-m} ⌈2^m x⌉`. -/
noncomputable def dy (m : ℕ) (x : ℝ≥0) : ℝ≥0 := ((⌈x * (2 : ℝ≥0) ^ m⌉₊ : ℕ) : ℝ≥0) / 2 ^ m

theorem le_dy (m : ℕ) (x : ℝ≥0) : x ≤ dy m x := by
  unfold dy
  rw [le_div_iff₀ (by positivity)]
  have := Nat.le_ceil (x * (2 : ℝ≥0) ^ m)
  exact this

theorem dy_le (m : ℕ) (x : ℝ≥0) : dy m x ≤ x + 1 / 2 ^ m := by
  unfold dy
  rw [div_le_iff₀ (by positivity), add_mul, one_div, inv_mul_cancel₀ (by positivity)]
  have := (Nat.ceil_lt_add_one (a := x * (2 : ℝ≥0) ^ m) (by positivity)).le
  exact this

theorem tendsto_dy (x : ℝ≥0) : Tendsto (fun m => dy m x) atTop (𝓝 x) := by
  have h1 : Tendsto (fun m : ℕ => x + 1 / (2 : ℝ≥0) ^ m) atTop (𝓝 x) := by
    have : Tendsto (fun m : ℕ => 1 / (2 : ℝ≥0) ^ m) atTop (𝓝 0) := by
      have := tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity : (0 : ℝ≥0) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ≥0) < 1)
      simpa [one_div, inv_pow] using this
    simpa using tendsto_const_nhds.add this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h1
    (fun m => le_dy m x) (fun m => dy_le m x)

theorem IsRegularPath.eventually_dy {d : ℕ} {γ : PathSpace d} (hγ : IsRegularPath γ) (x : ℝ≥0) :
    ∀ᶠ m in atTop, γ (dy m x) = γ x := by
  obtain ⟨δ, hδ, h⟩ := hγ x
  have : ∀ᶠ m in atTop, dy m x < x + δ :=
    (tendsto_dy x).eventually (gt_mem_nhds (lt_add_of_pos_right x hδ))
  filter_upwards [this] with m hm
  exact h _ (le_dy m x) hm

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {Z : Ω → PathSpace d}

/-- Evaluation of a process with regular paths at a measurable random time is measurable. -/
theorem measurable_eval_regular (hZ : ∀ s, Measurable fun ω => Z ω s)
    (hreg : ∀ ω, IsRegularPath (Z ω)) {r : Ω → ℝ≥0} (hr : Measurable r) :
    Measurable fun ω => Z ω (r ω) := by
  have hm : ∀ m : ℕ, Measurable fun ω => Z ω (dy m (r ω)) := by
    intro m
    have hn : Measurable fun ω => ⌈r ω * (2 : ℝ≥0) ^ m⌉₊ :=
      Nat.measurable_ceil.comp (hr.mul_const _)
    have : (fun ω => Z ω (dy m (r ω))) = fun ω =>
        (fun p : Ω × ℕ => Z p.1 ((p.2 : ℝ≥0) / 2 ^ m)) (ω, ⌈r ω * (2 : ℝ≥0) ^ m⌉₊) := rfl
    rw [this]
    refine (measurable_from_prod_countable_left (f := fun p : Ω × ℕ =>
      Z p.1 ((p.2 : ℝ≥0) / 2 ^ m)) (fun k => (hZ _ : Measurable fun ω => Z ω ((k : ℝ≥0) / 2 ^ m))) : Measurable _).comp (measurable_id.prodMk hn)
  refine measurable_of_tendsto_metrizable hm (tendsto_pi_nhds.2 fun ω => ?_)
  refine tendsto_nhds_of_eventually_eq ?_
  exact (hreg ω).eventually_dy (r ω)

end SRW
end ElboimSly
