/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Base.ContactGamma2
public import ElboimSly.Foundations.SRW.FixedCounts
public import ElboimSly.Foundations.SRW.Counts
public import Mathlib

/-!
# The first jump of the scenario

Contacts are few (ii), "Probability of the scenario", the event `F`: the clocks
`Ñ` have exactly one point in `D_{2d} × (0, 1]`, with direction `(0, v₀)`.

* `prob_single_point`: `P(F) = e^{-4d}`.
* `single_point_path`: on `F ∩ Ḡ`, `X̄(q) ∈ {0, (0, v₀)}` for `q ≤ 1` and `X̄(1) = (0, v₀)`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Paper

open ElboimSly.Cyclic ElboimSly.Paper.Base ElboimSly.SRW

variable {d : ℕ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}

/-- The event `F`: all counts in `(0, 1]` vanish, except the one for `v₁`, which is `1`. -/
def singlePoint {D : ℕ} (N : Ω → Measure (Dir D × ℝ)) (v₁ : Dir D) : Set Ω :=
  ⋂ v : Dir D, (cntN N 1 v) ⁻¹' {if v = v₁ then 1 else 0}

theorem prob_single_point {D : ℕ} {N : Ω → Measure (Dir D × ℝ)}
    (hN : IsPoissonPointProcess N (clockIntensity (Dir D)) P) (v₁ : Dir D) :
    P (singlePoint N v₁) = ENNReal.ofReal (Real.exp (-(2 * D : ℕ))) := by
  have := hN.isProbabilityMeasure
  have hind := iIndepFun_cntN hN (1 : ℝ)
  have h1 := hind.measure_inter_preimage_eq_mul (Finset.univ : Finset (Dir D))
    (sets := fun v => ({if v = v₁ then 1 else 0} : Set ℕ)) (fun v _ => MeasurableSet.of_discrete)
  have e : singlePoint N v₁ = ⋂ v ∈ (Finset.univ : Finset (Dir D)),
      (cntN N 1 v) ⁻¹' {if v = v₁ then 1 else 0} := by
    ext ω; simp [singlePoint]
  rw [e, h1]
  have hv : ∀ v : Dir D, P ((cntN N 1 v) ⁻¹' {if v = v₁ then 1 else 0}) =
      ENNReal.ofReal (Real.exp (-1)) := by
    intro v
    rw [← Measure.map_apply (measurable_cntN hN 1 v) (MeasurableSet.of_discrete),
      map_cntN hN zero_le_one v, poissonMeasure_singleton]
    congr 1
    split_ifs <;> simp
  simp only [hv, Finset.prod_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
    Fintype.card_bool]
  rw [← ENNReal.ofReal_pow (Real.exp_pos _).le, ← Real.exp_nat_mul]
  congr 2
  push_cast; ring

theorem walk_single_point {D : ℕ} {ν : Measure (Dir D × ℝ)} (hν : ν ∈ goodSet D) (v₁ : Dir D)
    (h : ∀ v : Dir D, natOf (cnt ν v 1) = if v = v₁ then 1 else 0) :
    (∀ s : ℝ, s ≤ 1 → walk D ν s = 0 ∨ walk D ν s = v₁.vec) ∧ walk D ν 1 = v₁.vec := by
  classical
  have hc : ∀ v : Dir D, cnt ν v 1 = if v = v₁ then 1 else 0 := by
    intro v
    obtain ⟨n, hn⟩ := good_cnt hν v 1
    have : natOf (cnt ν v 1) = n := by rw [hn]; simp [natOf]
    rw [hn]
    have h2 := h v
    rw [this] at h2
    rw [h2]; split_ifs <;> simp
  have hmono : ∀ v (s : ℝ), s ≤ 1 → cnt ν v s ≤ cnt ν v 1 := fun v s hs =>
    measure_mono (prod_mono subset_rfl (Ioc_subset_Ioc_right hs))
  have hsum : ∀ s : ℝ, s ≤ 1 →
      walk D ν s = ((⌊(cnt ν v₁ s).toReal⌋₊ : ℕ) : ℤ) • v₁.vec := by
    intro s hs
    unfold walk
    rw [ite_eq_left hν, Finset.sum_eq_single v₁]
    · intro v _ hv
      have : cnt ν v s = 0 := by
        have := hmono v s hs
        rw [hc v, ite_eq_right hv] at this
        exact le_antisymm this bot_le
      rw [this]; simp
    · intro hn; exact absurd (Finset.mem_univ _) hn
  refine ⟨fun s hs => ?_, ?_⟩
  · rw [hsum s hs]
    have hle : ⌊(cnt ν v₁ s).toReal⌋₊ ≤ 1 := by
      have h1 : cnt ν v₁ s ≤ 1 := by
        have := hmono v₁ s hs
        rwa [hc v₁, ite_eq_left rfl] at this
      have h2 : (cnt ν v₁ s).toReal ≤ 1 := by
        simpa using ENNReal.toReal_mono ENNReal.one_ne_top h1
      exact (Nat.floor_le_floor h2).trans (by simp)
    interval_cases hk : ⌊(cnt ν v₁ s).toReal⌋₊
    · left; simp
    · right; simp
  · rw [hsum 1 le_rfl, hc v₁, ite_eq_left rfl]; simp

end ElboimSly.Paper
