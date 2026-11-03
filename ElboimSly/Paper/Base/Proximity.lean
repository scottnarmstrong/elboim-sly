/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Base.ProximityDefs
public import Mathlib

/-!
# Proximity times of an independent walk

Proximity times of an independent walk (ES22 §8).

Let `d ≥ 5`, `n ≥ max(n_C(d), n_2(d))`, `t₀ ∈ (1, 4]`, `T = 2 t'_n = lem82T n t₀`,
`L ∈ [0, T]`, `V = {a + X₁(s) : s ∈ [0, L]}` and
`U = {s ∈ [0, T] : d(b + X₂(s), V) ≤ 1.9^{n+1}}`.  Then
`P(|U| > n⁴ 3.89ⁿ) ≤ e^{-n⁴} + 2^{-n⁴}`.

* `es8_proximity`: the probability bound.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Paper

open ElboimSly.SRW ElboimSly.Paper.Base

variable {d : ℕ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {Ñ : Ω → Measure ((Dir d × Fin 2) × ℝ)}

omit [MeasurableSpace Ω] in
/-- The covering step: on `{ζ_N = ∞}` the proximity set is covered by `N` intervals of length
`3.89ⁿ`, so its measure is at most `N 3.89ⁿ`. -/
theorem volume_proxSet_le (b a : Fin d → ℤ) (T L : ℝ≥0) (ρ : ℝ) (hh : ℝ≥0) (N : ℕ) (ω : Ω)
    (hN : hitSeq (proxY Ñ b) (proxK Ñ a L ρ) hh N ω = ⊤) :
    (volume (baseProxSet Ñ a b T L ρ ω)).toReal ≤ N * hh := by
  have hsub : baseProxSet Ñ a b T L ρ ω ⊆ ⋃ i ∈ Finset.range N,
      Ico (stopReal (hitSeq (proxY Ñ b) (proxK Ñ a L ρ) hh i) ω : ℝ)
        (stopReal (hitSeq (proxY Ñ b) (proxK Ñ a L ρ) hh i) ω + hh) := by
    intro x hx
    obtain ⟨hx0, -, y, hyL, hy⟩ := hx
    have hmem : proxY Ñ b ω x.toNNReal ∈ proxK Ñ a L ρ ω := ⟨y, hyL, hy⟩
    obtain ⟨i, hi, -, h1, h2⟩ := exists_mem_hitSeq_Ico hN hmem
    simp only [mem_iUnion, Finset.mem_range]
    refine ⟨i, hi, ?_, ?_⟩
    · have := (NNReal.coe_le_coe.2 h1)
      rwa [Real.coe_toNNReal _ hx0] at this
    · have := (NNReal.coe_lt_coe.2 h2)
      rw [Real.coe_toNNReal _ hx0] at this
      simpa using this
  have hvol : volume (baseProxSet Ñ a b T L ρ ω) ≤ N * ENNReal.ofReal hh := by
    calc volume (baseProxSet Ñ a b T L ρ ω) ≤ volume (⋃ i ∈ Finset.range N,
        Ico (stopReal (hitSeq (proxY Ñ b) (proxK Ñ a L ρ) hh i) ω : ℝ)
          (stopReal (hitSeq (proxY Ñ b) (proxK Ñ a L ρ) hh i) ω + hh)) := measure_mono hsub
      _ ≤ ∑ i ∈ Finset.range N, volume (Ico (stopReal (hitSeq (proxY Ñ b)
          (proxK Ñ a L ρ) hh i) ω : ℝ) (stopReal (hitSeq (proxY Ñ b)
          (proxK Ñ a L ρ) hh i) ω + hh)) := measure_biUnion_finset_le _ _
      _ = ∑ _i ∈ Finset.range N, ENNReal.ofReal hh := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Real.volume_Ico]; congr 1; ring
      _ = N * ENNReal.ofReal hh := by simp
  have hfin : (N : ℝ≥0∞) * ENNReal.ofReal hh ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.natCast_ne_top N) ENNReal.ofReal_ne_top
  calc (volume (baseProxSet Ñ a b T L ρ ω)).toReal ≤ ((N : ℝ≥0∞) * ENNReal.ofReal hh).toReal :=
        ENNReal.toReal_mono hfin hvol
    _ = N * hh := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_ofReal hh.coe_nonneg]


theorem measurableSet_exists_Icc_gen {Ω' : Type*} {m : MeasurableSpace Ω'}
    {Z : Ω' → PathSpace d} (hZm : ∀ s, Measurable[m] fun ω => Z ω s)
    (hreg : ∀ ω, IsRegularPath (Z ω)) (K : Set (Fin d → ℤ)) (L : ℝ≥0) :
    MeasurableSet[m] {ω | ∃ s, 0 ≤ s ∧ s ≤ L ∧ Z ω s ∈ K} :=
  measurableSet_exists_Icc hZm hreg K bot_le

theorem measurable_shiftStop_gen {Ω' : Type*} {m : MeasurableSpace Ω'}
    {Z : Ω' → PathSpace d} (hZm : ∀ s, Measurable[m] fun ω => Z ω s) (a : Fin d → ℤ) (L : ℝ≥0) :
    Measurable[m] fun ω s => a + Z ω (min s L) :=
  measurable_pi_iff.2 fun _s => measurable_add_discrete measurable_const (hZm _)

section

variable (h : IsPoissonPointProcess Ñ (clockIntensity (Dir d × Fin 2)) P)
include h

theorem measurableSet_proxK_mem (a : Fin d → ℤ) (L : ℝ≥0) (ρ : ℝ) (z : Fin d → ℤ) :
    MeasurableSet[drvFil Ñ 1 0] {ω | z ∈ proxK Ñ a L ρ ω} := by
  have hreg : ∀ ω, IsRegularPath (drvX Ñ 0 ω) := fun ω => (drivers_isSRW h 0).2.1 ω
  have := measurableSet_exists_Icc_gen (m := drvFil Ñ 1 0) (measurable_drvX0_comap) hreg
    {w : Fin d → ℤ | ‖z - (a + w)‖ ≤ ρ} L
  convert this using 1
  ext ω
  simp only [mem_ofPred_eq, proxK, zero_le, true_and]

end

end ElboimSly.Paper
