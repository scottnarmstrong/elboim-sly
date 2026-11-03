/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Interchange.GoodAsProb
public import ElboimSly.Foundations.Interchange.RingSplit
public import ElboimSly.Foundations.PPP.Invariance
public import ElboimSly.Foundations.Interchange.SymmGood
public import Mathlib

/-!
# (G3) holds almost surely

Configurations are a.s. good (proof of (G3)).

The bound `K ^ n * (β/2)^n / n!` tends to `0`, so almost surely some `n` bounds the length of ring
paths from `y` in a given window.
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal Nat

namespace ElboimSly.Interchange

variable {d : ℕ} {β : ℝ} [Fact (0 < β)] {Ω : Type*} [MeasurableSpace Ω]
  {N : Ω → Measure (RingSpace d β)} {P : Measure Ω}

theorem pow_mul_volume_orderedSimplex_le (K : ℕ) (n : ℕ) (p q : ℝ) (hpq : p ≤ q) :
    (K : ℝ≥0∞) ^ n * volume (orderedSimplex n p q) ≤
      ENNReal.ofReal (((K : ℝ) * (q - p)) ^ n / n !) := by
  have hfac : (n ! : ℝ≥0∞) ≠ 0 := by exact_mod_cast (Nat.factorial_pos n).ne'
  have hfac' : (n ! : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have h1 : volume (orderedSimplex n p q) ≤ ENNReal.ofReal (q - p) ^ n / n ! :=
    (ENNReal.le_div_iff_mul_le (Or.inl hfac) (Or.inl hfac')).2
      (by rw [mul_comm]; exact factorial_mul_volume_orderedSimplex_le n p q)
  calc (K : ℝ≥0∞) ^ n * volume (orderedSimplex n p q)
      ≤ (K : ℝ≥0∞) ^ n * (ENNReal.ofReal (q - p) ^ n / n !) := by gcongr
    _ = ENNReal.ofReal (((K : ℝ) * (q - p)) ^ n / n !) := by
        have hq : (0 : ℝ) ≤ q - p := sub_nonneg.2 hpq
        rw [ENNReal.ofReal_div_of_pos (by exact_mod_cast Nat.factorial_pos n), mul_pow,
          ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by positivity),
          ENNReal.ofReal_pow hq, ENNReal.ofReal_natCast, ENNReal.ofReal_natCast, mul_div_assoc]

theorem tendsto_pow_mul_volume (K : ℕ) (p q : ℝ) (hpq : p ≤ q) :
    ∃ b : ℕ → ℝ≥0∞, Tendsto b atTop (𝓝 0) ∧
      ∀ n, (K : ℝ≥0∞) ^ n * volume (orderedSimplex n p q) ≤ b n := by
  refine ⟨fun n => ENNReal.ofReal (((K : ℝ) * (q - p)) ^ n / n !), ?_,
    fun n => pow_mul_volume_orderedSimplex_le K n p q hpq⟩
  have := ENNReal.tendsto_ofReal (FloorSemiring.tendsto_pow_div_factorial_atTop ((K : ℝ) * (q - p)))
  simpa using this

/-- Paths from `y` in a window have bounded length, almost surely. -/
theorem ae_exists_noPathFrom
    (h : IsPoissonPointProcess N (ringIntensity d β) P) (y : Fin d → ℤ) (j : ℤ) :
    ∀ᵐ ω ∂P, ∃ n, NoPathFrom (N ω) (ringWindow β j) y n := by
  have hβ : 0 < β := Fact.out
  have hpq : (j * β / 4 : ℝ) ≤ j * β / 4 + β / 2 := by linarith
  obtain ⟨b, hb, hbn⟩ := tendsto_pow_mul_volume (stepCount d) (j * β / 4) (j * β / 4 + β / 2) hpq
  rw [ae_iff]
  have hle : P {ω | ¬ ∃ n, NoPathFrom (N ω) (ringWindow β j) y n} ≤ 0 := by
    refine ge_of_tendsto' hb fun n => ?_
    refine le_trans (measure_mono ?_) ((measure_exists_ringPath_le h y
      (a := j * β / 4 - β / 4) (by linarith) (by linarith) n).trans (hbn n))
    intro ω hω hn
    exact hω ⟨n, hn⟩
  exact le_antisymm hle bot_le

omit [Fact (0 < β)] in
theorem NoPathTo.of_le {μ : Measure (RingSpace d β)} {J : Set ℝ} {y : Fin d → ℤ} {n n' : ℕ}
    (h : NoPathTo μ J y n) (hn : n ≤ n') : NoPathTo μ J y n' := by
  rintro ⟨v, t, hv, hp⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  have hs := hp.suffix k
  rw [Nat.add_sub_cancel] at hs
  exact h ⟨fun i => v (i + k), fun i => t (i + k), hv, hs⟩

omit [Fact (0 < β)] in
theorem noPathTo_of_noPathFrom_reflect {μ : Measure (RingSpace d β)} {J : Set ℝ}
    {y : Fin d → ℤ} {n : ℕ} (h : NoPathFrom (reflectMeasure β μ) {u | -u ∈ J} y n) :
    NoPathTo μ J y n := by
  rintro ⟨v, t, hv, hp⟩
  exact h ⟨fun i => v (n - i), fun i => -t (n - 1 - i), by simpa using hv, hp.reflect'⟩

theorem isPoissonPointProcess_reflect (h : IsPoissonPointProcess N (ringIntensity d β) P) :
    IsPoissonPointProcess (fun ω => reflectMeasure β (N ω)) (ringIntensity d β) P := by
  have hφ : Measurable (ringMapEquiv (Equiv.refl (Edge d))
      (MeasurableEquiv.neg (AddCircle β))) := MeasurableEquiv.measurable _
  have h1 := h.map_measure hφ
  have e : ⇑(ringMapEquiv (Equiv.refl (Edge d)) (MeasurableEquiv.neg (AddCircle β))) =
      Prod.map (Equiv.refl (Edge d)) (fun x : AddCircle β => -x) := rfl
  rw [e, map_ringIntensity_neg d β (Equiv.refl (Edge d))] at h1
  exact h1

theorem ae_exists_noPathTo (h : IsPoissonPointProcess N (ringIntensity d β) P)
    (y : Fin d → ℤ) (j : ℤ) :
    ∀ᵐ ω ∂P, ∃ n, NoPathTo (N ω) (ringWindow β j) y n := by
  filter_upwards [ae_exists_noPathFrom (isPoissonPointProcess_reflect h) y (-j - 2)] with ω hω
  obtain ⟨n, hn⟩ := hω
  refine ⟨n, noPathTo_of_noPathFrom_reflect ?_⟩
  rw [neg_ringWindow]
  exact hn

/-- (G3) holds almost surely. -/
theorem ae_goodG3 (h : IsPoissonPointProcess N (ringIntensity d β) P) :
    ∀ᵐ ω ∂P, GoodG3 (N ω) := by
  have hall : ∀ᵐ ω ∂P, ∀ (y : Fin d → ℤ) (j : ℤ),
      (∃ n, NoPathFrom (N ω) (ringWindow β j) y n) ∧ (∃ n, NoPathTo (N ω) (ringWindow β j) y n) :=
    ae_all_iff.2 fun y => ae_all_iff.2 fun j =>
      (ae_exists_noPathFrom h y j).and (ae_exists_noPathTo h y j)
  filter_upwards [hall] with ω hω y j
  obtain ⟨⟨n₁, h₁⟩, ⟨n₂, h₂⟩⟩ := hω y j
  refine ⟨max n₁ n₂, ?_, ?_⟩
  · exact noPathFrom_iff.1 (h₁.of_le (le_max_left _ _))
  · exact noPathTo_iff.1 (h₂.of_le (le_max_right _ _))

end ElboimSly.Interchange
