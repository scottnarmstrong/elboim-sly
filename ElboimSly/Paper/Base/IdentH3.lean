/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Base.IdentRegen
public import ElboimSly.Foundations.SRW.BaseBounds
public import ElboimSly.Foundations.SRW.Lemma82B
public import ElboimSly.Frozen.Defs.IndH3
public import ElboimSly.Frozen.Defs.IndH2
public import Mathlib

/-!
# (H2) and (H3) at the base

(8.1)--(8.3) and (H2)--(H4) at the base (d), (e) and (8.1).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ElboimSly.Paper

open ElboimSly.SRW ElboimSly.Cyclic ElboimSly.Interchange

variable {d : ℕ} {β : ℝ} [Fact (0 < β)]

/-- For integer-valued sizes, a lower bound on a supremum is attained. -/
theorem ofReal_le_iSup_iff_nat {ι : Type*} [Nonempty ι] (g : ι → ℕ) (R : ℝ) :
    ENNReal.ofReal R ≤ ⨆ i, ENNReal.ofReal (g i : ℝ) ↔ ∃ i, R ≤ (g i : ℝ) := by
  constructor
  · intro h
    by_contra hcon
    push Not at hcon
    obtain ⟨i0⟩ := ‹Nonempty ι›
    have hR : 0 < R := lt_of_le_of_lt (Nat.cast_nonneg _) (hcon i0)
    have hm : ∀ i, g i ≤ ⌈R⌉₊ - 1 := by
      intro i
      have : g i < ⌈R⌉₊ := Nat.lt_ceil.2 (hcon i)
      omega
    have h1 : (⨆ i, ENNReal.ofReal (g i : ℝ)) ≤ ENNReal.ofReal ((⌈R⌉₊ - 1 : ℕ) : ℝ) :=
      iSup_le fun i => ENNReal.ofReal_le_ofReal (by exact_mod_cast hm i)
    have hc : 1 ≤ ⌈R⌉₊ := Nat.one_le_iff_ne_zero.2 (Nat.ceil_pos.2 hR).ne'
    have h2 : ((⌈R⌉₊ - 1 : ℕ) : ℝ) < R := by
      rw [Nat.cast_sub hc]
      have := Nat.ceil_lt_add_one hR.le
      simp; linarith
    have := (ENNReal.ofReal_lt_ofReal_iff hR).2 h2
    exact absurd (h.trans h1) (not_le.2 this)
  · rintro ⟨i, hi⟩
    exact (ENNReal.ofReal_le_ofReal hi).trans (le_iSup (fun i => ENNReal.ofReal (g i : ℝ)) i)

/-- (H3)/(8.1) at the base, as a statement about the path of the regenerated walk. -/
theorem base_H3_event {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {N : Ω → Measure (ℕ × RingSpace d β)}
    (hN : IsPoissonPointProcess N ((Measure.count : Measure ℕ).prod (ringIntensity d β)) P)
    [NeZero d] {n : ℕ} (hn16 : 16 ≤ n) (hd : Real.log (4 * d) ≤ n) {t₀ : ℝ} (ht1 : 1 < t₀)
    (htβ : 4 ^ n * t₀ ≤ β) :
    P {ω | ENNReal.ofReal ((n : ℝ) ^ 2 * Real.sqrt (4 ^ n * t₀)) ≤
        ⨆ s : Set.Icc (0 : ℝ) (4 ^ n * t₀),
          ENNReal.ofReal ‖regenWalk (fun k => copyEnv (N ω) k) (s : ℝ)‖} ≤
      ENNReal.ofReal (Real.exp (-((n : ℝ) ^ 3))) := by
  obtain ⟨Ω', mΩ', P', Z', hZ'⟩ := exists_srw d
  have := hZ'.isProbabilityMeasure
  set t0 : ℝ≥0 := t₀.toNNReal with ht0
  have ht0r : (t0 : ℝ) = t₀ := Real.coe_toNNReal _ (by linarith)
  have ht01 : 1 < t0 := by rw [← NNReal.coe_lt_coe]; simpa [ht0r] using ht1
  set T : ℝ≥0 := 4 ^ n * t0 with hT
  have hTr : (T : ℝ) = 4 ^ n * t₀ := by simp [hT, ht0r]
  set R : ℝ := (n : ℝ) ^ 2 * Real.sqrt ((T : ℝ≥0) : ℝ) with hR
  obtain ⟨V, hVm, hV⟩ := isRegSet_exists_le (d := d) {z : Fin d → ℤ | R ≤ ‖z‖} T
  have hreg : IsRegSet {γ : PathSpace d | ∃ s : ℝ≥0, s ≤ T ∧ γ s ∈ {z : Fin d → ℤ | R ≤ ‖z‖}} :=
    ⟨V, hVm, hV⟩
  have key := regenPath_prob_eq_srw (T := T) hN (by rw [hTr]; exact htβ) hreg
    (fun γ => by
      constructor
      · rintro ⟨s, hs, h⟩; exact ⟨s, hs, by simpa [SRW.stopPath, min_eq_left hs] using h⟩
      · rintro ⟨s, hs, h⟩; exact ⟨s, hs, by simpa [SRW.stopPath, min_eq_left hs] using h⟩) hZ'
  have e : {ω | ENNReal.ofReal ((n : ℝ) ^ 2 * Real.sqrt (4 ^ n * t₀)) ≤
        ⨆ s : Set.Icc (0 : ℝ) (4 ^ n * t₀),
          ENNReal.ofReal ‖regenWalk (fun k => copyEnv (N ω) k) (s : ℝ)‖} =
      {ω | regenPath (N ω) ∈ {γ : PathSpace d | ∃ s : ℝ≥0, s ≤ T ∧ γ s ∈
        {z : Fin d → ℤ | R ≤ ‖z‖}}} := by
    ext ω
    simp only [Set.mem_ofPred_eq, mem_ofPred_eq]
    have hRe : (n : ℝ) ^ 2 * Real.sqrt (4 ^ n * t₀) = R := by rw [hR, hTr]
    rw [hRe]
    have : Nonempty (Set.Icc (0 : ℝ) (4 ^ n * t₀)) :=
      ⟨⟨0, le_rfl, by positivity⟩⟩
    have := ofReal_le_iSup_iff_nat (ι := Set.Icc (0 : ℝ) (4 ^ n * t₀))
      (fun s => SRW.nrm (regenWalk (fun k => copyEnv (N ω) k) (s : ℝ))) R
    simp only [← norm_eq_nrm] at this
    rw [this]
    constructor
    · rintro ⟨⟨s, hs0, hs1⟩, h⟩
      refine ⟨s.toNNReal, ?_, ?_⟩
      · rw [← NNReal.coe_le_coe, hTr, Real.coe_toNNReal _ hs0]; exact hs1
      · simpa [regenPath, Real.coe_toNNReal _ hs0] using h
    · rintro ⟨s, hs, h⟩
      refine ⟨⟨(s : ℝ), s.2, by rw [← hTr]; exact_mod_cast hs⟩, ?_⟩
      simpa [regenPath] using h
  rw [e, key]
  have hb := hZ'.base_far_tail hn16 ht01 hd
  have hset : {ω | ∃ s : ℝ≥0, s ≤ T ∧ R ≤ ‖Z' ω s‖} =
      {ω | ∃ s, s ≤ 4 ^ n * t0 ∧ (n : ℝ) ^ 2 * √((4 ^ n * t0 : ℝ≥0) : ℝ) ≤ ‖Z' ω s‖} := rfl
  have : P' {ω | Z' ω ∈ {γ : PathSpace d | ∃ s : ℝ≥0, s ≤ T ∧ γ s ∈
      {z : Fin d → ℤ | R ≤ ‖z‖}}} = P' {ω | ∃ s : ℝ≥0, s ≤ T ∧ R ≤ ‖Z' ω s‖} := rfl
  rw [this, hset]
  rw [← ENNReal.ofReal_toReal (measure_ne_top P' _)]
  exact ENNReal.ofReal_le_ofReal hb

end ElboimSly.Paper

end
