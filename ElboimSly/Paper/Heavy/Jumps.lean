/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Heavy.JumpLaw
public import ElboimSly.Paper.Heavy.MeasJump
public import ElboimSly.Paper.Heavy.FastDisplacement
public import ElboimSly.Paper.Heavy.Thresholds
public import Mathlib

/-!
# Fast jumping is unlikely (first piece)

Fast jumping is unlikely (supplement), Steps 2-3.

For `β ≥ 2`, `L ≥ 1` and `t ≥ 1`, the first piece `W = W^ν_{0,0}` of a Poisson environment
satisfies `P(τ_jump(W; L) ≤ t) ≤ C_J t² e^{-L/2}` (`pathTjump_first_prob`), with
`C_J = 4 e^{4d(e-1)}`.  Since `τ_jump ≤ τ_fast` for cyclic paths, the same holds for `τ_fast`
(`pathTfast_first_prob`).  The events `≤ min(t_n, t_reg)` used in mathbbP(𝒢(i))ge1-e^-cn^3 are subevents
(`pathTjumpCube_first_prob`, `pathTfastCube_first_prob`).
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped NNReal ENNReal

namespace ElboimSly.Paper.Heavy

open ElboimSly ElboimSly.Paper ElboimSly.Cyclic ElboimSly.SRW ElboimSly.Interchange

variable {d : ℕ} {β : ℝ} [Fact (0 < β)]

/-- The unit window `(u - 1, u]` is covered by `(m, m + 2]` with `m = ⌊u⌋₊ - 1`. -/
theorem cycJumpCount_window_le {w : ℝ → Fin d → ℤ} (hw : IsCyclicPath w) {u : ℝ} (hu : 0 < u) :
    cycJumpCount w (u - 1) u ≤ cycJumpCount w ((⌊u⌋₊ - 1 : ℕ) : ℝ) (((⌊u⌋₊ - 1 : ℕ) : ℝ) + 2) := by
  unfold cycJumpCount
  refine Set.ncard_le_ncard (fun r hr => ?_) ((hw.fin _).subset fun x hx => ⟨hx.1, hx.2.2⟩)
  obtain ⟨hr0, hr1, hr2⟩ := hr
  have hr' : 0 < r := hr0.1
  have hf : (⌊u⌋₊ : ℝ) ≤ u := Nat.floor_le hu.le
  have hf2 : u < (⌊u⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one u
  refine ⟨hr0, ?_, ?_⟩
  · rcases Nat.eq_zero_or_pos ⌊u⌋₊ with h | h
    · rw [h]; simpa using hr'
    · rw [Nat.cast_sub h]
      simp only [Nat.cast_one]
      linarith
  · have : (⌊u⌋₊ : ℝ) ≤ ((⌊u⌋₊ - 1 : ℕ) : ℝ) + 1 := by
      rcases Nat.eq_zero_or_pos ⌊u⌋₊ with h | h
      · rw [h]; simp
      · rw [Nat.cast_sub h]; simp
    linarith

theorem sum_window_numeric (d : ℕ) {L t : ℝ} (hL : 1 ≤ L) (ht : 1 ≤ t) :
    ((⌊t⌋₊ : ℝ) + 1) * Real.exp (4 * d * (Real.exp 1 - 1) - (⌈L⌉₊ : ℝ)) ≤
      heavyCJ d * t ^ 2 * Real.exp (-(L / 2)) := by
  have hc : L ≤ (⌈L⌉₊ : ℝ) := Nat.le_ceil L
  have hf : (⌊t⌋₊ : ℝ) ≤ t := Nat.floor_le (by linarith)
  have e1 : Real.exp (4 * d * (Real.exp 1 - 1) - (⌈L⌉₊ : ℝ)) ≤
      Real.exp (4 * d * (Real.exp 1 - 1)) * Real.exp (-(L / 2)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.2
    linarith
  have hA : 0 ≤ Real.exp (4 * d * (Real.exp 1 - 1)) := (Real.exp_pos _).le
  have hB : 0 ≤ Real.exp (-(L / 2)) := (Real.exp_pos _).le
  unfold heavyCJ
  calc ((⌊t⌋₊ : ℝ) + 1) * Real.exp (4 * d * (Real.exp 1 - 1) - (⌈L⌉₊ : ℝ))
      ≤ (2 * t ^ 2) * (Real.exp (4 * d * (Real.exp 1 - 1)) * Real.exp (-(L / 2))) := by
        refine mul_le_mul (by nlinarith) e1 (Real.exp_pos _).le (by positivity)
    _ ≤ 4 * Real.exp (4 * d * (Real.exp 1 - 1)) * t ^ 2 * Real.exp (-(L / 2)) := by
        have : 0 ≤ t ^ 2 * (Real.exp (4 * d * (Real.exp 1 - 1)) * Real.exp (-(L / 2))) := by
          positivity
        nlinarith

variable {Ω : Type*} [MeasurableSpace Ω] {Pe : Measure Ω} {ν : Ω → Measure (RingSpace d β)}

/-- Fast jumping is unlikely. For a Poisson environment, `β ≥ 2`, `L ≥ 1`, `t ≥ 1`:
`P(τ_jump(W^ν_{0,0}; L) ≤ t) ≤ C_J t² e^{-L/2}`. -/
theorem pathTjump_first_prob (hβ : 2 ≤ β)
    (hν : IsPoissonPointProcess ν (ringIntensity d β) Pe) {L t : ℝ} (hL : 1 ≤ L) (ht : 1 ≤ t) :
    Pe {ω | pathTjump (fun s : ℝ => cycWalk (ν ω) 0 0 s) L ≤ ENNReal.ofReal t} ≤
      ENNReal.ofReal (heavyCJ d * t ^ 2 * Real.exp (-(L / 2))) := by
  have := hν.isProbabilityMeasure
  have hgood : ∀ᵐ ω ∂Pe, Good (ν ω) := ae_good hν
  set k : ℕ := ⌈L⌉₊ with hk
  set A : ℕ → Set Ω := fun m =>
    {ω | k ≤ cycJumpCount (fun s : ℝ => cycWalk (ν ω) 0 0 s) (m : ℝ) ((m : ℝ) + 2)} with hA
  have hsub : {ω | pathTjump (fun s : ℝ => cycWalk (ν ω) 0 0 s) L ≤ ENNReal.ofReal t} ≤ᵐ[Pe]
      ⋃ m ∈ Finset.range (⌊t⌋₊ + 1), A m := by
    filter_upwards [hgood] with ω hω h
    have hcyc := isCyclicPath_cycWalk hω
    obtain ⟨u, hu, hLu⟩ := (pathTjump_le_iff_rational hcyc (by linarith) (by linarith)).1 h
    obtain ⟨hu0, hut⟩ := rationalTimes_pos hu
    refine mem_iUnion₂.2 ⟨⌊u⌋₊ - 1, ?_, ?_⟩
    · simp only [Finset.mem_range]
      have : ⌊u⌋₊ ≤ ⌊t⌋₊ := Nat.floor_le_floor hut
      omega
    · have h1 := cycJumpCount_window_le hcyc hu0
      have h2 : k ≤ cycJumpCount (fun s : ℝ => cycWalk (ν ω) 0 0 s) (u - 1) u := by
        rw [hk]; exact Nat.ceil_le.2 hLu
      exact h2.trans h1
  have hmeas : Pe.real {ω | pathTjump (fun s : ℝ => cycWalk (ν ω) 0 0 s) L ≤ ENNReal.ofReal t} ≤
      heavyCJ d * t ^ 2 * Real.exp (-(L / 2)) := by
    calc _ ≤ Pe.real (⋃ m ∈ Finset.range (⌊t⌋₊ + 1), A m) := measureReal_mono_ae' hsub
      _ ≤ ∑ m ∈ Finset.range (⌊t⌋₊ + 1), Pe.real (A m) := measureReal_biUnion_finset_le _ _
      _ ≤ ∑ m ∈ Finset.range (⌊t⌋₊ + 1), Real.exp (4 * d * (Real.exp 1 - 1) - (k : ℝ)) :=
          Finset.sum_le_sum fun m _ => jump_window_prob hβ hν k m
      _ = ((⌊t⌋₊ : ℝ) + 1) * Real.exp (4 * d * (Real.exp 1 - 1) - (k : ℝ)) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring
      _ ≤ _ := sum_window_numeric d hL ht
  rw [← ENNReal.ofReal_toReal (measure_ne_top Pe _)]
  exact ENNReal.ofReal_le_ofReal hmeas

/-- `τ_fast` version: `τ_jump ≤ τ_fast` for cyclic paths. -/
theorem pathTfast_first_prob (hβ : 2 ≤ β)
    (hν : IsPoissonPointProcess ν (ringIntensity d β) Pe) {L t : ℝ} (hL : 1 ≤ L) (ht : 1 ≤ t) :
    Pe {ω | pathTfast (fun s : ℝ => cycWalk (ν ω) 0 0 s) L ≤ ENNReal.ofReal t} ≤
      ENNReal.ofReal (heavyCJ d * t ^ 2 * Real.exp (-(L / 2))) := by
  have hgood : ∀ᵐ ω ∂Pe, Good (ν ω) := ae_good hν
  refine le_trans (measure_mono_ae ?_) (pathTjump_first_prob hβ hν hL ht)
  filter_upwards [hgood] with ω hω h
  exact (pathTjump_le_pathTfast (isCyclicPath_cycWalk hω) L).trans h

end ElboimSly.Paper.Heavy
