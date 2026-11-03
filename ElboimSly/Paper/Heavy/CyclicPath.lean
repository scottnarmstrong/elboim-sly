/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Frozen.Defs.IsRelaxedTimeWrt
public import ElboimSly.Frozen.Defs.VisitedSet
public import Mathlib

/-!
# Cyclic paths and cyclic integer times

Cyclic paths and cyclic integer times (ES22 §6, supplement).

A path is a function `w : ℝ → Fin d → ℤ`; only its values on `[0, ∞)` matter (the convention
`w s = 0` for `s < 0` is imposed where needed by evaluating at `max s 0`, as in `cycTfast`).

* `IsCyclicPath w`: right-continuous, finitely many discontinuities in bounded intervals, each of
  `ℓ¹`-size `1`, and `w 0 = 0`.
* `cycClosingTime β w`: `T(w) = inf {ℓβ : ℓ ≥ 1, w (ℓβ) = 0}` in `[0, ∞]`.
* `HasNoReturn β w`: the no-return property.
* `cycIntTimes β`: the cyclic integer times `CI_β`, with phase `cycIntPhase`.
* `cycFloor β x`: `max (CI_β ∩ [0, x])`, with `x - 1 < cycFloor β x ≤ x`.
* `cycJumpCount w a b`: `J_w(a, b]`.  `entranceTime w B`: `ξ_B(w)`.  `relaxedTimes β w`: `𝒯(w)`.
-/

@[expose] public section

open Filter Topology Set
open scoped ENNReal

namespace ElboimSly.Paper

variable {d : ℕ}

/-- The discontinuities of `w` in `(0, ∞)`: the times `r > 0` with `w ≠ w r` arbitrarily close on
the left of `r`. -/
def cycJumpSet (w : ℝ → Fin d → ℤ) : Set ℝ :=
  {r | 0 < r ∧ ¬ ∀ᶠ u in 𝓝[<] r, w u = w r}

/-- Cyclic paths and cyclic integer times. A *cyclic path*: right-continuous, piecewise constant with finitely
many discontinuities in every bounded interval, each of `ℓ¹`-size `1`, and `w 0 = 0`. -/
structure IsCyclicPath (w : ℝ → Fin d → ℤ) : Prop where
  zero : w 0 = 0
  rc : ∀ s : ℝ, 0 ≤ s → ∀ᶠ u in 𝓝[≥] s, w u = w s
  fin : ∀ T : ℝ, (cycJumpSet w ∩ Iic T).Finite
  jump_size : ∀ r ∈ cycJumpSet w, ∀ᶠ u in 𝓝[<] r, ∑ i, |w r i - w u i| = 1

/-- Cyclic paths and cyclic integer times. The closing time
`T(w) = inf {ℓβ : ℓ ∈ ℤ_{≥1}, w (ℓβ) = 0} ∈ [0, ∞]`. -/
noncomputable def cycClosingTime (β : ℝ) (w : ℝ → Fin d → ℤ) : ℝ≥0∞ :=
  ⨅ ℓ ∈ {ℓ : ℕ | 1 ≤ ℓ ∧ w (ℓ * β) = 0}, ENNReal.ofReal (ℓ * β)

/-- Cyclic paths and cyclic integer times. The *no-return property*: `w s ≠ w s'` whenever
`0 ≤ s' < s < T(w)` and `s - s' ∈ βℤ`. -/
def HasNoReturn (β : ℝ) (w : ℝ → Fin d → ℤ) : Prop :=
  ∀ s s' : ℝ, 0 ≤ s' → s' < s → ENNReal.ofReal s < cycClosingTime β w →
    (∃ k : ℤ, s - s' = k * β) → w s ≠ w s'

/-- Cyclic paths and cyclic integer times. The cyclic integer times
`CI_β = {x ≥ 0 : x - β ⌊x/β⌋ ∈ ℤ}`. -/
def cycIntTimes (β : ℝ) : Set ℝ := {x | 0 ≤ x ∧ ∃ m : ℤ, x - β * ⌊x / β⌋ = m}

/-- Cyclic paths and cyclic integer times. The phase `q(x) = x - β ⌊x/β⌋`. -/
noncomputable def cycIntPhase (β x : ℝ) : ℝ := x - β * ⌊x / β⌋

/-- Cyclic paths and cyclic integer times. `J_w(a, b]`, the number of discontinuities of `w` in
`(a, b] ∩ (0, ∞)`. -/
noncomputable def cycJumpCount (w : ℝ → Fin d → ℤ) (a b : ℝ) : ℕ :=
  (cycJumpSet w ∩ Ioc a b).ncard

/-- Cyclic paths and cyclic integer times. The first entrance time `ξ_B(w) = inf {t ≥ 0 : w t ∈ B}`. -/
noncomputable def entranceTime (w : ℝ → Fin d → ℤ) (B : Set (Fin d → ℤ)) : ℝ≥0∞ :=
  ⨅ t ∈ {t : ℝ | 0 ≤ t ∧ w t ∈ B}, ENNReal.ofReal t

/-- Cyclic paths and cyclic integer times. `𝒯(w) = {s ≥ 0 : s is relaxed with respect to w|[0,s]}`. -/
def relaxedTimes (β : ℝ) (w : ℝ → Fin d → ℤ) : Set ℝ :=
  {s | 0 ≤ s ∧ IsRelaxedTimeWrt β w 0 s}

/-- `max (CI_β ∩ [0, x])`, computed explicitly. -/
noncomputable def cycFloor (β x : ℝ) : ℝ :=
  β * ⌊x / β⌋ + ⌊x - β * ⌊x / β⌋⌋

section floor

variable {β x : ℝ}

private theorem frac_nonneg (hβ : 0 < β) : 0 ≤ x - β * ⌊x / β⌋ := by
  have := Int.floor_le (x / β)
  have h2 : β * (x / β) = x := by field_simp
  nlinarith

private theorem frac_lt (hβ : 0 < β) : x - β * ⌊x / β⌋ < β := by
  have := Int.lt_floor_add_one (x / β)
  have h2 : β * (x / β) = x := by field_simp
  nlinarith

private theorem floor_cycFloor (hβ : 0 < β) (_hx : 0 ≤ x) :
    ⌊cycFloor β x / β⌋ = ⌊x / β⌋ := by
  unfold cycFloor
  have h0 : 0 ≤ ⌊x - β * ⌊x / β⌋⌋ := Int.floor_nonneg.2 (frac_nonneg hβ)
  have h1 : ((⌊x - β * ⌊x / β⌋⌋ : ℤ) : ℝ) < β :=
    lt_of_le_of_lt (Int.floor_le _) (frac_lt hβ)
  have h0' : (0 : ℝ) ≤ ((⌊x - β * ⌊x / β⌋⌋ : ℤ) : ℝ) := by exact_mod_cast h0
  rw [Int.floor_eq_iff]
  have e : (β * ⌊x / β⌋ + ⌊x - β * ⌊x / β⌋⌋) / β =
      ⌊x / β⌋ + ((⌊x - β * ⌊x / β⌋⌋ : ℤ) : ℝ) / β := by field_simp
  rw [e]
  constructor
  · have : 0 ≤ ((⌊x - β * ⌊x / β⌋⌋ : ℤ) : ℝ) / β := div_nonneg h0' hβ.le
    linarith
  · have : ((⌊x - β * ⌊x / β⌋⌋ : ℤ) : ℝ) / β < 1 := (div_lt_one hβ).2 h1
    linarith

theorem cycFloor_mem (hβ : 0 < β) (hx : 0 ≤ x) : cycFloor β x ∈ cycIntTimes β := by
  refine ⟨?_, ⌊x - β * ⌊x / β⌋⌋, ?_⟩
  · have h0 : 0 ≤ ⌊x - β * ⌊x / β⌋⌋ := Int.floor_nonneg.2 (frac_nonneg hβ)
    have h0' : (0 : ℝ) ≤ ((⌊x - β * ⌊x / β⌋⌋ : ℤ) : ℝ) := by exact_mod_cast h0
    have : (0 : ℝ) ≤ ((⌊x / β⌋ : ℤ) : ℝ) := by exact_mod_cast Int.floor_nonneg.2 (by positivity)
    unfold cycFloor
    have := mul_nonneg hβ.le this
    linarith
  · rw [floor_cycFloor hβ hx]; unfold cycFloor; ring

theorem cycFloor_le (_hβ : 0 < β) : cycFloor β x ≤ x := by
  unfold cycFloor
  have := Int.floor_le (x - β * ⌊x / β⌋)
  linarith

theorem lt_cycFloor_add_one (_hβ : 0 < β) : x < cycFloor β x + 1 := by
  unfold cycFloor
  have := Int.lt_floor_add_one (x - β * ⌊x / β⌋)
  linarith

/-- `cycFloor β x` is the greatest cyclic integer time `≤ x`. -/
theorem le_cycFloor_of_mem (hβ : 0 < β) (hx : 0 ≤ x) {y : ℝ} (hy : y ∈ cycIntTimes β)
    (hyx : y ≤ x) : y ≤ cycFloor β x := by
  obtain ⟨hy0, j, hj⟩ := hy
  set ℓ := ⌊y / β⌋ with hℓ
  have hℓm : ℓ ≤ ⌊x / β⌋ := by
    rw [Int.le_floor]
    have := Int.floor_le (y / β)
    calc (ℓ : ℝ) ≤ y / β := this
      _ ≤ x / β := by gcongr
  have hm0 : (0 : ℤ) ≤ ⌊x / β⌋ := Int.floor_nonneg.2 (by positivity)
  have hf0 : 0 ≤ ⌊x - β * ⌊x / β⌋⌋ := Int.floor_nonneg.2 (frac_nonneg hβ)
  have hf0' : (0 : ℝ) ≤ ((⌊x - β * ⌊x / β⌋⌋ : ℤ) : ℝ) := by exact_mod_cast hf0
  unfold cycFloor
  rcases lt_or_eq_of_le hℓm with hlt | heq
  · have h1 : ((ℓ : ℤ) : ℝ) + 1 ≤ ((⌊x / β⌋ : ℤ) : ℝ) := by exact_mod_cast hlt
    have h2 : y < β * (ℓ + 1) := by
      have := frac_lt hβ (x := y); linarith
    have h3 : β * (ℓ + 1) ≤ β * ⌊x / β⌋ := by gcongr
    linarith
  · have hjq : (j : ℝ) ≤ x - β * ⌊x / β⌋ := by
      rw [← heq]; linarith
    have : j ≤ ⌊x - β * ⌊x / β⌋⌋ := Int.le_floor.2 hjq
    have h' : (j : ℝ) ≤ ((⌊x - β * ⌊x / β⌋⌋ : ℤ) : ℝ) := by exact_mod_cast this
    have hy : y = β * ⌊x / β⌋ + j := by rw [← heq]; linarith
    linarith

end floor

end ElboimSly.Paper
