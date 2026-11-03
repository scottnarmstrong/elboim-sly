/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Step.TravelEngine
public import Mathlib

/-!
# The pathwise bound of Lemma 7.6 (Step 4)

ES22 Lemma 7.6, Step 4. On the complement of the four events
`E₁` (natural coupling is `ε'`-close to `W`), `E₂` (no block leaves `(-K, K)`),
`E₃` (the block sums are within `r₃` of `σ B((j+1)T)`) and `E₄` (the oscillation of `B` over each
block is below `K`), `‖W(u) - σ B(u)‖ < ε' + 4K + r₃` for every `u ≤ ℓT`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ElboimSly.Cyclic ElboimSly.SRW
open scoped NNReal ENNReal

namespace ElboimSly.Paper.Step

open ElboimSly.Paper

variable {d : ℕ} {β : ℝ} [Fact (0 < β)]

theorem norm_add3_lt {E : Type*} [SeminormedAddCommGroup E] {x y z : E} {a b c : ℝ}
    (hx : ‖x‖ < a) (hy : ‖y‖ < b) (hz : ‖z‖ < c) : ‖x + y + z‖ < a + b + c :=
  calc ‖x + y + z‖ ≤ ‖x + y‖ + ‖z‖ := norm_add_le _ _
    _ ≤ ‖x‖ + ‖y‖ + ‖z‖ := by gcongr; exact norm_add_le _ _
    _ < a + b + c := by linarith

theorem lemma76_pathwise {Y : ℝ≥0 → Fin d → ℤ} (hY : Y ∈ StepPath d) {T : ℝ≥0} {ℓ : ℕ}
    (hℓ : 1 ≤ ℓ) {K σ ε' r₃ : ℝ} (hσ0 : 0 ≤ σ) (hσ2 : σ ≤ 2) (Bp : ℝ≥0 → Fin d → ℝ)
    (hE1 : ∀ u : ℝ≥0, u ≤ (ℓ : ℝ≥0) * T → ‖stepReg β (stepShift 0 Y) u -
      stepNatTilde β 0 (fun _ => T) ℓ Y u‖ < ε')
    (hE2 : ∀ i < ℓ, stepWj β 0 (fun _ => T) Y i ∉ farSet K T)
    (hE3 : ∀ j < ℓ, ‖∑ i ∈ Finset.range (j + 1),
      (fun c => ((truncEnd T K (stepWj β 0 (fun _ => T) Y i) c : ℤ) : ℝ)) -
        σ • Bp ((((j + 1 : ℕ)) : ℝ≥0) * T)‖ < r₃)
    (hE4 : ∀ j : ℕ, 1 ≤ j → j ≤ ℓ → ∀ s : ℝ≥0, ((j - 1 : ℕ) : ℝ≥0) * T ≤ s → s ≤ j * T →
      ‖Bp s - Bp (j * T)‖ < K)
    (u : ℝ≥0) (hu : u ≤ (ℓ : ℝ≥0) * T) :
    ‖(fun c => ((stepReg β Y u c : ℤ) : ℝ)) - σ • Bp u‖ < ε' + 4 * K + r₃ := by
  set s : ℕ → ℝ≥0 := fun _ => T with hs
  obtain ⟨j, hjℓ, hlow, hup⟩ := exists_block s ℓ hℓ u
  have hSj : stepPartial s j = (j : ℝ≥0) * T := stepPartial_const T j
  have hexp := stepNatTilde_apply β 0 s ℓ Y j u hjℓ hlow hup
  have hv : u - stepPartial s j ≤ T := by
    rw [tsub_le_iff_left, hSj]
    by_cases hj1 : j + 1 < ℓ
    · have := hup hj1
      rw [stepPartial_const] at this
      calc u ≤ ((j + 1 : ℕ) : ℝ≥0) * T := this
        _ = (j : ℝ≥0) * T + T := by push_cast; ring
    · have hjk' : j = ℓ - 1 := by omega
      calc u ≤ (ℓ : ℝ≥0) * T := hu
        _ = (j : ℝ≥0) * T + T := by
          have : (ℓ : ℝ≥0) = j + 1 := by rw [hjk']; exact_mod_cast (Nat.sub_add_cancel hℓ).symm
          rw [this]; ring
  have hZj : ‖stepWalkZ β 0 s Y j (u - stepPartial s j)‖ < K := by
    have := lt_of_not_mem_farSet (isRegPath_stepWj (β := β) hY 0 s j) hv (hE2 j hjℓ)
    have hmin : min (u - stepPartial s j) (s j) = u - stepPartial s j := min_eq_left hv
    simp only [stepWj, hmin] at this
    exact this
  have hZT : ‖stepWalkZ β 0 s Y j T‖ < K := by
    have := lt_of_not_mem_farSet (isRegPath_stepWj (β := β) hY 0 s j) (le_refl T) (hE2 j hjℓ)
    have hmin : min T (s j) = T := min_self T
    simp only [stepWj, hmin] at this
    exact this
  -- the sums of the truncated endpoints
  have hsum : ∀ m ≤ ℓ, ∑ i ∈ Finset.range m, stepWalkZ β 0 s Y i (s i) =
      ∑ i ∈ Finset.range m, truncEnd T K (stepWj β 0 s Y i) := by
    intro m hm
    refine Finset.sum_congr rfl fun i hi => ?_
    have hik : i < ℓ := lt_of_lt_of_le (Finset.mem_range.1 hi) hm
    rw [truncEnd, Set.indicator_of_mem (show stepWj β 0 s Y i ∈ (farSet K T)ᶜ from hE2 i hik)]
    simp [stepWj, hs]
  have hcast : ∀ m : ℕ, ∑ i ∈ Finset.range m,
      (fun c => ((truncEnd T K (stepWj β 0 (fun _ => T) Y i) c : ℤ) : ℝ)) =
      fun c => (((∑ i ∈ Finset.range m, truncEnd T K (stepWj β 0 s Y i)) c : ℤ) : ℝ) := by
    intro m; funext c; simp [Finset.sum_apply, hs]
  -- E1
  have hu' : u ≤ (ℓ : ℝ≥0) * T := hu
  have h1 := hE1 u hu'
  rw [stepShift, shiftPath_zero hY] at h1
  have h1' : ‖(fun c => ((stepReg β Y u c : ℤ) : ℝ)) -
      (fun c => ((stepNatTilde β 0 s ℓ Y u c : ℤ) : ℝ))‖ < ε' := by
    have : (fun c => ((stepReg β Y u c : ℤ) : ℝ)) - (fun c => ((stepNatTilde β 0 s ℓ Y u c : ℤ) : ℝ)) =
        fun c => (((stepReg β Y u - stepNatTilde β 0 s ℓ Y u) c : ℤ) : ℝ) := by
      funext c; simp
    rw [this, norm_intCast_pi]; exact h1
  -- E3, E4
  have h3 := hE3 j hjℓ
  rw [hcast, ← hsum (j + 1) hjℓ] at h3
  have hu_lo : ((j : ℕ) : ℝ≥0) * T ≤ u := by
    rcases hlow with h0 | hl
    · rw [h0]; simp
    · rw [hSj] at hl; exact hl.le
  have hu_hi : u ≤ ((j + 1 : ℕ) : ℝ≥0) * T := by
    by_cases hj1 : j + 1 < ℓ
    · have := hup hj1; rwa [stepPartial_const] at this
    · have hjk' : j + 1 = ℓ := by omega
      rw [hjk']; exact hu
  have h4 := hE4 (j + 1) (by omega) hjℓ u (by simpa using hu_lo) hu_hi
  -- assemble
  have hsplit : (fun c => ((stepNatTilde β 0 s ℓ Y u c : ℤ) : ℝ)) - σ • Bp u =
      ((fun c => (((∑ i ∈ Finset.range (j + 1), stepWalkZ β 0 s Y i (s i)) c : ℤ) : ℝ)) -
        σ • Bp ((((j + 1 : ℕ)) : ℝ≥0) * T)) +
      ((fun c => ((stepWalkZ β 0 s Y j (u - stepPartial s j) c : ℤ) : ℝ)) -
        (fun c => ((stepWalkZ β 0 s Y j T c : ℤ) : ℝ))) +
      σ • (Bp ((((j + 1 : ℕ)) : ℝ≥0) * T) - Bp u) := by
    funext c
    simp only [hexp, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_range_succ,
      Int.cast_add]
    have : s j = T := rfl
    rw [this]
    ring
  have hB : ‖σ • (Bp ((((j + 1 : ℕ)) : ℝ≥0) * T) - Bp u)‖ < 2 * K := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hσ0, norm_sub_rev]
    calc σ * ‖Bp u - Bp ((((j + 1 : ℕ)) : ℝ≥0) * T)‖ ≤ 2 * ‖Bp u - Bp ((((j + 1 : ℕ)) : ℝ≥0) * T)‖ :=
          mul_le_mul_of_nonneg_right hσ2 (norm_nonneg _)
      _ < 2 * K := by linarith
  have hZ : ‖(fun c => ((stepWalkZ β 0 s Y j (u - stepPartial s j) c : ℤ) : ℝ)) -
      (fun c => ((stepWalkZ β 0 s Y j T c : ℤ) : ℝ))‖ < 2 * K := by
    have e : (fun c => ((stepWalkZ β 0 s Y j (u - stepPartial s j) c : ℤ) : ℝ)) -
        (fun c => ((stepWalkZ β 0 s Y j T c : ℤ) : ℝ)) =
        fun c => (((stepWalkZ β 0 s Y j (u - stepPartial s j) - stepWalkZ β 0 s Y j T) c : ℤ) : ℝ) := by
      funext c; simp
    rw [e, norm_intCast_pi]
    calc _ ≤ ‖stepWalkZ β 0 s Y j (u - stepPartial s j)‖ + ‖stepWalkZ β 0 s Y j T‖ := norm_sub_le _ _
      _ < 2 * K := by linarith
  have hb : ‖(fun c => ((stepNatTilde β 0 s ℓ Y u c : ℤ) : ℝ)) - σ • Bp u‖ < r₃ + 2 * K + 2 * K := by
    rw [hsplit]
    exact norm_add3_lt h3 hZ hB
  calc ‖(fun c => ((stepReg β Y u c : ℤ) : ℝ)) - σ • Bp u‖
      = ‖((fun c => ((stepReg β Y u c : ℤ) : ℝ)) - (fun c => ((stepNatTilde β 0 s ℓ Y u c : ℤ) : ℝ))) +
          ((fun c => ((stepNatTilde β 0 s ℓ Y u c : ℤ) : ℝ)) - σ • Bp u)‖ := by
        congr 1; abel
    _ ≤ ‖(fun c => ((stepReg β Y u c : ℤ) : ℝ)) - (fun c => ((stepNatTilde β 0 s ℓ Y u c : ℤ) : ℝ))‖ +
        ‖(fun c => ((stepNatTilde β 0 s ℓ Y u c : ℤ) : ℝ)) - σ • Bp u‖ := norm_add_le _ _
    _ < ε' + (r₃ + 2 * K + 2 * K) := add_lt_add h1' hb
    _ = ε' + 4 * K + r₃ := by ring

end ElboimSly.Paper.Step
