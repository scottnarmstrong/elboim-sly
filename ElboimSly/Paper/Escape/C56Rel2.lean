/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Escape.Phases
public import ElboimSly.Paper.Escape.RelaxedClosed
public import ElboimSly.Paper.Escape.C56Shift
public import Mathlib

/-!
# Relaxed times: first relaxed times, shifts in time and space

ES22 Claim 5.6, "ℬ_i holds".  The relaxed times of `W_v` relative to `ζ_{i-1}` are those
of `W̃` relative to `0`, shifted by `ζ_{i-1}`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Paper.Escape

open ElboimSly ElboimSly.Paper

section Zeta

variable {k : ℕ}

/-- If the first relaxed time is `< hi`, it is relaxed. -/
theorem escZetaStep_relaxed {β : ℝ} {y : ℝ → Fin (k + 2) → ℤ} {lo hi prev : ℝ}
    (hrc : ∀ r, prev ≤ r → ∀ᶠ u in 𝓝[≥] r, y u = y r) (h : escZetaStep β y lo hi prev < hi) :
    IsRelaxedTimeWrt β y prev (escZetaStep β y lo hi prev) ∧ prev ≤ escZetaStep β y lo hi prev := by
  unfold escZetaStep at h ⊢
  by_cases hex : ∃ s ∈ relaxedSet β y prev, lo ≤ s ∧ s < hi
  · rw [ite_eq_left hex] at h ⊢
    obtain ⟨s0, hs0, h1, -⟩ := hex
    have hne : (relaxedSet β y prev ∩ Ici lo).Nonempty := ⟨s0, hs0, h1⟩
    obtain ⟨hm, -⟩ := csInf_mem_relaxedSet hrc hne
    exact ⟨hm.2, hm.1⟩
  · rw [ite_eq_right hex] at h; exact absurd h (lt_irrefl _)

/-- If there is a relaxed time in `[lo, hi)`, the first one is `< hi`. -/
theorem escZetaStep_lt_of_exists {β : ℝ} {y : ℝ → Fin (k + 2) → ℤ} {lo hi prev s : ℝ}
    (hs : s ∈ relaxedSet β y prev) (h1 : lo ≤ s) (h2 : s < hi) :
    escZetaStep β y lo hi prev < hi ∧ escZetaStep β y lo hi prev ≤ s := by
  have hex : ∃ s ∈ relaxedSet β y prev, lo ≤ s ∧ s < hi := ⟨s, hs, h1, h2⟩
  unfold escZetaStep
  rw [ite_eq_left hex]
  have hle : sInf (relaxedSet β y prev ∩ Ici lo) ≤ s :=
    csInf_le ⟨lo, fun x hx => hx.2⟩ ⟨hs, h1⟩
  exact ⟨lt_of_le_of_lt hle h2, hle⟩

end Zeta

section Shift

variable {d : ℕ} {β : ℝ}

theorem isHeavy_congr_vis {w w' : ℝ → Fin d → ℤ} {a t a' t' : ℝ} (x y' : Fin d → ℤ) (r : ℝ)
    (h : visitedSet w a t = (fun z => x + z) '' visitedSet w' a' t') :
    IsHeavy w a t (x + y') r ↔ IsHeavy w' a' t' y' r := by
  unfold IsHeavy
  refine and_congr Iff.rfl ?_
  rw [h]
  have e : {y : Fin d → ℤ | ‖y - (x + y')‖ ≤ r} ∩ (fun z => x + z) '' visitedSet w' a' t' =
      (fun z => x + z) '' ({y : Fin d → ℤ | ‖y - y'‖ ≤ r} ∩ visitedSet w' a' t') := by
    rw [Set.image_inter (add_right_injective x)]
    congr 1
    ext y
    simp only [mem_ofPred_eq, mem_image]
    constructor
    · intro hy
      refine ⟨y - x, ?_, by abel⟩
      have : y - x - y' = y - (x + y') := by abel
      rw [this]; exact hy
    · rintro ⟨z, hz, rfl⟩
      have : x + z - (x + y') = z - y' := by abel
      rw [this]; exact hz
  rw [e, Set.ncard_image_of_injective _ (add_right_injective x)]

/-- Relaxedness only reads the path on `[a, t]`, up to a space shift and a time shift. -/
theorem isRelaxedTimeWrt_shift (hβ : 0 < β) {w g : ℝ → Fin d → ℤ} (x : Fin d → ℤ) (τ a s : ℝ)
    (h : ∀ r ∈ Icc a s, w (τ + r) = x + g r) :
    IsRelaxedTimeWrt β w (τ + a) (τ + s) ↔ IsRelaxedTimeWrt β g a s := by
  have hvis : visitedSet w (τ + a) (τ + s) = (fun z => x + z) '' visitedSet g a s := by
    unfold visitedSet
    ext y
    simp only [mem_image, mem_Icc]
    constructor
    · rintro ⟨u, ⟨hu1, hu2⟩, rfl⟩
      refine ⟨g (u - τ), ⟨u - τ, ⟨by linarith, by linarith⟩, rfl⟩, ?_⟩
      have := h (u - τ) ⟨by linarith, by linarith⟩
      rw [show τ + (u - τ) = u by ring] at this
      exact this.symm
    · rintro ⟨_, ⟨r, ⟨hr1, hr2⟩, rfl⟩, rfl⟩
      exact ⟨τ + r, ⟨by linarith, by linarith⟩, h r ⟨hr1, hr2⟩⟩
  unfold IsRelaxedTimeWrt
  by_cases has : a ≤ s
  · have hws : w (τ + s) = x + g s := h s ⟨has, le_rfl⟩
    refine and_congr ?_ ?_
    · refine forall_congr' fun r => imp_congr_right fun _ => not_congr ?_
      rw [hws]
      exact isHeavy_congr_vis x (g s) r hvis
    · constructor
      · intro H r hr1 hr2
        have hb : 0 ≤ β ^ (3 * indDelta d) := (Real.rpow_pos_of_pos hβ _).le
        have := H (τ + r) (by linarith) (by linarith)
        rw [hws, h r ⟨hr1, by linarith⟩] at this
        have e : x + g s - (x + g r) = g s - g r := by abel
        rwa [e] at this
      · intro H s'' hs1 hs2
        have hb : 0 ≤ β ^ (3 * indDelta d) := (Real.rpow_pos_of_pos hβ _).le
        have := H (s'' - τ) (by linarith) (by linarith)
        have hr := h (s'' - τ) ⟨by linarith, by linarith⟩
        rw [show τ + (s'' - τ) = s'' by ring] at hr
        rw [hws, hr]
        have e : x + g s - (x + g (s'' - τ)) = g s - g (s'' - τ) := by abel
        rwa [e]
  · -- empty interval: both sides are about the empty visited set and vacuous (R2)
    push Not at has
    have hvE : visitedSet w (τ + a) (τ + s) = ∅ := by
      unfold visitedSet; rw [Set.Icc_eq_empty (by linarith)]; simp
    have hvE' : visitedSet g a s = ∅ := by
      unfold visitedSet; rw [Set.Icc_eq_empty (by linarith)]; simp
    have hnh : ∀ (w' : ℝ → Fin d → ℤ) (a' t' : ℝ) (y : Fin d → ℤ) (r : ℝ),
        visitedSet w' a' t' = ∅ → ¬ IsHeavy w' a' t' y r := by
      intro w' a' t' y r hv hh
      have := hh.2
      rw [hv] at this
      simp only [Set.inter_empty, Set.ncard_empty, Nat.cast_zero] at this
      have h0 := hh.1
      have : (0 : ℝ) < r ^ (5 / 2 : ℝ) := Real.rpow_pos_of_pos h0 _
      linarith
    refine and_congr ?_ ?_
    · exact ⟨fun H r hr hh => absurd hh (hnh _ _ _ _ _ hvE'),
        fun H r hr hh => absurd hh (hnh _ _ _ _ _ hvE)⟩
    · have hb : 0 ≤ β ^ (3 * indDelta d) := (Real.rpow_pos_of_pos hβ _).le
      constructor
      · intro H s'' hs1 hs2; linarith
      · intro H s'' hs1 hs2; linarith

end Shift

end ElboimSly.Paper.Escape

end
