/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Interchange.TrajApi
import Mathlib

/-!
# Restriction, restart and periodicity of trajectories

Restriction, restart, periodicity.

(a) Restriction is `IsPathOn.mono` (in `BoundedPath`). (b) Restart: `fwdTraj_restart`.
(c) Periodicity: `fwdTraj_add_zsmul`, `bwdTraj_add_zsmul`.
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped NNReal

namespace ElboimSly.Interchange

variable {d : ℕ} {β : ℝ} [Fact (0 < β)] {ν : Measure (RingSpace d β)}

omit [Fact (0 < β)] in
/-- Ring times are `β`-periodic. -/
theorem rings_add_zsmul (e : Edge d) (t : ℝ) (k : ℤ) :
    Rings ν e (t + k * β) ↔ Rings ν e t := by
  have : ((t + k * β : ℝ) : AddCircle β) = (t : AddCircle β) := by
    rw [AddCircle.coe_add, ← zsmul_eq_mul, AddCircle.coe_zsmul, AddCircle.coe_period, smul_zero,
      add_zero]
  unfold Rings
  rw [this]

omit [Fact (0 < β)] in
theorem swapRule_add_zsmul (t : ℝ) (k : ℤ) (z w : Fin d → ℤ) :
    SwapRule ν (t + k * β) z w ↔ SwapRule ν t z w := by
  unfold SwapRule
  simp only [rings_add_zsmul]

theorem tendsto_sub_const_nhdsWithin (c t : ℝ) (S T : Set ℝ) (h : ∀ u ∈ S, u - c ∈ T) :
    Tendsto (fun u : ℝ => u - c) (𝓝[S] t) (𝓝[T] (t - c)) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
  · exact ((continuous_id.sub continuous_const).tendsto t).mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin (a := t) (s := S)] with u hu using h u hu

omit [Fact (0 < β)] in
/-- Time translation by a multiple of `β` preserves paths. -/
theorem IsPathOn.shift {a b : ℝ} {f : ℝ → Fin d → ℤ} (h : IsPathOn ν a b f) (k : ℤ) :
    IsPathOn ν (a + k * β) (b + k * β) (fun t => f (t - k * β)) := by
  set c : ℝ := k * β with hc
  have hL : ∀ {t : ℝ} {z : Fin d → ℤ}, IsLeftLimitAbove a f (t - c) z →
      IsLeftLimitAbove (a + c) (fun t => f (t - c)) t z := fun {t z} hz => by
    have hT := tendsto_sub_const_nhdsWithin c t (Set.Iio t) (Set.Iio (t - c))
      (fun u hu => sub_lt_sub_right hu c)
    filter_upwards [hT.eventually hz] with u hu hau
    exact hu (by linarith)
  have key : ∀ {t : ℝ}, a + c < t → t ≤ b + c → ∀ z,
      IsLeftLimitAbove (a + c) (fun t => f (t - c)) t z → IsLeftLimitAbove a f (t - c) z :=
    fun {t} ht htb z hz => by
    obtain ⟨z', hz'⟩ := h.2.1 (t - c) ⟨by linarith, by linarith⟩
    exact (IsLeftLimitAbove.unique ht (hL hz') hz) ▸ hz'
  refine ⟨fun t ht => ?_, fun t ht => ?_, ?_, fun t ht z hz => ?_⟩
  · have hT := tendsto_sub_const_nhdsWithin c t (Set.Ici t) (Set.Ici (t - c))
      (fun u hu => sub_le_sub_right hu c)
    filter_upwards [hT.eventually (h.1 (t - c) ⟨by linarith [ht.1], by linarith [ht.2]⟩)]
      with u hu hub
    exact hu (by linarith)
  · obtain ⟨z, hz⟩ := h.2.1 (t - c) ⟨by linarith [ht.1], by linarith [ht.2]⟩
    exact ⟨z, hL hz⟩
  · refine (h.2.2.1.image (fun u => u + c)).subset ?_
    rintro t ⟨ht, z, hz, hne⟩
    exact ⟨t - c, ⟨⟨by linarith [ht.1], by linarith [ht.2]⟩, z, key ht.1 ht.2 z hz, hne⟩,
      sub_add_cancel t c⟩
  · have h1 := h.2.2.2 (t - c) ⟨by linarith [ht.1], by linarith [ht.2]⟩ z (key ht.1 ht.2 z hz)
    have h2 := (swapRule_add_zsmul (ν := ν) (t - c) k z (f (t - c))).mpr h1
    rwa [sub_add_cancel] at h2

/-- Restart. Restriction, restart, periodicity(b). -/
theorem fwdTraj_restart (hν : Good ν) (x : Fin d → ℤ) {a c : ℝ} (hac : a ≤ c) {t : ℝ}
    (hct : c ≤ t) : fwdTraj hν x a t = fwdTraj hν (fwdTraj hν x a c) c t :=
  fwdTraj_eq_of_isPathOn hν hct ((fwdTraj_isPathOn hν x a t).mono hac le_rfl) rfl t
    ⟨hct, le_rfl⟩

/-- Periodicity of forward trajectories. Restriction, restart, periodicity(c). -/
theorem fwdTraj_add_zsmul (hν : Good ν) (x : Fin d → ℤ) (a : ℝ) (k : ℤ) {t : ℝ} (hat : a ≤ t) :
    fwdTraj hν x (a + k * β) (t + k * β) = fwdTraj hν x a t := by
  have hF := (fwdTraj_isPathOn hν x a t).shift k
  have h := fwdTraj_eq_of_isPathOn hν (x := x) (by linarith) hF
    (by simp [fwdTraj_self]) (t + k * β) ⟨by linarith, le_rfl⟩
  simpa using h.symm

/-- Periodicity of backward trajectories. Restriction, restart, periodicity(c). -/
theorem bwdTraj_add_zsmul (hν : Good ν) (y : Fin d → ℤ) (b : ℝ) (k : ℤ) {t : ℝ} (htb : t ≤ b) :
    bwdTraj hν y (b + k * β) (t + k * β) = bwdTraj hν y b t := by
  have hF := (bwdTraj_isPathOn hν y t b).shift k
  have h := bwdTraj_eq_of_isPathOn hν (y := y) (by linarith) hF
    (by simp [bwdTraj_self]) (t + k * β) ⟨le_rfl, by linarith⟩
  simpa using h.symm

end ElboimSly.Interchange
