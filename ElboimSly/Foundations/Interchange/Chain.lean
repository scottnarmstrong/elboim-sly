/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Interchange.Swap
public import ElboimSly.Frozen.Defs.IsRingPath
public import ElboimSly.Frozen.Defs.RingWindow
import Mathlib

/-!
# No accumulation of jumps

Existence and uniqueness of trajectories ("No accumulation"), using (G3).

An infinite chain of jumps along ringing edges, at strictly increasing times, has unbounded time.
The backward version has strictly decreasing times that are unbounded below.
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped NNReal

namespace ElboimSly.Interchange

variable {d : ℕ} {β : ℝ} [Fact (0 < β)] {ν : Measure (RingSpace d β)}

/-- Every short interval lies in a window `I_j`. -/
theorem exists_window (p : ℝ) : ∃ j : ℤ, ∀ u, p ≤ u → u ≤ p + β / 8 → u ∈ ringWindow β j := by
  have hβ : 0 < β := Fact.out
  refine ⟨⌊4 * p / β⌋, fun u hu hu' => ?_⟩
  have h1 : ((⌊4 * p / β⌋ : ℤ) : ℝ) ≤ 4 * p / β := Int.floor_le _
  have h2 : 4 * p / β < ((⌊4 * p / β⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one _
  rw [le_div_iff₀ hβ] at h1
  rw [div_lt_iff₀ hβ] at h2
  unfold ringWindow
  constructor <;> nlinarith

/-- A forward infinite ring chain has unbounded times. -/
theorem not_bddAbove_of_ring_chain (hν : Good ν) (t : ℕ → ℝ) (z : ℕ → Fin d → ℤ)
    (ht : StrictMono t)
    (hring : ∀ k, ∃ e : Edge d, e.1 = s(z k, z (k + 1)) ∧ Rings ν e (t (k + 1))) :
    ¬ BddAbove (Set.range t) := by
  intro hb
  have hβ : 0 < β := Fact.out
  obtain ⟨_, ⟨K, rfl⟩, hK⟩ := exists_lt_of_lt_csSup (Set.range_nonempty t)
    (show sSup (Set.range t) - β / 8 < sSup (Set.range t) by linarith)
  obtain ⟨j, hj⟩ := exists_window (β := β) (sSup (Set.range t) - β / 8)
  obtain ⟨n, hn1, -⟩ := hν.2.2.2 (z K) j
  refine hn1 ⟨fun i => z (K + i.val), fun i => t (K + i.val + 1), by simp, ?_, ?_, ?_⟩
  · intro i i' hii'
    exact ht (by have : i.val < i'.val := hii'; omega)
  · intro i
    have h1 : t (K + i.val + 1) ≤ sSup (Set.range t) := le_csSup hb ⟨_, rfl⟩
    have h2 : t K ≤ t (K + i.val + 1) := ht.monotone (by omega)
    exact hj _ (by linarith) (by linarith)
  · intro i
    simpa [add_assoc] using hring (K + i.val)

/-- A backward infinite ring chain has times unbounded below. -/
theorem not_bddBelow_of_ring_chain (hν : Good ν) (t : ℕ → ℝ) (z : ℕ → Fin d → ℤ)
    (ht : StrictAnti t)
    (hring : ∀ k, ∃ e : Edge d, e.1 = s(z k, z (k + 1)) ∧ Rings ν e (t (k + 1))) :
    ¬ BddBelow (Set.range t) := by
  intro hb
  have hβ : 0 < β := Fact.out
  obtain ⟨_, ⟨K, rfl⟩, hK⟩ := exists_lt_of_csInf_lt (Set.range_nonempty t)
    (show sInf (Set.range t) < sInf (Set.range t) + β / 8 by linarith)
  obtain ⟨j, hj⟩ := exists_window (β := β) (sInf (Set.range t))
  obtain ⟨n, -, hn2⟩ := hν.2.2.2 (z K) j
  refine hn2 ⟨fun i => z (K + (n - i.val)), fun i => t (K + (n - i.val)), by simp, ?_, ?_, ?_⟩
  · intro i i' hii'
    have : i.val < i'.val := hii'
    have : i'.val < n := i'.2
    exact ht (by omega)
  · intro i
    have h1 : sInf (Set.range t) ≤ t (K + (n - i.val)) := csInf_le hb ⟨_, rfl⟩
    have h2 : t (K + (n - i.val)) ≤ t K := ht.antitone (by omega)
    exact hj _ h1 (by linarith)
  · intro i
    have hi : i.val < n := i.2
    obtain ⟨e, he, hr⟩ := hring (K + (n - (i.val + 1)))
    have h3 : K + (n - (i.val + 1)) + 1 = K + (n - i.val) := by omega
    rw [h3] at he hr
    refine ⟨e, ?_, hr⟩
    simpa [Sym2.eq_swap] using he

end ElboimSly.Interchange
