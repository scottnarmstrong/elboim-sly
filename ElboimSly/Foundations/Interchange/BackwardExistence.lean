/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Interchange.BackwardPath
public import ElboimSly.Foundations.Interchange.RingTimes
public import ElboimSly.Foundations.Interchange.Chain
import Mathlib

/-!
# Existence of backward trajectories

Existence and uniqueness of trajectories (existence of the backward trajectory).

The greedy construction with decreasing times, started just after `b` (at a time `c ∈ (b, b + 1]`
where the starting vertex does not ring in `(b, c)`), so that a ring at time `b` itself is seen as
the first jump. By (G3) (paths *ending* at a vertex) the times are unbounded below.
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped NNReal

namespace ElboimSly.Interchange

variable {d : ℕ} {β : ℝ} [Fact (0 < β)] {ν : Measure (RingSpace d β)}

/-- The greedy backward jump sequence to `(y, b)`. -/
structure BwdSeq (ν : Measure (RingSpace d β)) (b : ℝ) (y : Fin d → ℤ) (t : ℕ → ℝ)
    (z : ℕ → Fin d → ℤ) : Prop where
  t_zero : b < t 0
  t_one : t 1 ≤ b
  z_zero : z 0 = y
  lt : ∀ k, t (k + 1) < t k
  gap : ∀ k u, t (k + 1) < u → u < t k → ¬ RingAt ν (z k) u
  swap : ∀ k, SwapRule ν (t (k + 1)) (z k) (z (k + 1))
  alt : ∀ k, (∃ e : Edge d, e.1 = s(z k, z (k + 1)) ∧ Rings ν e (t (k + 1))) ∨
    (t (k + 1) = t k - 1 ∧ z (k + 1) = z k ∧ ∀ u, ¬ RingAt ν (z k) u)

theorem exists_bwdSeq (hν : Good ν) (b : ℝ) (y : Fin d → ℤ) :
    ∃ (t : ℕ → ℝ) (z : ℕ → Fin d → ℤ), BwdSeq ν b y t z := by
  obtain ⟨c, hbc, hcb, hc⟩ := exists_gap hν y b
  choose τ w hτ hgap hsw halt using fun p : ℝ × (Fin d → ℤ) => exists_step_bwd hν p.2 p.1
  let sq : ℕ → ℝ × (Fin d → ℤ) := fun n => Nat.rec (c, y) (fun _ p => (τ p, w p)) n
  refine ⟨fun n => (sq n).1, fun n => (sq n).2, hbc, ?_, rfl, fun k => hτ (sq k),
    fun k => hgap (sq k), fun k => hsw (sq k), fun k => halt (sq k)⟩
  rcases halt (sq 0) with ⟨e, he, her⟩ | ⟨h1, -, -⟩
  · by_contra hlt
    exact hc _ (not_le.mp hlt) (hτ (sq 0)) ⟨e, by
      unfold Edge.Mem; rw [he]; exact Sym2.mem_mk_left _ _, her⟩
  · have : (sq 1).1 = c - 1 := h1
    show (sq 1).1 ≤ b
    linarith

omit [Fact (0 < β)] in
theorem BwdSeq.strictAnti {b : ℝ} {y : Fin d → ℤ} {t : ℕ → ℝ} {z : ℕ → Fin d → ℤ}
    (h : BwdSeq ν b y t z) : StrictAnti t :=
  strictAnti_nat_of_succ_lt h.lt

/-- The jump times of the greedy backward sequence are unbounded below (G3). -/
theorem BwdSeq.unbounded (hν : Good ν) {b : ℝ} {y : Fin d → ℤ} {t : ℕ → ℝ}
    {z : ℕ → Fin d → ℤ} (h : BwdSeq ν b y t z) : ∀ T, ∃ k, t k < T := by
  by_contra hcon
  push Not at hcon
  have hb : BddBelow (Set.range t) := by
    obtain ⟨T, hT⟩ := hcon
    exact ⟨T, by rintro _ ⟨k, rfl⟩; exact hT k⟩
  by_cases hreal : ∀ k, ∃ e : Edge d, e.1 = s(z k, z (k + 1)) ∧ Rings ν e (t (k + 1))
  · exact not_bddBelow_of_ring_chain hν t z h.strictAnti hreal hb
  · push Not at hreal
    obtain ⟨k0, hk0⟩ := hreal
    have hfake : ∀ n, t (k0 + n + 1) = t (k0 + n) - 1 ∧ z (k0 + n + 1) = z (k0 + n) ∧
        ∀ u, ¬ RingAt ν (z (k0 + n)) u := by
      intro n
      induction n with
      | zero =>
        rcases h.alt k0 with hr | hf
        · exact absurd hr (by simpa using hk0)
        · simpa using hf
      | succ n ih =>
        rcases h.alt (k0 + (n + 1)) with ⟨e, he, her⟩ | hf
        · exfalso
          have hz : z (k0 + (n + 1)) = z (k0 + n) := by
            rw [← add_assoc]; exact ih.2.1
          refine ih.2.2 (t (k0 + (n + 1) + 1)) ⟨e, ?_, her⟩
          unfold Edge.Mem
          rw [he, ← hz]
          exact Sym2.mem_mk_left _ _
        · exact hf
    have hgrow : ∀ n : ℕ, t (k0 + n) ≤ t k0 - n := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        have := (hfake n).1
        push_cast
        calc t (k0 + (n + 1)) = t (k0 + n + 1) := by rw [add_assoc]
          _ = t (k0 + n) - 1 := this
          _ ≤ t k0 - (n + 1) := by linarith
    obtain ⟨T, hT⟩ := hb
    obtain ⟨n, hn⟩ := exists_nat_gt (t k0 - T)
    have := hT ⟨k0 + n, rfl⟩
    linarith [hgrow n]

/-- Existence of the backward trajectory. Existence and uniqueness of trajectories. -/
theorem exists_backwardTrajectory (hν : Good ν) (y : Fin d → ℤ) (b : ℝ) :
    ∃ η : ℝ≥0 → Fin d → ℤ, IsBackwardTrajectory ν y b η := by
  obtain ⟨t, z, h⟩ := exists_bwdSeq hν b y
  have hun := h.unbounded hν
  refine ⟨bwdPath b t z,
    bwdPath_isBackwardPath hν h.strictAnti h.t_zero hun h.gap h.swap, ?_⟩
  rw [bwdPath_eq (k := 0) h.strictAnti (by simpa using h.t_zero) (by simpa using h.t_one)]
  exact h.z_zero

end ElboimSly.Interchange
