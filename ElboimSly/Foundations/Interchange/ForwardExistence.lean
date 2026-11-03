/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Interchange.ForwardPath
public import ElboimSly.Foundations.Interchange.RingTimes
public import ElboimSly.Foundations.Interchange.Chain
import Mathlib

/-!
# Existence of forward trajectories

Existence and uniqueness of trajectories (existence of the forward trajectory).

The greedy construction: from `(t k, z k)` jump to the next ring time of `z k` and the other
endpoint of the ringing edge (or, if `z k` never rings, to the dummy time `t k + 1` without
moving). By (G3) the times are unbounded.
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped NNReal

namespace ElboimSly.Interchange

variable {d : ℕ} {β : ℝ} [Fact (0 < β)] {ν : Measure (RingSpace d β)}

/-- The greedy forward jump sequence from `(a, x)`. -/
structure FwdSeq (ν : Measure (RingSpace d β)) (a : ℝ) (x : Fin d → ℤ) (t : ℕ → ℝ)
    (z : ℕ → Fin d → ℤ) : Prop where
  t_zero : t 0 = a
  z_zero : z 0 = x
  lt : ∀ k, t k < t (k + 1)
  gap : ∀ k u, t k < u → u < t (k + 1) → ¬ RingAt ν (z k) u
  swap : ∀ k, SwapRule ν (t (k + 1)) (z k) (z (k + 1))
  alt : ∀ k, (∃ e : Edge d, e.1 = s(z k, z (k + 1)) ∧ Rings ν e (t (k + 1))) ∨
    (t (k + 1) = t k + 1 ∧ z (k + 1) = z k ∧ ∀ u, ¬ RingAt ν (z k) u)

theorem exists_fwdSeq (hν : Good ν) (a : ℝ) (x : Fin d → ℤ) :
    ∃ (t : ℕ → ℝ) (z : ℕ → Fin d → ℤ), FwdSeq ν a x t z := by
  choose τ w hτ hgap hsw halt using fun p : ℝ × (Fin d → ℤ) => exists_step_fwd hν p.2 p.1
  let sq : ℕ → ℝ × (Fin d → ℤ) := fun n => Nat.rec (a, x) (fun _ p => (τ p, w p)) n
  exact ⟨fun n => (sq n).1, fun n => (sq n).2, rfl, rfl, fun k => hτ (sq k),
    fun k => hgap (sq k), fun k => hsw (sq k), fun k => halt (sq k)⟩

omit [Fact (0 < β)] in
theorem FwdSeq.strictMono {a : ℝ} {x : Fin d → ℤ} {t : ℕ → ℝ} {z : ℕ → Fin d → ℤ}
    (h : FwdSeq ν a x t z) : StrictMono t :=
  strictMono_nat_of_lt_succ h.lt

/-- The jump times of the greedy sequence are unbounded (G3). -/
theorem FwdSeq.unbounded (hν : Good ν) {a : ℝ} {x : Fin d → ℤ} {t : ℕ → ℝ}
    {z : ℕ → Fin d → ℤ} (h : FwdSeq ν a x t z) : ∀ T, ∃ k, T < t k := by
  by_contra hcon
  push Not at hcon
  have hb : BddAbove (Set.range t) := by
    obtain ⟨T, hT⟩ := hcon
    exact ⟨T, by rintro _ ⟨k, rfl⟩; exact hT k⟩
  by_cases hreal : ∀ k, ∃ e : Edge d, e.1 = s(z k, z (k + 1)) ∧ Rings ν e (t (k + 1))
  · exact not_bddAbove_of_ring_chain hν t z h.strictMono hreal hb
  · push Not at hreal
    obtain ⟨k0, hk0⟩ := hreal
    have hfake : ∀ n, t (k0 + n + 1) = t (k0 + n) + 1 ∧ z (k0 + n + 1) = z (k0 + n) ∧
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
    have hgrow : ∀ n : ℕ, t k0 + n ≤ t (k0 + n) := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        have := (hfake n).1
        push_cast
        calc t k0 + (n + 1) = (t k0 + n) + 1 := by ring
          _ ≤ t (k0 + n) + 1 := by linarith
          _ = t (k0 + (n + 1)) := by rw [← this, add_assoc]
    obtain ⟨T, hT⟩ := hb
    obtain ⟨n, hn⟩ := exists_nat_gt (T - t k0)
    have := hT ⟨k0 + n, rfl⟩
    linarith [hgrow n]

/-- Existence of the forward trajectory. Existence and uniqueness of trajectories. -/
theorem exists_forwardTrajectory (hν : Good ν) (x : Fin d → ℤ) (a : ℝ) :
    ∃ γ : ℝ≥0 → Fin d → ℤ, IsForwardTrajectory ν x a γ := by
  obtain ⟨t, z, h⟩ := exists_fwdSeq hν a x
  have hun := h.unbounded hν
  refine ⟨fwdPath a t z, fwdPath_isForwardPath h.strictMono h.t_zero hun h.gap h.swap, ?_⟩
  rw [fwdPath_eq (k := 0) h.strictMono (by simp [h.t_zero]) (by simpa [h.t_zero] using h.lt 0)]
  exact h.z_zero

end ElboimSly.Interchange
