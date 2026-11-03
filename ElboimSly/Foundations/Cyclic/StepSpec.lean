/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.NextRing
public import ElboimSly.Foundations.Interchange.ForwardExistence
public import ElboimSly.Foundations.Interchange.Swap
import Mathlib

/-!
# The explicit forward step

Measurability, Step 2 (the recursion `t_{k+1} = R(ν, z_k, t_k)`).

For a vertex `z` and a time `t`, `stepT ν z t` is the next ring time at `z` (or `t + 1` if `z`
never rings) and `stepW ν z t` the position after the jump. On good `ν` they satisfy exactly the
properties of `exists_step_fwd`, so the iterates form a `FwdSeq`.
-/

@[expose] public section

open MeasureTheory Set ElboimSly.Interchange
open scoped ENNReal

namespace ElboimSly.Cyclic

variable {d : ℕ} {β : ℝ} [Fact (0 < β)] {ν : Measure (RingSpace d β)}

/-- The edges containing `z`. -/
def Ez (d : ℕ) (z : Fin d → ℤ) : Set (Edge d) := {e | e.Mem z}

theorem Ez_finite (z : Fin d → ℤ) : (Ez d z).Finite := edgesAt_finite z

/-- The next ring time at `z`. -/
noncomputable def stepT (ν : Measure (RingSpace d β)) (z : Fin d → ℤ) (t : ℝ) : ℝ :=
  nxtJ ν (Ez d z) t

/-- `w` is the other end of the edge at `z` ringing at the next ring time. -/
def StepP (ν : Measure (RingSpace d β)) (z : Fin d → ℤ) (t : ℝ) (w : Fin d → ℤ) : Prop :=
  ∃ e ∈ Ez d z, e.1 = s(z, w) ∧ HasRing ν {e} ∧ nxt ν {e} t = nxt ν (Ez d z) t

open scoped Classical in
/-- The position after the jump. -/
noncomputable def stepW (ν : Measure (RingSpace d β)) (z : Fin d → ℤ) (t : ℝ) : Fin d → ℤ :=
  if HasRing ν (Ez d z) then Classical.epsilon (StepP ν z t) else z

omit [Fact (0 < β)] in
theorem stepW_of_not (z : Fin d → ℤ) (t : ℝ) (h : ¬ HasRing ν (Ez d z)) : stepW ν z t = z := by
  simp [stepW, h]

theorem nxt_single_eq (hν : Good ν) (z : Fin d → ℤ) (t : ℝ) (hH : HasRing ν (Ez d z))
    {e : Edge d} (he : e ∈ Ez d z) (hr : Rings ν e (nxt ν (Ez d z) t)) :
    nxt ν {e} t = nxt ν (Ez d z) t := by
  have hn : Nice ν := good_nice hν
  have hl := isLeast_nxt hn (Ez_finite z) t hH
  have hle := isLeast_nxt hn (Set.finite_singleton e) t ⟨_, e, rfl, hr⟩
  apply le_antisymm
  · exact hle.2 ⟨hl.1.1, e, rfl, hr⟩
  · obtain ⟨e', he', hr'⟩ := hle.1.2
    rw [Set.mem_singleton_iff] at he'
    subst he'
    exact hl.2 ⟨hle.1.1, e', he, hr'⟩

theorem stepW_eq_iff (hν : Good ν) (z : Fin d → ℤ) (t : ℝ) (hH : HasRing ν (Ez d z))
    (w : Fin d → ℤ) : stepW ν z t = w ↔ StepP ν z t w := by
  have hn : Nice ν := good_nice hν
  have hl := isLeast_nxt hn (Ez_finite z) t hH
  obtain ⟨e, he, hr⟩ := hl.1.2
  obtain ⟨w0, hw0⟩ := Sym2.mem_iff_exists.mp (show z ∈ e.1 from he)
  have key : StepP ν z t w0 :=
    ⟨e, he, hw0, ⟨_, e, rfl, hr⟩, nxt_single_eq hν z t hH he hr⟩
  have hex : ∃ w, StepP ν z t w := ⟨w0, key⟩
  have hsp := Classical.epsilon_spec hex
  have huniq : ∀ w1 w2, StepP ν z t w1 → StepP ν z t w2 → w1 = w2 := by
    rintro w1 w2 ⟨e1, he1, hs1, hH1, hn1⟩ ⟨e2, he2, hs2, hH2, hn2⟩
    have r1 : Rings ν e1 (nxt ν (Ez d z) t) := by
      rw [← hn1]
      obtain ⟨e', he', hr'⟩ := (isLeast_nxt hn (Set.finite_singleton e1) t hH1).1.2
      rw [Set.mem_singleton_iff] at he'; subst he'; exact hr'
    have r2 : Rings ν e2 (nxt ν (Ez d z) t) := by
      rw [← hn2]
      obtain ⟨e', he', hr'⟩ := (isLeast_nxt hn (Set.finite_singleton e2) t hH2).1.2
      rw [Set.mem_singleton_iff] at he'; subst he'; exact hr'
    have := edge_unique hν r1 r2
    subst this
    exact Sym2.congr_right.mp (hs1.symm.trans hs2)
  have hW : stepW ν z t = Classical.epsilon (StepP ν z t) := by simp [stepW, hH]
  rw [hW]
  exact ⟨fun h => h ▸ hsp, fun h => huniq _ _ hsp h⟩

/-- On good configurations, `(stepT, stepW)` satisfies the properties of `exists_step_fwd`. -/
theorem step_spec (hν : Good ν) (z : Fin d → ℤ) (t : ℝ) :
    t < stepT ν z t ∧ (∀ u, t < u → u < stepT ν z t → ¬ RingAt ν z u) ∧
      SwapRule ν (stepT ν z t) z (stepW ν z t) ∧
      ((∃ e : Edge d, e.1 = s(z, stepW ν z t) ∧ Rings ν e (stepT ν z t)) ∨
        (stepT ν z t = t + 1 ∧ stepW ν z t = z ∧ ∀ u, ¬ RingAt ν z u)) := by
  have hn : Nice ν := good_nice hν
  by_cases hH : HasRing ν (Ez d z)
  · have hl := isLeast_nxt hn (Ez_finite z) t hH
    have hT : stepT ν z t = nxt ν (Ez d z) t := nxtJ_of_hasRing t hH
    obtain ⟨e, he, hr⟩ := hl.1.2
    obtain ⟨w0, hw0⟩ := Sym2.mem_iff_exists.mp (show z ∈ e.1 from he)
    have hW : stepW ν z t = w0 :=
      (stepW_eq_iff hν z t hH w0).mpr ⟨e, he, hw0, ⟨_, e, rfl, hr⟩, nxt_single_eq hν z t hH he hr⟩
    rw [hT, hW]
    refine ⟨hl.1.1, fun u hu hu' hru => ?_, swapRule_of_edge hν e hw0 hr, Or.inl ⟨e, hw0, hr⟩⟩
    exact absurd (hl.2 ⟨hu, hru⟩) (not_le.mpr hu')
  · have hT : stepT ν z t = t + 1 := nxtJ_of_not_hasRing t hH
    have hno : ∀ u, ¬ RingAt ν z u := fun u hu => hH ⟨u, hu⟩
    rw [hT, stepW_of_not z t hH]
    exact ⟨by linarith, fun u _ _ => hno u, swapRule_self (hno _), Or.inr ⟨rfl, rfl, hno⟩⟩

/-- The iterated jump sequence. -/
noncomputable def fseq (ν : Measure (RingSpace d β)) (x : Fin d → ℤ) (a : ℝ) :
    ℕ → ℝ × (Fin d → ℤ)
  | 0 => (a, x)
  | k + 1 => (stepT ν (fseq ν x a k).2 (fseq ν x a k).1, stepW ν (fseq ν x a k).2 (fseq ν x a k).1)

theorem fwdSeq_fseq (hν : Good ν) (x : Fin d → ℤ) (a : ℝ) :
    FwdSeq ν a x (fun k => (fseq ν x a k).1) (fun k => (fseq ν x a k).2) := by
  refine ⟨rfl, rfl, fun k => (step_spec hν _ _).1, fun k => (step_spec hν _ _).2.1, fun k => ?_,
    fun k => ?_⟩
  · exact (step_spec hν _ _).2.2.1
  · rcases (step_spec hν (fseq ν x a k).2 (fseq ν x a k).1).2.2.2 with h | ⟨h1, h2, h3⟩
    · exact Or.inl h
    · exact Or.inr ⟨h1, h2, h3⟩

end ElboimSly.Cyclic

end
