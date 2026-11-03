/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycSchemeEnvMark
public import ElboimSly.Foundations.Cyclic.CycSchemeEnvAe
public import ElboimSly.Foundations.Cyclic.CycSchemeEnvUnb
public import Mathlib

/-!
# The environment scheme (b): trajectories of states, non-explosion of a walk

The environment scheme (b), non-explosion. A `Traj` is a sequence of states with
`S (j+1) = upd (S j) (O j)` and good outcomes at unfinished steps. `Traj.inv` gives the invariant
`Inv` for all `j`; `Traj.unbounded`: if walk `k` is the current unfinished walk at all steps
`j ≥ j0`, its current time is unbounded (the steps end at jumps of the environment path or multiples
of `β`, and these are locally finite).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic
namespace CycSchemeEnv
variable {I : Type*} [MeasurableSpace I] [Countable I] [MeasurableSingletonClass I] {d : ℕ} {β : ℝ}
  [Fact (0 < β)] {P : CycPlan I d β} {ν : Measure (I × RingSpace d β)} {sc : ℝ≥0∞}

omit [Countable I] [MeasurableSingletonClass I] [Fact (0 < β)] in
theorem EnvAt.k_unique {k k' : ℕ} {r r' : ℝ≥0} {ρ : CycRec I d} (h : EnvAt P ν k r ρ)
    (h' : EnvAt P ν k' r' ρ) : k = k' := by
  have := h.rec_eq.symm.trans h'.rec_eq
  have h2 := congrArg (fun x : CycRec I d => x.num) this
  simp only [CycRec.num] at h2
  exact_mod_cast Nat.succ_injective (Nat.cast_injective (R := ℕ∞) h2)

omit [Countable I] [MeasurableSingletonClass I] in
omit [Fact (0 < β)] in
theorem EnvAt.r_unique {k : ℕ} {r r' : ℝ≥0} {ρ : CycRec I d} (h : EnvAt P ν k r ρ)
    (h' : EnvAt P ν k r' ρ) : r = r' := by
  have h1 := h.len_cur false
  have h2 := h'.len_cur false
  rw [h1] at h2
  exact_mod_cast h2

/-- A trajectory of states: `S (j+1) = upd (S j) (O j)`, with good outcomes at unfinished steps. -/
structure Traj (P : CycPlan I d β) (sc : ℝ≥0∞) (ν : Measure (I × RingSpace d β)) where
  S : ℕ → CycScheme.State I d
  O : ℕ → Outcome (CycS I d β)
  step : ∀ j, S (j + 1) = CycScheme.upd P sc (S j) (O j)
  good : ∀ j, (S j).2 = false → StepGood P sc ν (S j).1 (O j)

variable (T : Traj P sc ν)

theorem Traj.inv (hν : CycGood ν) (hK : 0 < P.K) (h0 : T.S 0 = CycScheme.init P) :
    ∀ j, Inv P sc ν (T.S j) := by
  intro j
  induction j with
  | zero => rw [h0]; exact inv_init hν hK
  | succ j ih =>
    rw [T.step]
    exact inv_upd hν _ ih (T.good j)

theorem Traj.unbounded (hν : CycGood ν) {k : ℕ} {j0 : ℕ}
    (hcur : ∀ j, j0 ≤ j → ∃ r, EnvAt P ν k r (T.S j).1 ∧ (T.S j).2 = false) :
    ∀ M : ℝ≥0, ∃ j, j0 ≤ j ∧ ∃ r, EnvAt P ν k r (T.S j).1 ∧ M < r := by
  choose! r hr hf using hcur
  have hnext : ∀ j, j0 ≤ j → r (j + 1) = r j + CycScheme.sStar P sc (T.S j) (T.O j) ∧
      0 < CycScheme.sStar P sc (T.S j) (T.O j) ∧
      (r j + CycScheme.sStar P sc (T.S j) (T.O j) ∈ CDisc (pth P ν k).1.fn ∨
        ∃ m : ℕ, ((r j + CycScheme.sStar P sc (T.S j) (T.O j) : ℝ≥0) : ℝ) = β * m) := by
    intro j hj
    have hSj : T.S j = ((T.S j).1, false) := Prod.ext rfl (hf j hj)
    have hg := T.good j (hf j hj)
    have e : T.S (j + 1) = CycScheme.upd P sc ((T.S j).1, false) (T.O j) := by
      rw [T.step]; exact congrArg (fun x => CycScheme.upd P sc x (T.O j)) hSj
    have h1 := hr j hj
    have h2 := hr (j + 1) (Nat.le_succ_of_le hj)
    have h2f := hf (j + 1) (Nat.le_succ_of_le hj)
    rw [hSj] at ⊢
    have hs0 : ¬ CycScheme.stops P sc ((T.S j).1, false) (T.O j) := by
      intro hs
      by_cases hK : ((k + 1 : ℕ) : ℕ∞) < P.K
      · obtain ⟨-, h3⟩ := upd_stop_next hν h1 hg hs hK
        rw [e] at h2
        have := h2.k_unique h3
        omega
      · rw [e, upd_stop_end hν h1 hg hs hK] at h2f
        exact absurd h2f (by simp)
    obtain ⟨h3, h4⟩ := upd_notStop hν h1 hg hs0
    rw [e] at h2 h2f
    have hfl : ((CycScheme.sStar P sc ((T.S j).1, false) (T.O j) : ℝ≥0) : ℝ≥0∞) ≠
        CycScheme.hGl sc (T.S j).1 (CycScheme.cur P ((T.S j).1, false)) := by
      intro hh
      rw [h4] at h2f
      simp [hh] at h2f
    have hr' := h2.r_unique h3
    obtain ⟨hpos, hmark⟩ := step_marked hν h1 hg hs0 hfl
    exact ⟨hr', hpos, hmark⟩
  intro M
  set q : ℕ → ℝ≥0 := fun i => r (j0 + i + 1) with hq
  have hmono : StrictMono q := by
    refine strictMono_nat_of_lt_succ fun i => ?_
    have := hnext (j0 + i + 1) (by omega)
    show r (j0 + i + 1) < r (j0 + (i + 1) + 1)
    rw [show j0 + (i + 1) + 1 = j0 + i + 1 + 1 by ring, this.1]
    exact lt_add_of_pos_right _ this.2.1
  have hmark : ∀ i, q i ∈ CDisc (pth P ν k).1.fn ∨ ∃ m : ℕ, (q i : ℝ) = β * m := by
    intro i
    have := hnext (j0 + i) (by omega)
    have e : q i = r (j0 + i) + CycScheme.sStar P sc (T.S (j0 + i)) (T.O (j0 + i)) := this.1
    rw [e]
    exact this.2.2
  obtain ⟨i, hi⟩ := unbounded_of_marked (pth P ν k).1 q hmono hmark M
  exact ⟨j0 + i + 1, by omega, q i, hr _ (by omega), hi⟩

end CycSchemeEnv
end ElboimSly.Cyclic

end
