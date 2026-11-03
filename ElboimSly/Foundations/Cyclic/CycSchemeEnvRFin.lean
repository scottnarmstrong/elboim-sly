/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycSchemeEnvBud
public import ElboimSly.Foundations.Cyclic.CycSchemeEnvReach
public import ElboimSly.Foundations.Cyclic.CycSchemeEnvConv
public import Mathlib

/-!
# The environment scheme (b), finite horizon: reaching the walks of the recursion

The environment scheme (b), convergence for finite `s_∘`.

* `Traj.exit_fin`: a walk `k` with `Λ_k + ℓ_k ≤ s_∘` stops, so the scheme moves on to walk `k + 1`
  (or ends with the plan); the horizon never ends it earlier, since the infimum `ℓ_k` is attained.
* `Traj.reach_fin`: every walk `k` of the recursion with `Λ_k ≤ s_∘` is reached by the scheme.
* `Traj.cutoff_fin`: a walk `k` with `Λ_k + ℓ_k > s_∘` ends the scheme, with the record
  `shape k r` where `Λ_k + r = s_∘`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic
namespace CycSchemeEnv
variable {I : Type*} [MeasurableSpace I] [Countable I] [MeasurableSingletonClass I] {d : ℕ} {β : ℝ}
  [Fact (0 < β)] {P : CycPlan I d β} {ν : Measure (I × RingSpace d β)} {sc : ℝ≥0∞}
variable (T : Traj P sc ν)

theorem upd_flag_false {k : ℕ} {r : ℝ≥0} {ρ : CycRec I d} {o : Outcome (CycS I d β)}
    (hν : CycGood ν) (h : EnvAt P ν k r ρ) (hg : StepGood P sc ν ρ o)
    (hns : ¬ CycScheme.stops P sc (ρ, false) o) (hb : lam P ν k + r ≤ sc)
    (hfin : sInf (cand P ν k) < ⊤) (hbud : lam P ν k + sInf (cand P ν k) ≤ sc) :
    (CycScheme.upd P sc (ρ, false) o).2 = false := by
  obtain ⟨h1, h2⟩ := upd_notStop hν h hg hns
  rw [h2]
  simp only [decide_eq_false_iff_not]
  intro hEq
  have hlt := lt_sInf_of_not_stops hν h hg hns hfin
  have hfl : lam P ν k + r ≠ ⊤ :=
    ENNReal.add_ne_top.2 ⟨lam_ne_top h.allFin, ENNReal.coe_ne_top⟩
  rw [h.hGl_eq] at hEq
  have hsum : lam P ν k + ((r + CycScheme.sStar P sc (ρ, false) o : ℝ≥0) : ℝ≥0∞) = sc := by
    rw [ENNReal.coe_add, ← add_assoc, hEq]
    exact add_tsub_cancel_of_le hb
  have := ENNReal.add_lt_add_left (lam_ne_top h.allFin) hlt
  rw [hsum] at this
  exact absurd hbud (not_le.2 this)

/-- A walk with `Λ_k + ℓ_k ≤ s_∘` stops: afterwards the state is unfinished at walk `k + 1`, or the
plan ends with `k + 1 ≥ K`. -/
theorem Traj.exit_fin (hν : CycGood ν) (hK : 0 < P.K) (h0 : T.S 0 = CycScheme.init P) {k j0 : ℕ}
    (hcur : ∃ r, EnvAt P ν k r (T.S j0).1 ∧ (T.S j0).2 = false)
    (hfin : sInf (cand P ν k) < ⊤) (hbud : lam P ν k + sInf (cand P ν k) ≤ sc) :
    ∃ j, j0 ≤ j ∧ ((∃ r, EnvAt P ν (k + 1) r (T.S j).1 ∧ (T.S j).2 = false) ∨
      ((T.S j).1 = Sum.inl ⟨k + 1, P.ideal (rule P ν) (k + 1)⟩ ∧ (T.S j).2 = true ∧
        ¬ ((k + 1 : ℕ) : ℕ∞) < P.K)) := by
  by_contra hne
  have hall : ∀ j, j0 ≤ j → ∃ r, EnvAt P ν k r (T.S j).1 ∧ (T.S j).2 = false := by
    intro j hj
    induction j, hj using Nat.le_induction with
    | base => exact hcur
    | succ j hj ih =>
      obtain ⟨r, h, hf⟩ := ih
      have hSj : T.S j = ((T.S j).1, false) := Prod.ext rfl hf
      have hg := T.good j hf
      have e : T.S (j + 1) = CycScheme.upd P sc ((T.S j).1, false) (T.O j) := by
        rw [T.step]; exact congrArg (fun x => CycScheme.upd P sc x (T.O j)) hSj
      have hb := (T.bud hν hK h0 j).1 hf k r h
      by_cases hs : CycScheme.stops P sc ((T.S j).1, false) (T.O j)
      · exfalso
        by_cases hK' : ((k + 1 : ℕ) : ℕ∞) < P.K
        · obtain ⟨h1, h2⟩ := upd_stop_next hν h hg hs hK'
          rw [← e] at h1 h2
          exact hne ⟨j + 1, Nat.le_succ_of_le hj, Or.inl ⟨0, h2, h1⟩⟩
        · have := upd_stop_end hν h hg hs hK'
          rw [← e] at this
          exact hne ⟨j + 1, Nat.le_succ_of_le hj,
            Or.inr ⟨congrArg Prod.fst this, congrArg Prod.snd this, hK'⟩⟩
      · obtain ⟨h1, h2⟩ := upd_notStop hν h hg hs
        have hflag := upd_flag_false hν h hg hs hb hfin hbud
        rw [← e] at h1 hflag
        exact ⟨_, h1, hflag⟩
  obtain ⟨j, hj, r, hr, hrM⟩ := T.unbounded hν hall (sInf (cand P ν k)).toNNReal
  have h1 := hr.le_sInf
  have hfin' : sInf (cand P ν k) ≠ ⊤ := hfin.ne
  have h2 : ((sInf (cand P ν k)).toNNReal : ℝ≥0∞) < r := by exact_mod_cast hrM
  rw [ENNReal.coe_toNNReal hfin'] at h2
  exact absurd h1 (not_le.2 h2)

theorem Traj.reach_next_fin (hν : CycGood ν) (hK : 0 < P.K) (h0 : T.S 0 = CycScheme.init P)
    {k j0 : ℕ} (hcur : ∃ r, EnvAt P ν k r (T.S j0).1 ∧ (T.S j0).2 = false)
    (hfin : sInf (cand P ν k) < ⊤) (hbud : lam P ν k + sInf (cand P ν k) ≤ sc)
    (hK' : ((k + 1 : ℕ) : ℕ∞) < P.K) :
    ∃ j, j0 ≤ j ∧ ∃ r, EnvAt P ν (k + 1) r (T.S j).1 ∧ (T.S j).2 = false := by
  obtain ⟨j, hj, hcase⟩ := T.exit_fin hν hK h0 hcur hfin hbud
  rcases hcase with h | ⟨-, -, hh⟩
  · exact ⟨j, hj, h⟩
  · exact absurd hK' hh

/-- Every walk of the recursion with `Λ_k ≤ s_∘` is reached by the scheme. -/
theorem Traj.reach_fin (hν : CycGood ν) (hK : 0 < P.K) (h0 : T.S 0 = CycScheme.init P) :
    ∀ k : ℕ, P.Cont (rule P ν) k → lam P ν k ≤ sc →
      ∃ j, ∃ r, EnvAt P ν k r (T.S j).1 ∧ (T.S j).2 = false := by
  intro k
  induction k with
  | zero =>
    intro _ _
    exact ⟨0, 0, by rw [h0]; exact envAt_init hν hK, by rw [h0]; rfl⟩
  | succ k ih =>
    intro hc hl
    have hl' : lam P ν k ≤ sc := (lam_mono (Nat.le_succ k)).trans hl
    obtain ⟨j0, r0, h0', hf0⟩ := ih (CycPlan.Cont.anti P (rule P ν) (Nat.le_succ k) hc) hl'
    have hfin : sInf (cand P ν k) < ⊤ := by
      have := hc.2 k (Nat.lt_succ_self k)
      rwa [E_len'] at this
    have hbud : lam P ν k + sInf (cand P ν k) ≤ sc := by
      rw [← E_len', ← lam_succ]; exact hl
    obtain ⟨j, -, r, hr, hrf⟩ := T.reach_next_fin hν hK h0 ⟨r0, h0', hf0⟩ hfin hbud
      (by exact_mod_cast hc.1)
    exact ⟨j, r, hr, hrf⟩

end CycSchemeEnv
end ElboimSly.Cyclic

end
