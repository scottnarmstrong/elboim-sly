/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycSchemeEnvWalk
public import ElboimSly.Foundations.Cyclic.CycSchemeEnvExt
public import ElboimSly.Foundations.Cyclic.CycSchemeEnvFinalNth
public import Mathlib

/-!
# The environment scheme (b): the scheme reaches every walk of the recursion

The environment scheme (b), convergence. For `s_∘ = ∞`: the records of the scheme extend each
other (`Traj.extends`), and every walk that the recursion of world-lines of a plan; joint exploration filtration (a) appends is reached by
the scheme (`Traj.reach`): a walk of finite stopping length cannot stay current forever, by the
non-explosion of its steps (`Traj.unbounded`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic
namespace CycSchemeEnv
variable {I : Type*} [MeasurableSpace I] [Countable I] [MeasurableSingletonClass I] {d : ℕ} {β : ℝ}
  [Fact (0 < β)] {P : CycPlan I d β} {ν : Measure (I × RingSpace d β)} {sc : ℝ≥0∞}
variable (T : Traj P sc ν)

theorem Traj.extends (hν : CycGood ν) (hK : 0 < P.K) (h0 : T.S 0 = CycScheme.init P) (j : ℕ) :
    (T.S j).1.Extends (T.S (j + 1)).1 := by
  rcases T.inv hν hK h0 j with ⟨hf, k, r, h⟩ | ⟨ht, rest⟩
  · have hSj : T.S j = ((T.S j).1, false) := Prod.ext rfl hf
    have hg := T.good j hf
    have e : T.S (j + 1) = CycScheme.upd P sc ((T.S j).1, false) (T.O j) := by
      rw [T.step]; exact congrArg (fun x => CycScheme.upd P sc x (T.O j)) hSj
    rw [e]
    exact extends_upd hν h hg
  · have : CycScheme.upd P sc (T.S j) (T.O j) = T.S j := by
      unfold CycScheme.upd
      rw [ite_eq_left ht]
    rw [T.step, this]
    exact CycRec.Extends.refl _

/-- With `s_∘ = ∞` the end flag is never set by the horizon: an unfinished walk that does not stop
leaves the state unfinished. -/
theorem Traj.reach_next (hν : CycGood ν) (hsc : sc = ⊤) {k j0 : ℕ}
    (hcur : ∃ r, EnvAt P ν k r (T.S j0).1 ∧ (T.S j0).2 = false)
    (hfin : sInf (cand P ν k) < ⊤) (hK : ((k + 1 : ℕ) : ℕ∞) < P.K) :
    ∃ j, j0 ≤ j ∧ ∃ r, EnvAt P ν (k + 1) r (T.S j).1 ∧ (T.S j).2 = false := by
  have hgl : ∀ {k' : ℕ} {r' : ℝ≥0} {ρ' : CycRec I d}, EnvAt P ν k' r' ρ' →
      CycScheme.hGl sc ρ' (CycScheme.cur P (ρ', false)) = ⊤ := fun {k' r' ρ'} h' => by
    rw [hsc]; exact hGl_top h'
  by_contra hne
  push Not at hne
  -- all later states are unfinished states of walk `k`
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
      by_cases hs : CycScheme.stops P sc ((T.S j).1, false) (T.O j)
      · exfalso
        obtain ⟨h1, h2⟩ := upd_stop_next hν h hg hs hK
        rw [← e] at h1 h2
        exact hne (j + 1) (Nat.le_succ_of_le hj) 0 h2 h1
      · obtain ⟨h1, h2⟩ := upd_notStop hν h hg hs
        rw [← e] at h1 h2
        refine ⟨_, h1, ?_⟩
        rw [h2]
        simp only [decide_eq_false_iff_not]
        rw [hgl h]
        exact ENNReal.coe_ne_top
  obtain ⟨j, hj, r, hr, hrM⟩ := T.unbounded hν hall (sInf (cand P ν k)).toNNReal
  have h1 := hr.le_sInf
  have hfin' : sInf (cand P ν k) ≠ ⊤ := hfin.ne
  have : (sInf (cand P ν k)).toNNReal < r := hrM
  have h2 : ((sInf (cand P ν k)).toNNReal : ℝ≥0∞) < r := by exact_mod_cast this
  rw [ENNReal.coe_toNNReal hfin'] at h2
  exact absurd h1 (not_le.2 h2)

omit [Countable I] [MeasurableSingletonClass I] in
omit [Fact (0 < β)] in
theorem E_len (k : ℕ) : (P.E (rule P ν) k).len = sInf (cand P ν k) := by
  rw [E_eq]
  exact CPath.cut_len _ _

/-- Every walk that the recursion appends is reached by the scheme (for `s_∘ = ∞`). -/
theorem Traj.reach (hν : CycGood ν) (hK : 0 < P.K) (h0 : T.S 0 = CycScheme.init P)
    (hsc : sc = ⊤) :
    ∀ k : ℕ, P.Cont (rule P ν) k →
      ∃ j, ∃ r, EnvAt P ν k r (T.S j).1 ∧ (T.S j).2 = false := by
  intro k
  induction k with
  | zero =>
    intro _
    exact ⟨0, 0, by rw [h0]; exact envAt_init hν hK, by rw [h0]; rfl⟩
  | succ k ih =>
    intro hc
    obtain ⟨j0, r0, h0', hf0⟩ := ih (CycPlan.Cont.anti P (rule P ν) (Nat.le_succ k) hc)
    have hfin : sInf (cand P ν k) < ⊤ := by
      have := hc.2 k (Nat.lt_succ_self k)
      rwa [E_len] at this
    obtain ⟨j, -, r, hr, hrf⟩ := T.reach_next hν hsc ⟨r0, h0', hf0⟩ hfin (by exact_mod_cast hc.1)
    exact ⟨j, r, hr, hrf⟩

end CycSchemeEnv
end ElboimSly.Cyclic

end
