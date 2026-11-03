/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycSchemeEnvRFin
public import Mathlib

/-!
# The environment scheme (b), finite horizon: eventual entries of the records

The environment scheme (b), convergence for finite `s_∘`. For a walk `k` that the scheme
reaches (`Cont k`, `Λ_k ≤ s_∘`):

* `Traj.nth_eventually_stop`: if `Λ_k + ℓ_k ≤ s_∘` then entry `k` of the records is eventually `E k`;
* `Traj.nth_eventually_cut`: if `s_∘ < Λ_k + ℓ_k` then entry `k` is eventually the initial piece of
  the environment world-line at time `r = s_∘ - Λ_k` (`Traj.cutoff_fin`: the horizon ends the scheme).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic
namespace CycSchemeEnv
variable {I : Type*} [MeasurableSpace I] [Countable I] [MeasurableSingletonClass I] {d : ℕ} {β : ℝ}
  [Fact (0 < β)] {P : CycPlan I d β} {ν : Measure (I × RingSpace d β)} {sc : ℝ≥0∞}
variable (T : Traj P sc ν)

/-- A walk with `s_∘ < Λ_k + ℓ_k` ends the scheme at the horizon. -/
theorem Traj.cutoff_fin (hν : CycGood ν) (hK : 0 < P.K) (h0 : T.S 0 = CycScheme.init P) {k j0 : ℕ}
    (hcur : ∃ r, EnvAt P ν k r (T.S j0).1 ∧ (T.S j0).2 = false)
    (hbad : sc < lam P ν k + sInf (cand P ν k)) :
    ∃ j, j0 ≤ j ∧ ∃ r : ℝ≥0, lam P ν k + r = sc ∧ (T.S j).1 = shape P ν k r ∧
      (T.S j).2 = true := by
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
      have hsb := step_bud hν h hg hb
      by_cases hs : CycScheme.stops P sc ((T.S j).1, false) (T.O j)
      · exfalso
        have := sInf_cand_eq hν h hg hs
        rw [this] at hbad
        exact absurd hsb (not_le.2 hbad)
      · obtain ⟨h1, h2⟩ := upd_notStop hν h hg hs
        refine ⟨_, by rw [← e] at h1; exact h1, ?_⟩
        by_contra hflag
        have hflag' : (T.S (j + 1)).2 = true := by simpa using hflag
        refine hne ⟨j + 1, Nat.le_succ_of_le hj, r + CycScheme.sStar P sc ((T.S j).1, false) (T.O j),
          ?_, by rw [e]; exact h1.eq_shape, hflag'⟩
        rw [e, h2] at hflag'
        have hd := of_decide_eq_true hflag'
        rw [h.hGl_eq] at hd
        rw [ENNReal.coe_add, ← add_assoc, hd]
        exact add_tsub_cancel_of_le hb
  have hsc : sc ≠ ⊤ := ne_top_of_lt hbad
  obtain ⟨j, hj, r, hr, hrM⟩ := T.unbounded hν hall sc.toNNReal
  have hb := (T.bud hν hK h0 j).1 (hall j hj).choose_spec.2 k r hr
  have h2 : (sc.toNNReal : ℝ≥0∞) < r := by exact_mod_cast hrM
  rw [ENNReal.coe_toNNReal hsc] at h2
  exact absurd (le_add_self.trans hb) (not_le.2 h2)

/-- Entry `k` is eventually `E k` if the walk stops before the horizon. -/
theorem Traj.nth_eventually_stop (hν : CycGood ν) (hK : 0 < P.K) (h0 : T.S 0 = CycScheme.init P)
    {k : ℕ} (hc : P.Cont (rule P ν) k) (hl : lam P ν k ≤ sc)
    (hfin : sInf (cand P ν k) < ⊤) (hbud : lam P ν k + sInf (cand P ν k) ≤ sc) :
    ∃ J, ∀ j, J ≤ j → (T.S j).1.nth k = some (P.E (rule P ν) k) := by
  obtain ⟨j0, r0, h0', hf0⟩ := T.reach_fin hν hK h0 k hc hl
  obtain ⟨j1, hj1, hcase⟩ := T.exit_fin hν hK h0 ⟨r0, h0', hf0⟩ hfin hbud
  have hpers : ∀ j, j1 ≤ j → ((T.S j).1.nth (k + 1)).isSome ∨
      ((T.S j).1 = Sum.inl ⟨k + 1, P.ideal (rule P ν) (k + 1)⟩ ∧ (T.S j).2 = true) := by
    intro j hj
    induction j, hj using Nat.le_induction with
    | base =>
      rcases hcase with ⟨r, hr, -⟩ | ⟨h1, h2, -⟩
      · left; rw [hr.eq_shape, nth_shape_self]; rfl
      · right; exact ⟨h1, h2⟩
    | succ j hj ih =>
      rcases ih with hsome | ⟨hrec, hfl⟩
      · left
        obtain ⟨e, he⟩ := Option.isSome_iff_exists.1 hsome
        obtain ⟨e', he', -⟩ := T.extends hν hK h0 j (k + 1) e he
        rw [he']; rfl
      · right
        have : CycScheme.upd P sc (T.S j) (T.O j) = T.S j := by
          unfold CycScheme.upd
          rw [ite_eq_left hfl]
        rw [T.step, this]
        exact ⟨hrec, hfl⟩
  refine ⟨j1, fun j hj => ?_⟩
  rcases hpers j hj with hsome | ⟨hrec, -⟩
  · obtain ⟨e, he⟩ := Option.isSome_iff_exists.1 hsome
    obtain ⟨k', r, hrec, -, -, -⟩ := (T.inv hν hK h0 j).rec_form
    have hs : (T.S j).1 = shape P ν k' r := hrec
    rw [hs] at he ⊢
    rcases lt_trichotomy (k + 1) k' with hk | rfl | hk
    · exact nth_shape_lt k' r (by omega)
    · exact nth_shape_lt (k + 1) r (Nat.lt_succ_self k)
    · rw [nth_shape_gt k' r hk] at he
      exact absurd he (by simp)
  · rw [hrec]; exact nth_ideal_succ_self k

/-- Entry `k` is eventually the initial piece at time `s_∘ - Λ_k` if the horizon cuts the walk. -/
theorem Traj.nth_eventually_cut (hν : CycGood ν) (hK : 0 < P.K) (h0 : T.S 0 = CycScheme.init P)
    {k : ℕ} (hc : P.Cont (rule P ν) k) (hl : lam P ν k ≤ sc)
    (hbad : sc < lam P ν k + sInf (cand P ν k)) :
    ∃ r : ℝ≥0, lam P ν k + r = sc ∧ ∃ J, ∀ j, J ≤ j →
      (T.S j).1.nth k = some (dat P ν k, (pth P ν k).cut (r : ℝ≥0∞)) := by
  obtain ⟨j0, r0, h0', hf0⟩ := T.reach_fin hν hK h0 k hc hl
  obtain ⟨j1, hj1, r, hr, hrec, hfl⟩ := T.cutoff_fin hν hK h0 ⟨r0, h0', hf0⟩ hbad
  refine ⟨r, hr, j1, fun j hj => ?_⟩
  rw [T.stay_finished hfl j hj, hrec]
  exact nth_shape_self k r

end CycSchemeEnv
end ElboimSly.Cyclic

end
