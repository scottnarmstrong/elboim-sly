/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycSchemeEnvReach
public import Mathlib

/-!
# The environment scheme (b): convergence of one coordinate of the records

The environment scheme (b), convergence (`s_∘ = ∞`). For a walk `k` appended by the recursion:
if its stopping length is infinite, its current time in the records `ρ_j` is eventually larger than
any `M` (`Traj.case_top`); if it is finite, the entry `k` of `ρ_j` is eventually exactly the
environment world-line `E k` (`Traj.case_fin`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic
namespace CycSchemeEnv
variable {I : Type*} [MeasurableSpace I] [Countable I] [MeasurableSingletonClass I] {d : ℕ} {β : ℝ}
  [Fact (0 < β)] {P : CycPlan I d β} {ν : Measure (I × RingSpace d β)} {sc : ℝ≥0∞}
variable (T : Traj P sc ν)

omit [Countable I] [MeasurableSingletonClass I] [Fact (0 < β)] in
/-- Entry `k` of an invariant state is an initial piece of the environment world-line `E k`. -/
theorem nth_of_inv {st : CycScheme.State I d} (hI : Inv P sc ν st) {k : ℕ} {e : CycEntry I d}
    (h : st.1.nth k = some e) :
    ∃ ρ' : ℝ≥0∞, ρ' ≤ sInf (cand P ν k) ∧ e = (dat P ν k, (pth P ν k).cut ρ') := by
  obtain ⟨k', r, hrec, -, -, hle⟩ := hI.rec_form
  have hs : st.1 = shape P ν k' r := hrec
  rw [hs] at h
  rcases lt_trichotomy k k' with hk | rfl | hk
  · rw [nth_shape_lt k' r hk] at h
    cases h
    exact ⟨_, le_rfl, E_eq P ν k⟩
  · rw [nth_shape_self] at h
    cases h
    exact ⟨_, hle, rfl⟩
  · rw [nth_shape_gt k' r hk] at h
    exact absurd h (by simp)

theorem Traj.stay (hν : CycGood ν) (hsc : sc = ⊤) {k j0 : ℕ}
    (hcur : ∃ r, EnvAt P ν k r (T.S j0).1 ∧ (T.S j0).2 = false)
    (htop : sInf (cand P ν k) = ⊤) :
    ∀ j, j0 ≤ j → ∃ r, EnvAt P ν k r (T.S j).1 ∧ (T.S j).2 = false := by
  have hgl : ∀ {k' : ℕ} {r' : ℝ≥0} {ρ' : CycRec I d}, EnvAt P ν k' r' ρ' →
      CycScheme.hGl sc ρ' (CycScheme.cur P (ρ', false)) = ⊤ := fun {k' r' ρ'} h' => by
    rw [hsc]; exact hGl_top h'
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
      have := sInf_cand_eq hν h hg hs
      rw [htop] at this
      exact ENNReal.top_ne_coe this
    · obtain ⟨h1, h2⟩ := upd_notStop hν h hg hs
      rw [← e] at h1 h2
      refine ⟨_, h1, ?_⟩
      rw [h2]
      simp only [decide_eq_false_iff_not]
      rw [hgl h]
      exact ENNReal.coe_ne_top

/-- A walk of finite stopping length stops: afterwards the state has an entry `k + 1`, or it is the
finished state `(ideal (k+1), true)`. -/
theorem Traj.exit (hν : CycGood ν) (hsc : sc = ⊤) {k j0 : ℕ}
    (hcur : ∃ r, EnvAt P ν k r (T.S j0).1 ∧ (T.S j0).2 = false)
    (hfin : sInf (cand P ν k) < ⊤) :
    ∃ j, j0 ≤ j ∧ ((∃ r, EnvAt P ν (k + 1) r (T.S j).1 ∧ (T.S j).2 = false) ∨
      ((T.S j).1 = Sum.inl ⟨k + 1, P.ideal (rule P ν) (k + 1)⟩ ∧ (T.S j).2 = true)) := by
  by_contra hne
  push Not at hne
  have hgl : ∀ {k' : ℕ} {r' : ℝ≥0} {ρ' : CycRec I d}, EnvAt P ν k' r' ρ' →
      CycScheme.hGl sc ρ' (CycScheme.cur P (ρ', false)) = ⊤ := fun {k' r' ρ'} h' => by
    rw [hsc]; exact hGl_top h'
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
        by_cases hK : ((k + 1 : ℕ) : ℕ∞) < P.K
        · obtain ⟨h1, h2⟩ := upd_stop_next hν h hg hs hK
          rw [← e] at h1 h2
          have := (hne (j + 1) (Nat.le_succ_of_le hj)).1 0
          exact this h2 h1
        · have := upd_stop_end hν h hg hs hK
          rw [← e] at this
          exact (hne (j + 1) (Nat.le_succ_of_le hj)).2 (congrArg Prod.fst this)
            (congrArg Prod.snd this)
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
  have h2 : ((sInf (cand P ν k)).toNNReal : ℝ≥0∞) < r := by exact_mod_cast hrM
  rw [ENNReal.coe_toNNReal hfin'] at h2
  exact absurd h1 (not_le.2 h2)

omit [Countable I] [MeasurableSingletonClass I] in
omit [Fact (0 < β)] in
theorem nth_ideal_succ_self (k : ℕ) :
    CycRec.nth (Sum.inl ⟨k + 1, P.ideal (rule P ν) (k + 1)⟩ : CycRec I d) k =
      some (P.E (rule P ν) k) := by
  simp only [CycRec.nth, dite_eq_left (Nat.lt_succ_self k)]
  congr 1
  exact P.ideal_apply (rule P ν) (k + 1) ⟨k, Nat.lt_succ_self k⟩

/-- Case `ℓ_k = ∞`: the current time of walk `k` is eventually larger than any `M`. -/
theorem Traj.case_top (hν : CycGood ν) (hK : 0 < P.K) (h0 : T.S 0 = CycScheme.init P)
    (hsc : sc = ⊤) {k : ℕ} (hc : P.Cont (rule P ν) k) (htop : sInf (cand P ν k) = ⊤) (M : ℝ≥0) :
    ∃ J, ∀ j, J ≤ j → ∃ r : ℝ≥0, M < r ∧
      (T.S j).1.nth k = some (dat P ν k, (pth P ν k).cut (r : ℝ≥0∞)) := by
  obtain ⟨j0, r0, h0', hf0⟩ := T.reach hν hK h0 hsc k hc
  have hstay := T.stay hν hsc ⟨r0, h0', hf0⟩ htop
  obtain ⟨j1, hj1, r1, hr1, hM⟩ := T.unbounded hν hstay M
  refine ⟨j1, fun j hj => ?_⟩
  have hmono : ∀ j, j1 ≤ j → ∃ r : ℝ≥0, M < r ∧ EnvAt P ν k r (T.S j).1 := by
    intro j hj
    induction j, hj using Nat.le_induction with
    | base => exact ⟨r1, hM, hr1⟩
    | succ j hj ih =>
      obtain ⟨r, hMr, hr⟩ := ih
      obtain ⟨r', hr', -⟩ := hstay (j + 1) (by omega)
      refine ⟨r', lt_of_lt_of_le hMr ?_, hr'⟩
      have hext := T.extends hν hK h0 j
      obtain ⟨e', he', -, hp⟩ := hext k (dat P ν k, (pth P ν k).cut (r : ℝ≥0∞)) (by
        rw [hr.eq_shape]; exact nth_shape_self k r)
      rw [hr'.eq_shape, nth_shape_self] at he'
      cases he'
      have h1 : ((r : ℝ≥0) : ℝ≥0∞) ≤ (r' : ℝ≥0∞) := by
        have := hp.1
        change ((pth P ν k).1.cut (r : ℝ≥0∞)).len ≤ ((pth P ν k).1.cut (r' : ℝ≥0∞)).len at this
        rwa [CPath.cut_len, CPath.cut_len] at this
      exact_mod_cast h1
  obtain ⟨r, hMr, hr⟩ := hmono j hj
  exact ⟨r, hMr, by rw [hr.eq_shape]; exact nth_shape_self k r⟩

/-- Case `ℓ_k < ∞`: the entry `k` is eventually `E k`. -/
theorem Traj.case_fin (hν : CycGood ν) (hK : 0 < P.K) (h0 : T.S 0 = CycScheme.init P)
    (hsc : sc = ⊤) {k : ℕ} (hc : P.Cont (rule P ν) k) (hfin : sInf (cand P ν k) < ⊤) :
    ∃ J, ∀ j, J ≤ j → (T.S j).1.nth k = some (P.E (rule P ν) k) := by
  obtain ⟨j0, r0, h0', hf0⟩ := T.reach hν hK h0 hsc k hc
  obtain ⟨j1, hj1, hcase⟩ := T.exit hν hsc ⟨r0, h0', hf0⟩ hfin
  have hpers : ∀ j, j1 ≤ j → ((T.S j).1.nth (k + 1)).isSome ∨
      ((T.S j).1 = Sum.inl ⟨k + 1, P.ideal (rule P ν) (k + 1)⟩ ∧ (T.S j).2 = true) := by
    intro j hj
    induction j, hj using Nat.le_induction with
    | base =>
      rcases hcase with ⟨r, hr, -⟩ | h
      · left; rw [hr.eq_shape, nth_shape_self]; rfl
      · right; exact h
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

end CycSchemeEnv
end ElboimSly.Cyclic

end
