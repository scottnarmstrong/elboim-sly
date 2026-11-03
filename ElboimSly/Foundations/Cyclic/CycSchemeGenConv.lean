/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycSchemeGenInv
public import ElboimSly.Foundations.Cyclic.CycSchemeEnvConv
public import Mathlib

/-!
# Generic reach and convergence of the records (port of `CycSchemeEnvReach/Conv`)

The environment scheme (b), the driving scheme (c).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic
namespace CycSchemeGen
open ElboimSly.Cyclic.CycSchemeEnv (candAbs unbounded_of_marked)
variable {I : Type*} [MeasurableSpace I] [Countable I] [MeasurableSingletonClass I] {d : ℕ} {β : ℝ}
  [Fact (0 < β)] {P : CycPlan I d β} {rl : PathRule I d} {sc : ℝ≥0∞}

variable (T : GTraj P sc rl)

theorem GTraj.extends (hK : 0 < P.K) (h0 : T.S 0 = CycScheme.init P) (j : ℕ) :
    (T.S j).1.Extends (T.S (j + 1)).1 := by
  rcases T.inv hK h0 j with ⟨hf, k, r, h⟩ | ⟨ht, rest⟩
  · have hSj : T.S j = ((T.S j).1, false) := Prod.ext rfl hf
    have hg := T.good j hf _ _ h
    have e : T.S (j + 1) = CycScheme.upd P sc ((T.S j).1, false) (T.O j) := by
      rw [T.step]; exact congrArg (fun x => CycScheme.upd P sc x (T.O j)) hSj
    rw [e]
    exact extends_upd T.zero h hg
  · have : CycScheme.upd P sc (T.S j) (T.O j) = T.S j := by
      unfold CycScheme.upd
      rw [ite_eq_left ht]
    rw [T.step, this]
    exact CycRec.Extends.refl _

/-- With `s_∘ = ∞` the end flag is never set by the horizon: an unfinished walk that does not stop
leaves the state unfinished. -/
theorem GTraj.reach_next (hsc : sc = ⊤) {k j0 : ℕ}
    (hcur : ∃ r, GAt P rl k r (T.S j0).1 ∧ (T.S j0).2 = false)
    (hfin : sInf (gcand P rl k) < ⊤) (hK : ((k + 1 : ℕ) : ℕ∞) < P.K) :
    ∃ j, j0 ≤ j ∧ ∃ r, GAt P rl (k + 1) r (T.S j).1 ∧ (T.S j).2 = false := by
  have hgl : ∀ {k' : ℕ} {r' : ℝ≥0} {ρ' : CycRec I d}, GAt P rl k' r' ρ' →
      CycScheme.hGl sc ρ' (CycScheme.cur P (ρ', false)) = ⊤ := fun {k' r' ρ'} h' => by
    rw [hsc]; exact hGl_top h'
  by_contra hne
  push Not at hne
  -- all later states are unfinished states of walk `k`
  have hall : ∀ j, j0 ≤ j → ∃ r, GAt P rl k r (T.S j).1 ∧ (T.S j).2 = false := by
    intro j hj
    induction j, hj using Nat.le_induction with
    | base => exact hcur
    | succ j hj ih =>
      obtain ⟨r, h, hf⟩ := ih
      have hSj : T.S j = ((T.S j).1, false) := Prod.ext rfl hf
      have hg := T.good j hf _ _ h
      have e : T.S (j + 1) = CycScheme.upd P sc ((T.S j).1, false) (T.O j) := by
        rw [T.step]; exact congrArg (fun x => CycScheme.upd P sc x (T.O j)) hSj
      by_cases hs : CycScheme.stops P sc ((T.S j).1, false) (T.O j)
      · exfalso
        obtain ⟨h1, h2⟩ := upd_stop_next T.zero h hg hs hK
        rw [← e] at h1 h2
        exact hne (j + 1) (Nat.le_succ_of_le hj) 0 h2 h1
      · obtain ⟨h1, h2⟩ := upd_notStop h hg hs
        rw [← e] at h1 h2
        refine ⟨_, h1, ?_⟩
        rw [h2]
        simp only [decide_eq_false_iff_not]
        rw [hgl h]
        exact ENNReal.coe_ne_top
  obtain ⟨j, hj, r, hr, hrM⟩ := T.unbounded hall (sInf (gcand P rl k)).toNNReal
  have h1 := hr.le_sInf
  have hfin' : sInf (gcand P rl k) ≠ ⊤ := hfin.ne
  have : (sInf (gcand P rl k)).toNNReal < r := hrM
  have h2 : ((sInf (gcand P rl k)).toNNReal : ℝ≥0∞) < r := by exact_mod_cast this
  rw [ENNReal.coe_toNNReal hfin'] at h2
  exact absurd h1 (not_le.2 h2)

omit [Countable I] [MeasurableSingletonClass I] in
omit [Fact (0 < β)] in
theorem E_len (k : ℕ) : (P.E rl k).len = sInf (gcand P rl k) := by
  rw [E_eq']
  exact CPath.cut_len _ _

/-- Every walk that the recursion appends is reached by the scheme (for `s_∘ = ∞`). -/
theorem GTraj.reach (hK : 0 < P.K) (h0 : T.S 0 = CycScheme.init P)
    (hsc : sc = ⊤) :
    ∀ k : ℕ, P.Cont rl k →
      ∃ j, ∃ r, GAt P rl k r (T.S j).1 ∧ (T.S j).2 = false := by
  intro k
  induction k with
  | zero =>
    intro _
    exact ⟨0, 0, by rw [h0]; exact gAt_init T.zero hK, by rw [h0]; rfl⟩
  | succ k ih =>
    intro hc
    obtain ⟨j0, r0, h0', hf0⟩ := ih (CycPlan.Cont.anti P rl (Nat.le_succ k) hc)
    have hfin : sInf (gcand P rl k) < ⊤ := by
      have := hc.2 k (Nat.lt_succ_self k)
      rwa [E_len] at this
    obtain ⟨j, -, r, hr, hrf⟩ := T.reach_next hsc ⟨r0, h0', hf0⟩ hfin (by exact_mod_cast hc.1)
    exact ⟨j, r, hr, hrf⟩


omit [Countable I] [MeasurableSingletonClass I] [Fact (0 < β)] in
/-- Entry `k` of an invariant state is an initial piece of the environment world-line `E k`. -/
theorem nth_of_inv {st : CycScheme.State I d} (hI : GInv P sc rl st) {k : ℕ} {e : CycEntry I d}
    (h : st.1.nth k = some e) :
    ∃ ρ' : ℝ≥0∞, ρ' ≤ sInf (gcand P rl k) ∧ e = (gdat P rl k, (gpth P rl k).cut ρ') := by
  obtain ⟨k', r, hrec, -, -, hle⟩ := hI.rec_form
  have hs : st.1 = gshape P rl k' r := hrec
  rw [hs] at h
  rcases lt_trichotomy k k' with hk | rfl | hk
  · rw [nth_shape_lt k' r hk] at h
    cases h
    exact ⟨_, le_rfl, E_eq' P rl k⟩
  · rw [nth_shape_self] at h
    cases h
    exact ⟨_, hle, rfl⟩
  · rw [nth_shape_gt k' r hk] at h
    exact absurd h (by simp)

theorem GTraj.stay (hsc : sc = ⊤) {k j0 : ℕ}
    (hcur : ∃ r, GAt P rl k r (T.S j0).1 ∧ (T.S j0).2 = false)
    (htop : sInf (gcand P rl k) = ⊤) :
    ∀ j, j0 ≤ j → ∃ r, GAt P rl k r (T.S j).1 ∧ (T.S j).2 = false := by
  have hgl : ∀ {k' : ℕ} {r' : ℝ≥0} {ρ' : CycRec I d}, GAt P rl k' r' ρ' →
      CycScheme.hGl sc ρ' (CycScheme.cur P (ρ', false)) = ⊤ := fun {k' r' ρ'} h' => by
    rw [hsc]; exact hGl_top h'
  intro j hj
  induction j, hj using Nat.le_induction with
  | base => exact hcur
  | succ j hj ih =>
    obtain ⟨r, h, hf⟩ := ih
    have hSj : T.S j = ((T.S j).1, false) := Prod.ext rfl hf
    have hg := T.good j hf _ _ h
    have e : T.S (j + 1) = CycScheme.upd P sc ((T.S j).1, false) (T.O j) := by
      rw [T.step]; exact congrArg (fun x => CycScheme.upd P sc x (T.O j)) hSj
    by_cases hs : CycScheme.stops P sc ((T.S j).1, false) (T.O j)
    · exfalso
      have := sInf_cand_eq h hg hs
      rw [htop] at this
      exact ENNReal.top_ne_coe this
    · obtain ⟨h1, h2⟩ := upd_notStop h hg hs
      rw [← e] at h1 h2
      refine ⟨_, h1, ?_⟩
      rw [h2]
      simp only [decide_eq_false_iff_not]
      rw [hgl h]
      exact ENNReal.coe_ne_top

/-- A walk of finite stopping length stops: afterwards the state has an entry `k + 1`, or it is the
finished state `(ideal (k+1), true)`. -/
theorem GTraj.exit (hsc : sc = ⊤) {k j0 : ℕ}
    (hcur : ∃ r, GAt P rl k r (T.S j0).1 ∧ (T.S j0).2 = false)
    (hfin : sInf (gcand P rl k) < ⊤) :
    ∃ j, j0 ≤ j ∧ ((∃ r, GAt P rl (k + 1) r (T.S j).1 ∧ (T.S j).2 = false) ∨
      ((T.S j).1 = Sum.inl ⟨k + 1, P.ideal rl (k + 1)⟩ ∧ (T.S j).2 = true)) := by
  by_contra hne
  push Not at hne
  have hgl : ∀ {k' : ℕ} {r' : ℝ≥0} {ρ' : CycRec I d}, GAt P rl k' r' ρ' →
      CycScheme.hGl sc ρ' (CycScheme.cur P (ρ', false)) = ⊤ := fun {k' r' ρ'} h' => by
    rw [hsc]; exact hGl_top h'
  have hall : ∀ j, j0 ≤ j → ∃ r, GAt P rl k r (T.S j).1 ∧ (T.S j).2 = false := by
    intro j hj
    induction j, hj using Nat.le_induction with
    | base => exact hcur
    | succ j hj ih =>
      obtain ⟨r, h, hf⟩ := ih
      have hSj : T.S j = ((T.S j).1, false) := Prod.ext rfl hf
      have hg := T.good j hf _ _ h
      have e : T.S (j + 1) = CycScheme.upd P sc ((T.S j).1, false) (T.O j) := by
        rw [T.step]; exact congrArg (fun x => CycScheme.upd P sc x (T.O j)) hSj
      by_cases hs : CycScheme.stops P sc ((T.S j).1, false) (T.O j)
      · exfalso
        by_cases hK : ((k + 1 : ℕ) : ℕ∞) < P.K
        · obtain ⟨h1, h2⟩ := upd_stop_next T.zero h hg hs hK
          rw [← e] at h1 h2
          have := (hne (j + 1) (Nat.le_succ_of_le hj)).1 0
          exact this h2 h1
        · have := upd_stop_end h hg hs hK
          rw [← e] at this
          exact (hne (j + 1) (Nat.le_succ_of_le hj)).2 (congrArg Prod.fst this)
            (congrArg Prod.snd this)
      · obtain ⟨h1, h2⟩ := upd_notStop h hg hs
        rw [← e] at h1 h2
        refine ⟨_, h1, ?_⟩
        rw [h2]
        simp only [decide_eq_false_iff_not]
        rw [hgl h]
        exact ENNReal.coe_ne_top
  obtain ⟨j, hj, r, hr, hrM⟩ := T.unbounded hall (sInf (gcand P rl k)).toNNReal
  have h1 := hr.le_sInf
  have hfin' : sInf (gcand P rl k) ≠ ⊤ := hfin.ne
  have h2 : ((sInf (gcand P rl k)).toNNReal : ℝ≥0∞) < r := by exact_mod_cast hrM
  rw [ENNReal.coe_toNNReal hfin'] at h2
  exact absurd h1 (not_le.2 h2)

omit [Countable I] [MeasurableSingletonClass I] in
omit [Fact (0 < β)] in
theorem nth_ideal_succ_self (k : ℕ) :
    CycRec.nth (Sum.inl ⟨k + 1, P.ideal rl (k + 1)⟩ : CycRec I d) k =
      some (P.E rl k) := by
  simp only [CycRec.nth, dite_eq_left (Nat.lt_succ_self k)]
  congr 1
  exact P.ideal_apply rl (k + 1) ⟨k, Nat.lt_succ_self k⟩

/-- Case `ℓ_k = ∞`: the current time of walk `k` is eventually larger than any `M`. -/
theorem GTraj.case_top (hK : 0 < P.K) (h0 : T.S 0 = CycScheme.init P)
    (hsc : sc = ⊤) {k : ℕ} (hc : P.Cont rl k) (htop : sInf (gcand P rl k) = ⊤) (M : ℝ≥0) :
    ∃ J, ∀ j, J ≤ j → ∃ r : ℝ≥0, M < r ∧
      (T.S j).1.nth k = some (gdat P rl k, (gpth P rl k).cut (r : ℝ≥0∞)) := by
  obtain ⟨j0, r0, h0', hf0⟩ := T.reach hK h0 hsc k hc
  have hstay := T.stay hsc ⟨r0, h0', hf0⟩ htop
  obtain ⟨j1, hj1, r1, hr1, hM⟩ := T.unbounded hstay M
  refine ⟨j1, fun j hj => ?_⟩
  have hmono : ∀ j, j1 ≤ j → ∃ r : ℝ≥0, M < r ∧ GAt P rl k r (T.S j).1 := by
    intro j hj
    induction j, hj using Nat.le_induction with
    | base => exact ⟨r1, hM, hr1⟩
    | succ j hj ih =>
      obtain ⟨r, hMr, hr⟩ := ih
      obtain ⟨r', hr', -⟩ := hstay (j + 1) (by omega)
      refine ⟨r', lt_of_lt_of_le hMr ?_, hr'⟩
      have hext := T.extends hK h0 j
      obtain ⟨e', he', -, hp⟩ := hext k (gdat P rl k, (gpth P rl k).cut (r : ℝ≥0∞)) (by
        rw [hr.eq_shape]; exact nth_shape_self k r)
      rw [hr'.eq_shape, nth_shape_self] at he'
      cases he'
      have h1 : ((r : ℝ≥0) : ℝ≥0∞) ≤ (r' : ℝ≥0∞) := by
        have := hp.1
        change ((gpth P rl k).1.cut (r : ℝ≥0∞)).len ≤ ((gpth P rl k).1.cut (r' : ℝ≥0∞)).len at this
        rwa [CPath.cut_len, CPath.cut_len] at this
      exact_mod_cast h1
  obtain ⟨r, hMr, hr⟩ := hmono j hj
  exact ⟨r, hMr, by rw [hr.eq_shape]; exact nth_shape_self k r⟩

/-- Case `ℓ_k < ∞`: the entry `k` is eventually `E k`. -/
theorem GTraj.case_fin (hK : 0 < P.K) (h0 : T.S 0 = CycScheme.init P)
    (hsc : sc = ⊤) {k : ℕ} (hc : P.Cont rl k) (hfin : sInf (gcand P rl k) < ⊤) :
    ∃ J, ∀ j, J ≤ j → (T.S j).1.nth k = some (P.E rl k) := by
  obtain ⟨j0, r0, h0', hf0⟩ := T.reach hK h0 hsc k hc
  obtain ⟨j1, hj1, hcase⟩ := T.exit hsc ⟨r0, h0', hf0⟩ hfin
  have hpers : ∀ j, j1 ≤ j → ((T.S j).1.nth (k + 1)).isSome ∨
      ((T.S j).1 = Sum.inl ⟨k + 1, P.ideal rl (k + 1)⟩ ∧ (T.S j).2 = true) := by
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
        obtain ⟨e', he', -⟩ := T.extends hK h0 j (k + 1) e he
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
    obtain ⟨k', r, hrec, -, -, -⟩ := (T.inv hK h0 j).rec_form
    have hs : (T.S j).1 = gshape P rl k' r := hrec
    rw [hs] at he ⊢
    rcases lt_trichotomy (k + 1) k' with hk | rfl | hk
    · exact nth_shape_lt k' r (by omega)
    · exact nth_shape_lt (k + 1) r (Nat.lt_succ_self k)
    · rw [nth_shape_gt k' r hk] at he
      exact absurd he (by simp)
  · rw [hrec]; exact nth_ideal_succ_self k


end CycSchemeGen
end ElboimSly.Cyclic

end
