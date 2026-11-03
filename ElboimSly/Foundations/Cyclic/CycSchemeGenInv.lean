/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycSchemeGenUpd
public import ElboimSly.Foundations.Cyclic.CycSchemeEnvUnb
public import ElboimSly.Foundations.Cyclic.CycSchemeEnvAe
public import Mathlib

/-!
# Generic invariant, extension and non-explosion (port of `CycSchemeEnvAe/Ext/Walk`)

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

omit [Countable I] [MeasurableSingletonClass I] [Fact (0 < β)] in
theorem GAt.le_sInf {k : ℕ} {r : ℝ≥0} {ρ : CycRec I d} (h : GAt P rl k r ρ) :
    (r : ℝ≥0∞) ≤ sInf (gcand P rl k) := by
  rcases h.pre with rfl | h
  · simp
  · exact _root_.le_sInf fun c hc => (h c hc).le

omit [Countable I] [MeasurableSingletonClass I] in
omit [Fact (0 < β)] in
theorem nth_rec_lt {k : ℕ} (e : CycEntry I d) {i : ℕ} (hi : i < k) :
    CycRec.nth (Sum.inl ⟨k + 1, CycRec.snoc (P.ideal rl k) e⟩ : CycRec I d) i =
      some (P.E rl i) := by
  simp only [CycRec.nth, dite_eq_left (Nat.lt_succ_of_lt hi)]
  congr 1
  have : (⟨i, Nat.lt_succ_of_lt hi⟩ : Fin (k + 1)) = Fin.castSucc ⟨i, hi⟩ := rfl
  rw [this]
  simp only [CycRec.snoc, Fin.snoc_castSucc]
  exact P.ideal_apply rl k ⟨i, hi⟩

omit [Countable I] [MeasurableSingletonClass I] in
omit [Fact (0 < β)] in
theorem total_ne_top {k : ℕ} {r : ℝ≥0} {ρ : CycRec I d} (h : GAt P rl k r ρ) : ρ.total ≠ ⊤ := by
  rw [h.rec_eq]
  show CycRec.cum _ (k + 1 - 1) ≠ ⊤
  rw [Nat.add_sub_cancel]
  unfold CycRec.cum
  refine ENNReal.sum_ne_top.2 fun i hi => ?_
  have hik : i < k := Finset.mem_range.1 hi
  unfold CycRec.lenAt
  rw [nth_rec_lt (P := P) (rl := rl) _ hik]
  exact (h.allFin i hik).ne

omit [Countable I] [MeasurableSingletonClass I] in
omit [Fact (0 < β)] in
theorem hGl_top {k : ℕ} {r : ℝ≥0} {ρ : CycRec I d} (h : GAt P rl k r ρ) :
    CycScheme.hGl ⊤ ρ (CycScheme.cur P (ρ, false)) = ⊤ := by
  unfold CycScheme.hGl
  rw [ENNReal.top_sub (total_ne_top h)]
  exact ENNReal.top_sub ENNReal.coe_ne_top

/-- The invariant of the states along the scheme: unfinished states satisfy `EnvAt`, finished ones
are an `EnvRec`-shaped record (full earlier world-lines and an initial piece of walk `k`). -/
def GInv (P : CycPlan I d β) (sc : ℝ≥0∞) (rl : PathRule I d)
    (st : CycScheme.State I d) : Prop :=
  (st.2 = false ∧ ∃ (k : ℕ) (r : ℝ≥0), GAt P rl k r st.1) ∨
  (st.2 = true ∧ ∃ (k : ℕ) (r : ℝ≥0), st.1 = Sum.inl ⟨k + 1, CycRec.snoc (P.ideal rl k)
      (gdat P rl k, (gpth P rl k).cut (r : ℝ≥0∞))⟩ ∧ P.AllFin rl k ∧ (k : ℕ∞) < P.K ∧
      (r : ℝ≥0∞) ≤ sInf (gcand P rl k) ∧
      (sc = ⊤ → (r : ℝ≥0∞) = sInf (gcand P rl k) ∧ ¬ ((k + 1 : ℕ) : ℕ∞) < P.K))

omit [Countable I] [MeasurableSingletonClass I] [Fact (0 < β)] in
theorem ginv_init (hz : ZeroRule P rl) (hK : 0 < P.K) : GInv P sc rl (CycScheme.init P) :=
  Or.inl ⟨rfl, 0, 0, gAt_init hz hK⟩

theorem ginv_upd (hz : ZeroRule P rl) {st : CycScheme.State I d} (o : Outcome (CycS I d β))
    (hI : GInv P sc rl st)
    (hg : st.2 = false → ∀ k r, GAt P rl k r st.1 → GStep P sc rl k r st.1 o) : GInv P sc rl (CycScheme.upd P sc st o) := by
  rcases hI with ⟨hst, k, r, h⟩ | ⟨hst, rest⟩
  · obtain ⟨ρ, b⟩ := st
    simp only at hst h
    subst hst
    have hg' := hg rfl k r h
    simp only at hg'
    by_cases hs : CycScheme.stops P sc (ρ, false) o
    · by_cases hK : ((k + 1 : ℕ) : ℕ∞) < P.K
      · obtain ⟨h1, h2⟩ := upd_stop_next hz h hg' hs hK
        exact Or.inl ⟨h1, k + 1, 0, h2⟩
      · rw [upd_stop_end h hg' hs hK]
        refine Or.inr ⟨rfl, k, r + CycScheme.sStar P sc (ρ, false) o, ?_, h.allFin, h.lt_K,
          (sInf_cand_eq h hg' hs).ge, fun _ => ⟨(sInf_cand_eq h hg' hs).symm, hK⟩⟩
        show (Sum.inl ⟨k + 1, CycRec.snoc (P.ideal rl k) (P.E rl k)⟩ : CycRec I d) = _
        rw [E_eq_of_stops h hg' hs]
    · obtain ⟨h1, h2⟩ := upd_notStop h hg' hs
      by_cases hf : (CycScheme.upd P sc (ρ, false) o).2 = true
      · refine Or.inr ⟨hf, k, _, h1.rec_eq, h1.allFin, h1.lt_K, h1.le_sInf, fun hsc => ?_⟩
        exfalso
        rw [h2] at hf
        have hd := of_decide_eq_true hf
        rw [hsc, hGl_top h] at hd
        exact ENNReal.coe_ne_top hd
      · exact Or.inl ⟨by simpa using hf, k, _, h1⟩
  · have : CycScheme.upd P sc st o = st := by
      unfold CycScheme.upd
      rw [ite_eq_left hst]
    rw [this]
    exact Or.inr ⟨hst, rest⟩

omit [Countable I] [MeasurableSingletonClass I] in
omit [Fact (0 < β)] in
theorem E_cut_eq (k : ℕ) {r : ℝ≥0} (hr : (r : ℝ≥0∞) ≤ sInf (gcand P rl k)) :
    (P.E rl k).cut (r : ℝ≥0∞) = (gdat P rl k, (gpth P rl k).cut (r : ℝ≥0∞)) := by
  rw [E_eq']
  refine Prod.ext rfl (Subtype.ext ?_)
  exact CPath.cut_cut _ hr

omit [Countable I] [MeasurableSingletonClass I] [Fact (0 < β)] in
theorem GInv.rec_form {st : CycScheme.State I d} (hI : GInv P sc rl st) :
    ∃ (k : ℕ) (r : ℝ≥0), st.1 = Sum.inl ⟨k + 1, CycRec.snoc (P.ideal rl k)
        (gdat P rl k, (gpth P rl k).cut (r : ℝ≥0∞))⟩ ∧ P.AllFin rl k ∧ (k : ℕ∞) < P.K ∧
      (r : ℝ≥0∞) ≤ sInf (gcand P rl k) := by
  rcases hI with ⟨-, k, r, h⟩ | ⟨-, k, r, hr⟩
  · exact ⟨k, r, h.rec_eq, h.allFin, h.lt_K, h.le_sInf⟩
  · exact ⟨k, r, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1⟩

/-- The record of the first `k` full environment world-lines and the initial piece of walk `k` at
time `r`. -/
noncomputable def gshape (P : CycPlan I d β) (rl : PathRule I d) (k : ℕ) (r : ℝ≥0) :
    CycRec I d :=
  Sum.inl ⟨k + 1, CycRec.snoc (P.ideal rl k) (gdat P rl k, (gpth P rl k).cut (r : ℝ≥0∞))⟩

omit [Countable I] [MeasurableSingletonClass I] in
omit [Fact (0 < β)] in
theorem nth_shape_lt (k : ℕ) (r : ℝ≥0) {i : ℕ} (hi : i < k) :
    (gshape P rl k r).nth i = some (P.E rl i) := by
  simp only [gshape, CycRec.nth, dite_eq_left (Nat.lt_succ_of_lt hi)]
  congr 1
  have : (⟨i, Nat.lt_succ_of_lt hi⟩ : Fin (k + 1)) = Fin.castSucc ⟨i, hi⟩ := rfl
  rw [this]
  simp only [CycRec.snoc, Fin.snoc_castSucc]
  exact P.ideal_apply rl k ⟨i, hi⟩

omit [Countable I] [MeasurableSingletonClass I] [Fact (0 < β)] in
theorem nth_shape_self (k : ℕ) (r : ℝ≥0) :
    (gshape P rl k r).nth k = some (gdat P rl k, (gpth P rl k).cut (r : ℝ≥0∞)) := by
  simp only [gshape, CycRec.nth, dite_eq_left (Nat.lt_succ_self k)]
  congr 1
  have : (⟨k, Nat.lt_succ_self k⟩ : Fin (k + 1)) = Fin.last k := rfl
  rw [this]
  simp [CycRec.snoc]

omit [Countable I] [MeasurableSingletonClass I] [Fact (0 < β)] in
theorem nth_shape_gt (k : ℕ) (r : ℝ≥0) {i : ℕ} (hi : k < i) : (gshape P rl k r).nth i = none := by
  simp only [gshape, CycRec.nth, dite_eq_right (show ¬ i < k + 1 by omega)]

theorem isPiece_cut (p : CPath (Fin d → ℤ)) {r r' : ℝ≥0∞} (h : r ≤ r') :
    (p.cut r).IsPiece (p.cut r') := by
  refine ⟨by simpa using h, ?_⟩
  rw [CPath.cut_len, CPath.cut_cut p h]

omit [Countable I] [MeasurableSingletonClass I] in
omit [Fact (0 < β)] in
theorem extends_shape_same (k : ℕ) {r r' : ℝ≥0} (h : r ≤ r') :
    (gshape P rl k r).Extends (gshape P rl k r') := by
  intro i e he
  rcases lt_trichotomy i k with hi | heq | hi
  · rw [nth_shape_lt k r hi] at he
    refine ⟨e, by rw [nth_shape_lt k r' hi]; exact he, rfl, ?_⟩
    exact CPath.isPiece_refl _
  · rw [heq, nth_shape_self] at he
    cases he
    exact ⟨(gdat P rl k, (gpth P rl k).cut (r' : ℝ≥0∞)), by rw [heq]; exact nth_shape_self k r', rfl,
      isPiece_cut (gpth P rl k).1 (by exact_mod_cast h : (r : ℝ≥0∞) ≤ r')⟩
  · rw [nth_shape_gt k r hi] at he
    exact absurd he (by simp)

omit [Countable I] [MeasurableSingletonClass I] in
omit [Fact (0 < β)] in
theorem extends_shape_next (k : ℕ) {r : ℝ≥0} (h : (r : ℝ≥0∞) ≤ sInf (gcand P rl k)) :
    (gshape P rl k r).Extends (gshape P rl (k + 1) 0) := by
  intro i e he
  rcases lt_trichotomy i k with hi | heq | hi
  · rw [nth_shape_lt k r hi] at he
    refine ⟨e, by rw [nth_shape_lt (k + 1) 0 (Nat.lt_succ_of_lt hi)]; exact he, rfl, ?_⟩
    exact CPath.isPiece_refl _
  · rw [heq, nth_shape_self] at he
    cases he
    refine ⟨P.E rl k, by rw [heq]; exact nth_shape_lt (k := k + 1) 0 (Nat.lt_succ_self k), rfl, ?_⟩
    rw [E_eq']
    exact isPiece_cut _ h
  · rw [nth_shape_gt k r hi] at he
    exact absurd he (by simp)

omit [Countable I] [MeasurableSingletonClass I] [Fact (0 < β)] in
theorem GAt.eq_shape {k : ℕ} {r : ℝ≥0} {ρ : CycRec I d} (h : GAt P rl k r ρ) :
    ρ = gshape P rl k r := h.rec_eq

theorem extends_upd (hz : ZeroRule P rl) {sc : ℝ≥0∞} {k : ℕ} {r : ℝ≥0} {ρ : CycRec I d}
    (h : GAt P rl k r ρ) {o : Outcome (CycS I d β)} (hg : GStep P sc rl k r ρ o) :
    ρ.Extends (CycScheme.upd P sc (ρ, false) o).1 := by
  by_cases hs : CycScheme.stops P sc (ρ, false) o
  · by_cases hK : ((k + 1 : ℕ) : ℕ∞) < P.K
    · obtain ⟨-, h2⟩ := upd_stop_next hz h hg hs hK
      have := extends_shape_next (P := P) (rl := rl) k h.le_sInf
      rw [← h.eq_shape, ← h2.eq_shape] at this
      exact this
    · rw [upd_stop_end h hg hs hK]
      have e : (Sum.inl ⟨k + 1, P.ideal rl (k + 1)⟩ : CycRec I d) =
          gshape P rl k (r + CycScheme.sStar P sc (ρ, false) o) := by
        show (Sum.inl ⟨k + 1, CycRec.snoc (P.ideal rl k) (P.E rl k)⟩ : CycRec I d) = _
        rw [E_eq_of_stops h hg hs]
        rfl
      show ρ.Extends (Sum.inl ⟨k + 1, P.ideal rl (k + 1)⟩ : CycRec I d)
      rw [e]
      have := extends_shape_same (P := P) (rl := rl) k
        (le_self_add : r ≤ r + CycScheme.sStar P sc (ρ, false) o)
      rw [← h.eq_shape] at this
      exact this
  · obtain ⟨h1, -⟩ := upd_notStop h hg hs
    have := extends_shape_same (P := P) (rl := rl) k
      (le_self_add : r ≤ r + CycScheme.sStar P sc (ρ, false) o)
    rw [← h.eq_shape, ← h1.eq_shape] at this
    exact this

omit [Countable I] [MeasurableSingletonClass I] [Fact (0 < β)] in
theorem GAt.k_unique {k k' : ℕ} {r r' : ℝ≥0} {ρ : CycRec I d} (h : GAt P rl k r ρ)
    (h' : GAt P rl k' r' ρ) : k = k' := by
  have := h.rec_eq.symm.trans h'.rec_eq
  have h2 := congrArg (fun x : CycRec I d => x.num) this
  simp only [CycRec.num] at h2
  exact_mod_cast Nat.succ_injective (Nat.cast_injective (R := ℕ∞) h2)

omit [Countable I] [MeasurableSingletonClass I] in
omit [Fact (0 < β)] in
theorem GAt.r_unique {k : ℕ} {r r' : ℝ≥0} {ρ : CycRec I d} (h : GAt P rl k r ρ)
    (h' : GAt P rl k r' ρ) : r = r' := by
  have h1 := h.len_cur false
  have h2 := h'.len_cur false
  rw [h1] at h2
  exact_mod_cast h2

/-- A trajectory of states: `S (j+1) = upd (S j) (O j)`, with good outcomes at unfinished steps. -/
structure GTraj (P : CycPlan I d β) (sc : ℝ≥0∞) (rl : PathRule I d) where
  S : ℕ → CycScheme.State I d
  O : ℕ → Outcome (CycS I d β)
  step : ∀ j, S (j + 1) = CycScheme.upd P sc (S j) (O j)
  zero : ZeroRule P rl
  good : ∀ j, (S j).2 = false → ∀ k r, GAt P rl k r (S j).1 → GStep P sc rl k r (S j).1 (O j)

variable (T : GTraj P sc rl)

theorem GTraj.inv (hK : 0 < P.K) (h0 : T.S 0 = CycScheme.init P) :
    ∀ j, GInv P sc rl (T.S j) := by
  intro j
  induction j with
  | zero => rw [h0]; exact ginv_init T.zero hK
  | succ j ih =>
    rw [T.step]
    exact ginv_upd T.zero _ ih (T.good j)

theorem GTraj.unbounded {k : ℕ} {j0 : ℕ}
    (hcur : ∀ j, j0 ≤ j → ∃ r, GAt P rl k r (T.S j).1 ∧ (T.S j).2 = false) :
    ∀ M : ℝ≥0, ∃ j, j0 ≤ j ∧ ∃ r, GAt P rl k r (T.S j).1 ∧ M < r := by
  choose! r hr hf using hcur
  have hnext : ∀ j, j0 ≤ j → r (j + 1) = r j + CycScheme.sStar P sc (T.S j) (T.O j) ∧
      0 < CycScheme.sStar P sc (T.S j) (T.O j) ∧
      (r j + CycScheme.sStar P sc (T.S j) (T.O j) ∈ CDisc (gpth P rl k).1.fn ∨
        ∃ m : ℕ, ((r j + CycScheme.sStar P sc (T.S j) (T.O j) : ℝ≥0) : ℝ) = β * m) := by
    intro j hj
    have hSj : T.S j = ((T.S j).1, false) := Prod.ext rfl (hf j hj)
    have e : T.S (j + 1) = CycScheme.upd P sc ((T.S j).1, false) (T.O j) := by
      rw [T.step]; exact congrArg (fun x => CycScheme.upd P sc x (T.O j)) hSj
    have h1 := hr j hj
    have h2 := hr (j + 1) (Nat.le_succ_of_le hj)
    have hg := T.good j (hf j hj) k _ h1
    have h2f := hf (j + 1) (Nat.le_succ_of_le hj)
    rw [hSj] at ⊢
    have hs0 : ¬ CycScheme.stops P sc ((T.S j).1, false) (T.O j) := by
      intro hs
      by_cases hK : ((k + 1 : ℕ) : ℕ∞) < P.K
      · obtain ⟨-, h3⟩ := upd_stop_next T.zero h1 hg hs hK
        rw [e] at h2
        have := h2.k_unique h3
        omega
      · rw [e, upd_stop_end h1 hg hs hK] at h2f
        exact absurd h2f (by simp)
    obtain ⟨h3, h4⟩ := upd_notStop h1 hg hs0
    rw [e] at h2 h2f
    have hfl : ((CycScheme.sStar P sc ((T.S j).1, false) (T.O j) : ℝ≥0) : ℝ≥0∞) ≠
        CycScheme.hGl sc (T.S j).1 (CycScheme.cur P ((T.S j).1, false)) := by
      intro hh
      rw [h4] at h2f
      simp [hh] at h2f
    have hr' := h2.r_unique h3
    obtain ⟨hpos, hmark⟩ := hg.marked hs0 hfl
    exact ⟨hr', hpos, hmark⟩
  intro M
  set q : ℕ → ℝ≥0 := fun i => r (j0 + i + 1) with hq
  have hmono : StrictMono q := by
    refine strictMono_nat_of_lt_succ fun i => ?_
    have := hnext (j0 + i + 1) (by omega)
    show r (j0 + i + 1) < r (j0 + (i + 1) + 1)
    rw [show j0 + (i + 1) + 1 = j0 + i + 1 + 1 by ring, this.1]
    exact lt_add_of_pos_right _ this.2.1
  have hmark : ∀ i, q i ∈ CDisc (gpth P rl k).1.fn ∨ ∃ m : ℕ, (q i : ℝ) = β * m := by
    intro i
    have := hnext (j0 + i) (by omega)
    have e : q i = r (j0 + i) + CycScheme.sStar P sc (T.S (j0 + i)) (T.O (j0 + i)) := this.1
    rw [e]
    exact this.2.2
  obtain ⟨i, hi⟩ := unbounded_of_marked (gpth P rl k).1 q hmono hmark M
  exact ⟨j0 + i + 1, by omega, q i, hr _ (by omega), hi⟩

end CycSchemeGen
end ElboimSly.Cyclic

end
