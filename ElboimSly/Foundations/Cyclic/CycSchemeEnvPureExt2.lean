/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycSchemeEnvPureExt
public import ElboimSly.Foundations.PPP.Exploration.ThmLawInf
public import ElboimSly.Foundations.Cyclic.CycRecLimit
public import Mathlib

/-!
# The records of the scheme extend each other (record level)

The environment scheme of a plan; Several walks explored one after another (b). `CycScheme.upd_finRec_extends`: the
update of a state whose record has only entries of finite length gives a record of the same kind
that extends the old one, for every outcome. `CycScheme.extends_stateAt`: the records `ρ_j(π_j y)`
of the pure scheme along any element `y` of `ℋ_∞` extend each other.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ElboimSly.Circle
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

variable {I : Type*} [MeasurableSpace I] {d : ℕ}

namespace CycRec

omit [MeasurableSpace I] in
theorem extends_setLast_inl {n : ℕ} (f : Fin (n + 1) → CycEntry I d) (e : CycEntry I d)
    (hd : (f (Fin.last n)).data = e.data) (hp : (f (Fin.last n)).path.IsPiece e.path) :
    CycRec.Extends (Sum.inl ⟨n + 1, f⟩ : CycRec I d)
      (Sum.inl ⟨n + 1, Function.update f (Fin.last n) e⟩) := by
  intro i e0 he
  have hi : i < n + 1 := by
    by_contra hh
    simp [CycRec.nth, hh] at he
  simp only [CycRec.nth, dite_eq_left hi, Option.some.injEq] at he
  subst he
  by_cases hl : (⟨i, hi⟩ : Fin (n + 1)) = Fin.last n
  · refine ⟨e, ?_, ?_, ?_⟩
    · simp only [CycRec.nth, dite_eq_left hi, hl, Function.update_self]
    · rw [hl]; exact hd
    · rw [hl]; exact hp
  · refine ⟨f ⟨i, hi⟩, ?_, rfl, CPath.isPiece_refl _⟩
    simp only [CycRec.nth, dite_eq_left hi, Function.update_of_ne hl]

omit [MeasurableSpace I] in
theorem extends_push_inl {n : ℕ} (f : Fin n → CycEntry I d) (e : CycEntry I d) :
    CycRec.Extends (Sum.inl ⟨n, f⟩ : CycRec I d) (Sum.inl ⟨n + 1, CycRec.snoc f e⟩) := by
  intro i e0 he
  have hi : i < n := by
    by_contra hh
    simp [CycRec.nth, hh] at he
  simp only [CycRec.nth, dite_eq_left hi, Option.some.injEq] at he
  subst he
  refine ⟨f ⟨i, hi⟩, ?_, rfl, CPath.isPiece_refl _⟩
  simp only [CycRec.nth, dite_eq_left (Nat.lt_succ_of_lt hi), CycRec.snoc]
  have : (⟨i, Nat.lt_succ_of_lt hi⟩ : Fin (n + 1)) = Fin.castSucc ⟨i, hi⟩ := rfl
  rw [this, Fin.snoc_castSucc]

end CycRec

namespace CycScheme

variable [Countable I] [MeasurableSingletonClass I] {β : ℝ} [Fact (0 < β)] (P : CycPlan I d β)
  (sc : ℝ≥0∞)

/-- A finite non-empty record all of whose entries have finite length. -/
def FinRec (ρ : CycRec I d) : Prop :=
  ∃ (n : ℕ) (f : Fin (n + 1) → CycEntry I d), ρ = Sum.inl ⟨n + 1, f⟩ ∧ ∀ i, (f i).len ≠ ⊤

omit [Countable I] [MeasurableSingletonClass I] in
omit [MeasurableSpace I] in
theorem hFr_ne_zero {n : ℕ} (f : Fin (n + 1) → CycEntry I d) (hf : ∀ i, (f i).len ≠ ⊤)
    (E : CycEntry I d) : hFr β (Sum.inl ⟨n + 1, f⟩ : CycRec I d) E ≠ 0 := by
  rcases hFr_attained (β := β) _ E (finite_clock_ringSet (β := β) f hf) with h | ⟨x, -, -, -, h⟩
  · rw [h]; exact ENNReal.top_ne_zero
  · rw [h]; exact (ENNReal.ofReal_pos.2 (circS_mem_Ioc E _ _).1).ne'

theorem newV_of_sStar_zero (st : State I d) (o : Outcome (CycS I d β))
    (hfr : hFr β st.1 (cur P st) ≠ 0) (hs : sStar P sc st o = 0) :
    newV P sc st o = (cur P st).pos := by
  have h1 : ¬ ((sStar P sc st o : ℝ≥0) : ℝ≥0∞) = hFr β st.1 (cur P st) := by
    rw [hs]; exact fun h => hfr h.symm
  have h2 : freshEdge P sc st o = none := by
    unfold freshEdge
    split
    · rw [ite_eq_right]
      rintro ⟨h0, hle, -⟩
      have hne : o.1 ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top hle
      have h3 : (min o.1 (hOf P sc st : ℝ≥0∞)).toNNReal = 0 := hs
      rw [min_eq_left hle, ENNReal.toNNReal_eq_zero_iff] at h3
      rcases h3 with h3 | h3
      · exact h0.ne' h3
      · exact hne h3
    · rfl
  unfold newV
  rw [ite_eq_right h1]
  simp only [h2]

omit [Countable I] [MeasurableSingletonClass I] [Fact (0 < β)] in
theorem finRec_init : FinRec (init P : State I d).1 := by
  refine ⟨0, CycRec.snoc (fun i : Fin 0 => i.elim0) (P.startOf CycRec.empty).newEntry, rfl, ?_⟩
  intro i
  refine Fin.lastCases ?_ (fun j => j.elim0) i
  show (Fin.snoc (α := fun _ => CycEntry I d) (fun i : Fin 0 => i.elim0) _ (Fin.last 0)).len ≠ ⊤
  rw [Fin.snoc_last]
  exact newEntry_len_ne_top _

omit [Countable I] [MeasurableSingletonClass I] in
omit [MeasurableSpace I] in
theorem push_finRec {ρ : CycRec I d} (h : FinRec ρ) {e : CycEntry I d} (he : e.len ≠ ⊤) :
    FinRec (CycRec.push e ρ) ∧ CycRec.Extends ρ (CycRec.push e ρ) := by
  obtain ⟨n, f, rfl, hf⟩ := h
  refine ⟨⟨n + 1, CycRec.snoc f e, rfl, fun i => ?_⟩, CycRec.extends_push_inl f e⟩
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa [CycRec.snoc] using he
  · simp only [CycRec.snoc, Fin.snoc_castSucc]
    exact hf j

/-- The update extends the record and keeps all entries of finite length, for every outcome. -/
theorem upd_finRec_extends (st : State I d) (o : Outcome (CycS I d β)) (h : FinRec st.1) :
    FinRec (upd P sc st o).1 ∧ CycRec.Extends st.1 (upd P sc st o).1 := by
  obtain ⟨ρ, b⟩ := st
  obtain ⟨n, f, rfl, hf⟩ := h
  by_cases hb : b = true
  · have : upd P sc ((Sum.inl ⟨n + 1, f⟩ : CycRec I d), b) o = (Sum.inl ⟨n + 1, f⟩, b) := by
      unfold upd; rw [ite_eq_left hb]
    rw [this]
    exact ⟨⟨n, f, rfl, hf⟩, CycRec.Extends.refl _⟩
  · set st : State I d := ((Sum.inl ⟨n + 1, f⟩ : CycRec I d), b) with hst
    have hcur : cur P st = f (Fin.last n) := cur_inl P n f b
    have hfr : hFr β st.1 (cur P st) ≠ 0 := hFr_ne_zero f hf _
    have hlen : (cur P st).len ≠ ⊤ := by rw [hcur]; exact hf _
    have hpiece : (cur P st).data = (newEntry P sc st o).data ∧
        (cur P st).path.IsPiece (newEntry P sc st o).path := by
      refine ⟨rfl, ?_⟩
      show (cur P st).path.IsPiece ((cur P st).2.extend ((cur P st).time + sStar P sc st o)
        (newV P sc st o)).1
      refine CPath.isPiece_extend (cur P st).2.1 (cur P st).2.2 ?_ ?_
      · exact_mod_cast CycEntry.len_eq_time hlen
      · intro hs0
        exact newV_of_sStar_zero P sc st o hfr hs0
    have hnew : newRec P sc st o = Sum.inl ⟨n + 1, Function.update f (Fin.last n) (newEntry P sc st o)⟩ := rfl
    have hext : CycRec.Extends st.1 (newRec P sc st o) := by
      rw [hnew]
      refine CycRec.extends_setLast_inl f _ ?_ ?_
      · rw [← hcur]; exact hpiece.1
      · rw [← hcur]; exact hpiece.2
    have hfin' : FinRec (newRec P sc st o) := by
      refine ⟨n, _, hnew, fun i => ?_⟩
      by_cases hi : i = Fin.last n
      · subst hi
        simp only [Function.update_self]
        show (((cur P st).2.extend ((cur P st).time + sStar P sc st o) (newV P sc st o)).1).len ≠ ⊤
        exact ENNReal.coe_ne_top
      · simp only [Function.update_of_ne hi]; exact hf i
    have hbf : b = false := by simpa using hb
    unfold upd
    simp only [hst] at *
    split_ifs with hs hK
    · obtain ⟨hF, hE⟩ := push_finRec hfin' (newEntry_len_ne_top _)
      exact ⟨hF, hext.trans hE⟩
    · exact ⟨hfin', hext⟩
    · exact ⟨hfin', hext⟩

variable {U : Type*} [MeasurableSpace U]

theorem finRec_stateAt (k : ℕ) (η : Hist U (CycS I d β) k) : FinRec (stateAt P sc k η).1 := by
  induction k with
  | zero => exact finRec_init P
  | succ k ih =>
    exact (upd_finRec_extends P sc _ η.last (ih η.init)).1

/-- The records of the pure scheme extend each other along every history. -/
theorem extends_stateAt_succ (k : ℕ) (η : Hist U (CycS I d β) (k + 1)) :
    CycRec.Extends (stateAt P sc k η.init).1 (stateAt P sc (k + 1) η).1 :=
  (upd_finRec_extends P sc _ η.last (finRec_stateAt P sc k η.init)).2

/-- The records `ρ_j(π_j y)` of the pure scheme extend each other along every `y ∈ ℋ_∞`
(Several walks explored one after another (b)). -/
theorem extends_stateAt_trunc (j : ℕ) (y : U × (ℕ → Outcome (CycS I d β))) :
    CycRec.Extends (stateAt P sc j (truncHist j y)).1 (stateAt P sc (j + 1) (truncHist (j + 1) y)).1 :=
  extends_stateAt_succ P sc j (truncHist (j + 1) y)

end CycScheme

end ElboimSly.Cyclic

end
