/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Base.TwoParticle
public import ElboimSly.Paper.Base.StepRec
public import ElboimSly.Foundations.Cyclic.CPathLeft
public import Mathlib

/-!
# The two-particle map as a function of a jump-list path

Contacts are few (i) (adaptedness of `y = 𝔉_{a,b}(X₁, X₂)`), via paths.

For a path `q : CPath (ℤ^d × ℤ^d)` (the pair of driving paths), `solQ a b q` is the explicit
solution `recSol q G b` of the causal recursion of the two-particle map.  Here the right-hand
side of the rules is a function `twoStepV` of the left value, the value, and the current state.
-/

@[expose] public section

open Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Paper

open ElboimSly.Cyclic ElboimSly.Paper.Base

variable {d : ℕ}

/-- The pairs of driving paths take values in `ℤ^d × ℤ^d`. -/
abbrev PairE (d : ℕ) : Type := (Fin d → ℤ) × (Fin d → ℤ)

/-- The right-hand side of the rules (F1)-(F3) as a function of `u = (p(r-), x₂(r-))`-type left
values, `v` the values at `r`, and the state `w = y(r-)`. -/
noncomputable def twoStepV (a : Fin d → ℤ) (u v : PairE d) (w : Fin d → ℤ) : Fin d → ℤ :=
  open Classical in
  if u.1 ≠ v.1 ∧ (w = a + u.1 ∨ w = a + v.1) then
    (if w = a + u.1 then a + v.1 else a + u.1)
  else if u.2 ≠ v.2 ∧ a + u.1 ≠ w ∧ a + u.1 ≠ w + (v.2 - u.2) then w + (v.2 - u.2)
  else w

/-- The right-hand side `G` of the recursion, for the driving pair `q`. -/
noncomputable def stepG (a : Fin d → ℤ) (q : CPath (PairE d)) (r : ℝ≥0) (w : Fin d → ℤ) :
    Fin d → ℤ :=
  twoStep a (fun s => (q.fn s).1) (fun s => (q.fn s).2) r w

/-- The explicit solution of the two-particle recursion driven by `q`. -/
noncomputable def solQ (a b : Fin d → ℤ) (q : CPath (PairE d)) : ℝ≥0 → Fin d → ℤ :=
  recSol q (stepG a q) b

theorem isStepPath_fst (q : CPath (PairE d)) : IsStepPath fun s => (q.fn s).1 :=
  ⟨fun s => by filter_upwards [q.rc s] with u hu; rw [hu],
    fun T => (q.fin T).subset fun r hr =>
      ⟨⟨hr.1.1, fun hc => hr.1.2 (by
        filter_upwards [hc] with u hu; rw [hu])⟩, hr.2⟩⟩

theorem isStepPath_snd (q : CPath (PairE d)) : IsStepPath fun s => (q.fn s).2 :=
  ⟨fun s => by filter_upwards [q.rc s] with u hu; rw [hu],
    fun T => (q.fin T).subset fun r hr =>
      ⟨⟨hr.1.1, fun hc => hr.1.2 (by
        filter_upwards [hc] with u hu; rw [hu])⟩, hr.2⟩⟩

theorem stepG_of_notMem (a : Fin d → ℤ) (q : CPath (PairE d)) {r : ℝ≥0} (hr : r ∉ CDisc q.fn)
    (w : Fin d → ℤ) : stepG a q r w = w :=
  twoStep_of_notMem a (notMem_pair (x₁ := fun s => (q.fn s).1) (x₂ := fun s => (q.fn s).2) hr).1
    (notMem_pair (x₁ := fun s => (q.fn s).1) (x₂ := fun s => (q.fn s).2) hr).2 w

theorem isTwoParticle_solQ (a b : Fin d → ℤ) (q : CPath (PairE d)) :
    IsTwoParticle a b (fun s => (q.fn s).1) (fun s => (q.fn s).2) (solQ a b q) := by
  have hG : ∀ r, r ∉ CDisc q.fn → ∀ w, stepG a q r w = w := fun r hr w => stepG_of_notMem a q hr w
  refine ⟨recSol_isStepPath q (stepG a q) b hG, ?_, fun r hr => recSol_eq q (stepG a q) b hG hr⟩
  unfold solQ recSol; rw [cnt_zero]; rfl

theorem solQ_zero (a b : Fin d → ℤ) (q : CPath (PairE d)) : solQ a b q 0 = b :=
  (isTwoParticle_solQ a b q).zero

theorem isStepPath_solQ (a b : Fin d → ℤ) (q : CPath (PairE d)) : IsStepPath (solQ a b q) :=
  (isTwoParticle_solQ a b q).step

theorem twoParticle_eq_solQ (a b : Fin d → ℤ) {x₁ x₂ : ℝ≥0 → Fin d → ℤ} (h1 : IsStepPath x₁)
    (h2 : IsStepPath x₂) (q : CPath (PairE d)) (hq : ∀ s, q.fn s = (x₁ s, x₂ s)) :
    twoParticle a b x₁ x₂ = solQ a b q := by
  have e1 : (fun s => (q.fn s).1) = x₁ := funext fun s => by rw [hq]
  have e2 : (fun s => (q.fn s).2) = x₂ := funext fun s => by rw [hq]
  have := isTwoParticle_solQ a b q
  rw [e1, e2] at this
  exact (eq_twoParticle h1 h2 this).symm

theorem stepG_eq_V (a : Fin d → ℤ) (q : CPath (PairE d)) {r : ℝ≥0} (hr : 0 < r)
    (w : Fin d → ℤ) : stepG a q r w = twoStepV a (q.left r) (q.fn r) w := by
  have l1 : Function.leftLim (fun s => (q.fn s).1) r = (q.left r).1 :=
    IsStepPath.leftLim_eq hr ((q.eventually_left hr).mono fun u hu => by rw [hu])
  have l2 : Function.leftLim (fun s => (q.fn s).2) r = (q.left r).2 :=
    IsStepPath.leftLim_eq hr ((q.eventually_left hr).mono fun u hu => by rw [hu])
  have c1 : r ∈ CDisc (fun s => (q.fn s).1) ↔ (q.left r).1 ≠ (q.fn r).1 := by
    rw [(isStepPath_fst q).mem_CDisc_iff hr, l1]
  have c2 : r ∈ CDisc (fun s => (q.fn s).2) ↔ (q.left r).2 ≠ (q.fn r).2 := by
    rw [(isStepPath_snd q).mem_CDisc_iff hr, l2]
  unfold stepG twoStep twoStepV
  simp only [c1, c2, l1, l2]

/-- The sequence of states after `k` jumps, with the rules written in terms of `q.jv`. -/
noncomputable def jseq (a b : Fin d → ℤ) (q : CPath (PairE d)) : ℕ → Fin d → ℤ
  | 0 => b
  | k + 1 =>
    if q.jt (k + 1) < ⊤ then twoStepV a (q.jv k) (q.jv (k + 1)) (jseq a b q k) else b

theorem jumpSeq_eq_jseq (a b : Fin d → ℤ) (q : CPath (PairE d)) :
    ∀ k, (k = 0 ∨ q.jt k < ⊤) → jumpSeq q (stepG a q) b k = jseq a b q k
  | 0, _ => rfl
  | k + 1, h => by
    have hlt : q.jt (k + 1) < ⊤ := h.resolve_left (Nat.succ_ne_zero k)
    have hlt' : q.jt k < q.jt (k + 1) := q.jt_lt_succ hlt
    have ih := jumpSeq_eq_jseq a b q k (by
      rcases Nat.eq_zero_or_pos k with hk | hk
      · exact Or.inl hk
      · exact Or.inr (hlt'.trans hlt))
    set r := (q.jt (k + 1)).toNNReal with hr
    have hrc : (r : ℝ≥0∞) = q.jt (k + 1) := ENNReal.coe_toNNReal hlt.ne
    have hr0 : 0 < r := by
      have : (0 : ℝ≥0∞) < r := by rw [hrc]; exact lt_of_le_of_lt bot_le hlt'
      exact_mod_cast this
    have hl : q.left r = q.jv k := q.left_eq_jv (by rw [hrc]; exact hlt') (by rw [hrc])
    show stepG a q r (jumpSeq q (stepG a q) b k) = _
    rw [stepG_eq_V a q hr0, hl, ih]
    simp only [jseq, ite_eq_left hlt]
    rfl

theorem measurable_jseq (a b : Fin d → ℤ) :
    ∀ k, Measurable (fun q : CPath (PairE d) => jseq a b q k)
  | 0 => measurable_const
  | k + 1 => by
    have hset : MeasurableSet {q : CPath (PairE d) | q.jt (k + 1) < ⊤} :=
      measurableSet_lt (CPath.measurable_jt _) measurable_const
    refine Measurable.ite hset ?_ measurable_const
    have hf := (CPath.measurable_jv (V := PairE d) k).prodMk
      ((CPath.measurable_jv (V := PairE d) (k + 1)).prodMk (measurable_jseq a b k))
    exact (measurable_of_countable
      (fun p : PairE d × PairE d × (Fin d → ℤ) => twoStepV a p.1 p.2.1 p.2.2)).comp hf

theorem solQ_eq_jseq (a b : Fin d → ℤ) (q : CPath (PairE d)) (t : ℝ≥0) :
    solQ a b q t = jseq a b q (q.cnt t) := by
  unfold solQ recSol
  refine jumpSeq_eq_jseq a b q _ ?_
  rcases Nat.eq_zero_or_pos (q.cnt t) with h | h
  · exact Or.inl h
  · exact Or.inr (lt_of_le_of_lt ((q.jt_le_iff _ t).2 le_rfl) ENNReal.coe_lt_top)

/-- The state at a fixed time is a measurable function of the driving path. -/
theorem measurable_solQ (a b : Fin d → ℤ) (t : ℝ≥0) :
    Measurable (fun q : CPath (PairE d) => solQ a b q t) := by
  have h1 : Measurable fun q : CPath (PairE d) => (q.cnt t, q) :=
    (CPath.measurable_cnt t).prodMk measurable_id
  have h2 : Measurable fun p : ℕ × CPath (PairE d) => jseq a b p.2 p.1 :=
    measurable_from_prod_countable_right fun k => measurable_jseq a b k
  have := h2.comp h1
  convert this using 1
  funext q
  exact solQ_eq_jseq a b q t

end ElboimSly.Paper
