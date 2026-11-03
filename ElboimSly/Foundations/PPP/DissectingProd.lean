/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.PPP.DissectingReal
public import Mathlib

/-!
# Dissecting systems on `E × T`

Examples (c), (d).

For countable `E` (discrete `σ`-algebra) and a separating partition sequence `P` of `T`,
`prodCount E P` has cells `{e} × C`, `C` a cell of `P`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace ElboimSly

/-- A fixed injection of a countable type into `ℕ`. -/
noncomputable def encE (E : Type*) [Countable E] : E → ℕ :=
  Classical.choose (Countable.exists_injective_nat E)

theorem encE_injective (E : Type*) [Countable E] : Function.Injective (encE E) :=
  Classical.choose_spec (Countable.exists_injective_nat E)

namespace SepPartSeq

variable {T : Type*} [MeasurableSpace T] (E : Type*) [MeasurableSpace E] [Countable E]
  [MeasurableSingletonClass E]

/-- Examples (c). -/
noncomputable def prodCount (P : SepPartSeq T) : SepPartSeq (E × T) where
  idx m p := Nat.pair (encE E p.1) (P.idx m p.2)
  measurable_idx m := by
    have h1 : Measurable fun p : E × T => (encE E p.1, P.idx m p.2) :=
      ((measurable_of_countable _).comp measurable_fst).prodMk
        ((P.measurable_idx m).comp measurable_snd)
    exact (measurable_of_countable (fun q : ℕ × ℕ => Nat.pair q.1 q.2)).comp h1
  refine m x y h := by
    have := Nat.pair_eq_pair.1 (show Nat.pair _ _ = Nat.pair _ _ from h)
    exact Nat.pair_eq_pair.2 ⟨this.1, P.refine m _ _ this.2⟩
  separate x y hxy := by
    by_cases he : x.1 = y.1
    · have ht : x.2 ≠ y.2 := fun e => hxy (Prod.ext he e)
      obtain ⟨m, hm⟩ := P.separate _ _ ht
      exact ⟨m, fun h => hm (Nat.pair_eq_pair.1 (show Nat.pair _ _ = Nat.pair _ _ from h)).2⟩
    · exact ⟨0, fun h => he (encE_injective E (Nat.pair_eq_pair.1 (show Nat.pair _ _ = Nat.pair _ _ from h)).1)⟩

variable {E}

theorem prodCount_cell (P : SepPartSeq T) (m b : ℕ) (e : E) :
    (prodCount E P).cell m (Nat.pair (encE E e) b) = {e} ×ˢ P.cell m b := by
  ext ⟨e', t⟩
  simp only [cell, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_prod]
  change Nat.pair (encE E e') (P.idx m t) = Nat.pair (encE E e) b ↔ e' = e ∧ P.idx m t = b
  rw [Nat.pair_eq_pair]
  exact ⟨fun h => ⟨encE_injective E h.1, h.2⟩, fun h => ⟨by rw [h.1], h.2⟩⟩

/-- Examples (c): `# ⊗ λ` is dissected by `prodCount`. -/
theorem prodCount_isDissecting (P : SepPartSeq T) (lam : Measure T) [SFinite lam]
    (hP : P.IsDissecting lam) :
    (prodCount E P).IsDissecting (Measure.count.prod lam) := by
  intro i
  have hsub : (prodCount E P).cell 0 i ⊆
      {e | encE E e = (Nat.unpair i).1} ×ˢ P.cell 0 (Nat.unpair i).2 := by
    rintro ⟨e, t⟩ h
    have h' : Nat.pair (encE E e) (P.idx 0 t) = i := h
    have := Nat.unpair_pair (encE E e) (P.idx 0 t)
    rw [h'] at this
    exact ⟨congrArg Prod.fst this.symm, congrArg Prod.snd this.symm⟩
  refine lt_of_le_of_lt (measure_mono hsub) ?_
  rw [Measure.prod_prod]
  have hcount : (Measure.count : Measure E) {e | encE E e = (Nat.unpair i).1} ≤ 1 := by
    by_cases hne : ∃ e0, encE E e0 = (Nat.unpair i).1
    · obtain ⟨e0, he0⟩ := hne
      have : {e | encE E e = (Nat.unpair i).1} ⊆ {e0} := fun e he =>
        encE_injective E (he.trans he0.symm)
      refine (measure_mono this).trans ?_
      simp
    · have : {e | encE E e = (Nat.unpair i).1} = ∅ := by
        ext e; exact ⟨fun he => (hne ⟨e, he⟩).elim, fun h => h.elim⟩
      rw [this]; simp
  exact lt_of_le_of_lt (mul_le_mul_left hcount _) (by simpa using hP _)

end SepPartSeq

end ElboimSly
