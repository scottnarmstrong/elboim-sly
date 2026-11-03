/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycFinalSpec
public import ElboimSly.Foundations.Cyclic.CycDrivenEvents
public import ElboimSly.Foundations.Cyclic.CycRingMeas
public import ElboimSly.Foundations.Cyclic.CycPiece
public import Mathlib

/-!
# Basic properties of world-lines (d): first events of classes (helpers)

Basic properties of world-lines (d). The per-event dichotomy: an event of a driven path is either a
(D1′) event (its class is already in `Q_{<r}`) or a (D2′) event (the driver jumps and the
update is fresh). Also the finiteness of the set of clock values of known rings.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

variable {I : Type*} [MeasurableSpace I] {d : ℕ} {β : ℝ} [Fact (0 < β)]

omit [MeasurableSpace I] [Fact (0 < β)] in
/-- The per-event dichotomy: a nontrivial update is (D1′) or (D2′). -/
theorem RuleFn.dichotomy {δ : CycData I d} {θ : AddCircle β} {w v : Fin d → ℤ}
    {Z Q' : Set (I × RingSpace d β)} {jmp : Prop} {dv : Fin d → ℤ}
    (h : RuleFn δ θ w v Z Q' jmp dv) (hne : v ≠ w) :
    (∃ e : Edge d, Edge.Mem w e ∧ (δ.copy, (e, θ)) ∈ Q' ∧ e.1 = s(w, v)) ∨
      ((¬ ∃ e : Edge d, Edge.Mem w e ∧ (δ.copy, (e, θ)) ∈ Q') ∧ jmp ∧
        (∀ e : Edge d, e.1 = s(w, w + dv) → (δ.copy, (e, θ)) ∉ Z) ∧ v = w + dv) := by
  classical
  obtain ⟨d1, d2, d3⟩ := h
  by_cases hc : ∃ e : Edge d, Edge.Mem w e ∧ (δ.copy, (e, θ)) ∈ Q'
  · left
    let S : Set ℕ := {n | ∃ e : Edge d, Edge.Mem w e ∧ (δ.copy, (e, θ)) ∈ Q' ∧ n = edgeEnc e}
    have hSne : S.Nonempty := by
      obtain ⟨e, h1, h2⟩ := hc
      exact ⟨_, e, h1, h2, rfl⟩
    obtain ⟨e0, h1, h2, h3⟩ := Nat.sInf_mem hSne
    exact ⟨e0, h1, h2, d1 e0 h1 h2 (fun e' a b => by rw [← h3]; exact Nat.sInf_le ⟨e', a, b, rfl⟩)⟩
  · right
    by_cases hj : jmp ∧ ∀ e : Edge d, e.1 = s(w, w + dv) → (δ.copy, (e, θ)) ∉ Z
    · exact ⟨hc, hj.1, hj.2, d2 hc hj.1 hj.2⟩
    · exact absurd (d3 hc hj) hne

omit [MeasurableSpace I] [Fact (0 < β)] in
/-- The clock values of the known rings of a record of entries of finite length are finite. -/
theorem finite_clock_ringSet {k : ℕ} (f : CycRecN I d k) (hf : ∀ i, (f i).len ≠ ⊤) :
    {θ : AddCircle β | ∃ x ∈ CycRec.ringSet β (Sum.inl ⟨k, f⟩ : CycRec I d), x.2.2 = θ}.Finite := by
  have hsub : {θ : AddCircle β | ∃ x ∈ CycRec.ringSet β (Sum.inl ⟨k, f⟩ : CycRec I d),
      x.2.2 = θ} ⊆ ⋃ i : Fin k, (fun r : ℝ≥0 => (f i).data.clock β r) ''
        (CDisc (f i).path.fn ∩ Iic (f i).len.toNNReal) := by
    rintro θ ⟨x, ⟨e, ⟨j, hj⟩, hx⟩, rfl⟩
    have hjk : j < k := by
      by_contra hh
      simp [CycRec.nth, hh] at hj
    have hej : e = f ⟨j, hjk⟩ := by
      simp [CycRec.nth, hjk] at hj
      exact hj.symm
    subst hej
    obtain ⟨r, hr0, hrl, hne, -, h2, -⟩ := hx
    refine mem_iUnion.mpr ⟨⟨j, hjk⟩, r, ⟨(CPath.mem_CDisc_iff _ hr0).mpr hne, ?_⟩, h2.symm⟩
    have := hf ⟨j, hjk⟩
    show r ≤ _
    have h3 : (r : ℝ≥0∞) ≤ (f ⟨j, hjk⟩).len := hrl
    rw [← ENNReal.coe_le_coe, ENNReal.coe_toNNReal this]
    exact h3
  refine Set.Finite.subset (Set.finite_iUnion fun i => ?_) hsub
  exact ((f i).path.fin _).image _

namespace CycPlan

variable (P : CycPlan I d β) {J : Type*} (jx : ∀ k : ℕ, CycRecN I d k → J) (X : J → CycPath d)

end CycPlan

namespace CycPlan

variable (P : CycPlan I d β) {J : Type*} (jx : ∀ k : ℕ, CycRecN I d k → J) (X : J → CycPath d)

end CycPlan

namespace CycPlan

variable (P : CycPlan I d β) {J : Type*} (jx : ∀ k : ℕ, CycRecN I d k → J) (X : J → CycPath d)

end CycPlan

end ElboimSly.Cyclic

end
