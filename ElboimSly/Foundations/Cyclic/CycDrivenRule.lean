/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycLines
public import Mathlib

/-!
# The driven rules as a function of local data

Basic properties of world-lines (c). `RuleFn` is the conjunction (D1′)–(D3′) at one time, as a
predicate on the left limit `w`, the new value `v`, the sets `Z`, `Q'` and the driver data.
It has exactly one solution `v` (`RuleFn.exists_val`, `RuleFn.unique`), and `IsDriven` is
`RuleFn` at every time (`isDriven_iff`).
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

variable {I : Type*} [MeasurableSpace I] {d : ℕ} {β : ℝ} [Fact (0 < β)]

/-- (D1′)–(D3′) at one time. -/
def RuleFn (δ : CycData I d) (θ : AddCircle β) (w v : Fin d → ℤ) (Z Q' : Set (I × RingSpace d β))
    (jmp : Prop) (dv : Fin d → ℤ) : Prop :=
  (∀ e : Edge d, Edge.Mem w e → (δ.copy, (e, θ)) ∈ Q' →
      (∀ e' : Edge d, Edge.Mem w e' → (δ.copy, (e', θ)) ∈ Q' → edgeEnc e ≤ edgeEnc e') →
        e.1 = s(w, v)) ∧
    ((¬ ∃ e : Edge d, Edge.Mem w e ∧ (δ.copy, (e, θ)) ∈ Q') → jmp →
      (∀ e : Edge d, e.1 = s(w, w + dv) → (δ.copy, (e, θ)) ∉ Z) → v = w + dv) ∧
    ((¬ ∃ e : Edge d, Edge.Mem w e ∧ (δ.copy, (e, θ)) ∈ Q') →
      ¬ (jmp ∧ ∀ e : Edge d, e.1 = s(w, w + dv) → (δ.copy, (e, θ)) ∉ Z) → v = w)

/-- Own explored region before `r`. -/
def drvZown (β : ℝ) (δ : CycData I d) (p : CPath (Fin d → ℤ)) (r : ℝ≥0) :
    Set (I × RingSpace d β) :=
  {x | ∃ r' : ℝ≥0, 0 < r' ∧ r' < r ∧ x.1 = δ.copy ∧ x.2.2 = δ.clock β r' ∧
    Edge.Mem (p.left r') x.2.1}

/-- Own known rings before `r`. -/
def drvQown (β : ℝ) (δ : CycData I d) (p : CPath (Fin d → ℤ)) (r : ℝ≥0) :
    Set (I × RingSpace d β) :=
  {x | ∃ r' : ℝ≥0, 0 < r' ∧ r' < r ∧ p.left r' ≠ p.fn r' ∧ x.1 = δ.copy ∧
    x.2.2 = δ.clock β r' ∧ x.2.1.1 = s(p.left r', p.fn r')}

/-- The driven rules at time `r`. -/
def DrvRule (β : ℝ) [Fact (0 < β)] (R Q : Set (I × RingSpace d β)) (δ : CycData I d)
    (X : CPath (Fin d → ℤ)) (a : ℝ≥0) (p : CPath (Fin d → ℤ)) (r : ℝ≥0) : Prop :=
  RuleFn δ (δ.clock β r) (p.left r) (p.fn r) (R ∪ drvZown β δ p r) (Q ∪ drvQown β δ p r)
    (X.left (a + r) ≠ X.fn (a + r)) (X.fn (a + r) - X.left (a + r))

omit [MeasurableSpace I] in
theorem isDriven_iff {R Q : Set (I × RingSpace d β)} {δ : CycData I d}
    {X : CPath (Fin d → ℤ)} {a : ℝ≥0} {p : CPath (Fin d → ℤ)} :
    IsDriven β R Q δ X a p ↔
      p.len = ⊤ ∧ p.fn 0 = δ.start ∧ ∀ r : ℝ≥0, 0 < r → DrvRule β R Q δ X a p r := Iff.rfl

omit [MeasurableSpace I] [Fact (0 < β)] in
theorem RuleFn.exists_val (δ : CycData I d) (θ : AddCircle β) (w : Fin d → ℤ)
    (Z Q' : Set (I × RingSpace d β)) (jmp : Prop) (dv : Fin d → ℤ) :
    ∃ v, RuleFn δ θ w v Z Q' jmp dv := by
  classical
  by_cases hc : ∃ e : Edge d, Edge.Mem w e ∧ (δ.copy, (e, θ)) ∈ Q'
  · let S : Set ℕ := {n | ∃ e : Edge d, Edge.Mem w e ∧ (δ.copy, (e, θ)) ∈ Q' ∧ n = edgeEnc e}
    have hSne : S.Nonempty := by
      obtain ⟨e, h1, h2⟩ := hc
      exact ⟨_, e, h1, h2, rfl⟩
    obtain ⟨e0, h1, h2, h3⟩ := Nat.sInf_mem hSne
    have hmin : ∀ e' : Edge d, Edge.Mem w e' → (δ.copy, (e', θ)) ∈ Q' →
        edgeEnc e0 ≤ edgeEnc e' := fun e' a b => by
      rw [← h3]; exact Nat.sInf_le ⟨e', a, b, rfl⟩
    have hw : w ∈ e0.1 := h1
    refine ⟨Sym2.Mem.other hw, ?_, fun hn => absurd hc hn, fun hn => absurd hc hn⟩
    intro e he he2 hle
    have : e = e0 := by
      have : edgeEnc e = edgeEnc e0 := le_antisymm (hle e0 h1 h2) (hmin e he he2)
      exact @Encodable.encode_injective _ (Encodable.ofCountable (Edge d)) _ _ this
    subst this
    exact (Sym2.other_spec hw).symm
  · by_cases hj : jmp ∧ ∀ e : Edge d, e.1 = s(w, w + dv) → (δ.copy, (e, θ)) ∉ Z
    · exact ⟨w + dv, fun e he he2 _ => absurd ⟨e, he, he2⟩ hc, fun _ _ _ => rfl,
        fun _ hn => absurd hj hn⟩
    · exact ⟨w, fun e he he2 _ => absurd ⟨e, he, he2⟩ hc,
        fun _ h1 h2 => absurd ⟨h1, h2⟩ hj, fun _ _ => rfl⟩

omit [MeasurableSpace I] [Fact (0 < β)] in
theorem RuleFn.unique {δ : CycData I d} {θ : AddCircle β} {w v v' : Fin d → ℤ}
    {Z Q' : Set (I × RingSpace d β)} {jmp : Prop} {dv : Fin d → ℤ}
    (h : RuleFn δ θ w v Z Q' jmp dv) (h' : RuleFn δ θ w v' Z Q' jmp dv) : v = v' := by
  classical
  obtain ⟨d1, d2, d3⟩ := h
  obtain ⟨d1', d2', d3'⟩ := h'
  by_cases hc : ∃ e : Edge d, Edge.Mem w e ∧ (δ.copy, (e, θ)) ∈ Q'
  · let S : Set ℕ := {n | ∃ e : Edge d, Edge.Mem w e ∧ (δ.copy, (e, θ)) ∈ Q' ∧ n = edgeEnc e}
    have hSne : S.Nonempty := by
      obtain ⟨e, h1, h2⟩ := hc
      exact ⟨_, e, h1, h2, rfl⟩
    obtain ⟨e0, h1, h2, h3⟩ := Nat.sInf_mem hSne
    have hmin : ∀ e' : Edge d, Edge.Mem w e' → (δ.copy, (e', θ)) ∈ Q' →
        edgeEnc e0 ≤ edgeEnc e' := fun e' a b => by
      rw [← h3]; exact Nat.sInf_le ⟨e', a, b, rfl⟩
    exact Sym2.congr_right.mp ((d1 e0 h1 h2 hmin).symm.trans (d1' e0 h1 h2 hmin))
  · by_cases hj : jmp ∧ ∀ e : Edge d, e.1 = s(w, w + dv) → (δ.copy, (e, θ)) ∉ Z
    · rw [d2 hc hj.1 hj.2, d2' hc hj.1 hj.2]
    · rw [d3 hc hj, d3' hc hj]

omit [MeasurableSpace I] [Fact (0 < β)] in
theorem RuleFn.of_stay {δ : CycData I d} {θ : AddCircle β} {w : Fin d → ℤ}
    {Z Q' : Set (I × RingSpace d β)} {jmp : Prop} {dv : Fin d → ℤ}
    (hq : ¬ ∃ e : Edge d, Edge.Mem w e ∧ (δ.copy, (e, θ)) ∈ Q') (hj : ¬ jmp) :
    RuleFn δ θ w w Z Q' jmp dv :=
  ⟨fun e he he2 _ => absurd ⟨e, he, he2⟩ hq, fun _ h1 _ => absurd h1 hj, fun _ _ => rfl⟩

end ElboimSly.Cyclic

end
