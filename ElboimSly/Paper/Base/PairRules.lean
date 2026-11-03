/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycDrivenRegionRules
public import ElboimSly.Foundations.Cyclic.CycDrivenExists
public import Mathlib

/-!
# The driven rules (D1')-(D3') in the situation of cyclic walks within one lap

Cyclic walks within one lap (b), (c), "Walk 1" and "Walk 2".

* `ruleFn_none`: if there is no known ring and no explored region at the cyclic time, the rule says
  that the walk follows the driving jump (if any).
* `ruleFn_pair`: if the only known ring at the cyclic time is the edge `{l, n}` of a jump of the
  other walk, and the explored region is the set of edges containing `l`, the rule is the
  rule (F1)-(F3) of the two-particle map.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Paper

open ElboimSly.Cyclic

variable {I : Type*} [MeasurableSpace I] {d : ℕ} {β : ℝ} [Fact (0 < β)]
  {δ : CycData I d} {θ : AddCircle β}

omit [MeasurableSpace I] [Fact (0 < β)] in
theorem ruleFn_none {w v dv : Fin d → ℤ} {Z Q' : Set (I × RingSpace d β)} {jmp : Prop}
    (hQ : ∀ e : Edge d, (δ.copy, (e, θ)) ∉ Q') (hZ : ∀ e : Edge d, (δ.copy, (e, θ)) ∉ Z)
    (h1 : jmp → v = w + dv) (h2 : ¬ jmp → v = w) : RuleFn δ θ w v Z Q' jmp dv := by
  refine ⟨fun e _ he _ => absurd he (hQ e), fun _ hj _ => h1 hj, fun _ hj => h2 ?_⟩
  exact fun h => hj ⟨h, fun e _ => hZ e⟩

omit [MeasurableSpace I] [Fact (0 < β)] in
theorem ruleFn_pair {w v l n dv : Fin d → ℤ} {Z Q' : Set (I × RingSpace d β)} {jmp : Prop}
    (hQ : ∀ e : Edge d, (δ.copy, (e, θ)) ∈ Q' ↔ (l ≠ n ∧ e.1 = s(l, n)))
    (hZ : ∀ e : Edge d, (δ.copy, (e, θ)) ∈ Z ↔ l ∈ e.1)
    (hln : l ≠ n → ∑ i, |l i - n i| = 1) (hdv : jmp → ∑ i, |dv i| = 1)
    (h1 : (l ≠ n ∧ (w = l ∨ w = n)) → v = (open Classical in if w = l then n else l))
    (h2 : ¬ (l ≠ n ∧ (w = l ∨ w = n)) → (jmp ∧ l ≠ w ∧ l ≠ w + dv) → v = w + dv)
    (h3 : ¬ (l ≠ n ∧ (w = l ∨ w = n)) → ¬ (jmp ∧ l ≠ w ∧ l ≠ w + dv) → v = w) :
    RuleFn δ θ w v Z Q' jmp dv := by
  classical
  have hno : (¬ ∃ e : Edge d, Edge.Mem w e ∧ (δ.copy, (e, θ)) ∈ Q') →
      ¬ (l ≠ n ∧ (w = l ∨ w = n)) := by
    rintro hn ⟨hne, hw⟩
    refine hn ⟨unitEdge l n (hln hne), ?_, (hQ _).2 ⟨hne, rfl⟩⟩
    show w ∈ s(l, n)
    rcases hw with rfl | rfl
    · exact Sym2.mem_mk_left _ _
    · exact Sym2.mem_mk_right _ _
  refine ⟨?_, ?_, ?_⟩
  · intro e hwe heQ _
    obtain ⟨hne, he⟩ := (hQ e).1 heQ
    have hw : w ∈ s(l, n) := he ▸ hwe
    have hw' : w = l ∨ w = n := Sym2.mem_iff.1 hw
    rw [h1 ⟨hne, hw'⟩, he]
    split_ifs with h
    · rw [h]
    · have : w = n := hw'.resolve_left h
      rw [this, Sym2.eq_swap]
  · intro hn hj hZ'
    have hc := hno hn
    refine h2 hc ⟨hj, ?_⟩
    have hdv1 := hdv hj
    have hedge : ∑ i, |w i - (w + dv) i| = 1 := by
      rw [← hdv1]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp
    have hnZ := hZ' (unitEdge w (w + dv) hedge) rfl
    rw [Ne, Ne, ← not_or]
    intro hlw
    apply hnZ
    rw [hZ]
    show l ∈ s(w, w + dv)
    rcases hlw with h | h
    · rw [h]; exact Sym2.mem_mk_left _ _
    · rw [h]; exact Sym2.mem_mk_right _ _
  · intro hn hj
    refine h3 (hno hn) fun ⟨hjm, hl1, hl2⟩ => hj ⟨hjm, fun e he hmem => ?_⟩
    rw [hZ] at hmem
    rw [he] at hmem
    rcases Sym2.mem_iff.1 hmem with h | h
    · exact hl1 h
    · exact hl2 h

end ElboimSly.Paper

end
