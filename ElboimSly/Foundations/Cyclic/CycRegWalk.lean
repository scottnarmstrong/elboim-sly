/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycFinalNth
public import Mathlib

/-!
# The regenerated walk of a record, and the gluing of pieces

The constructions of the regenerated walk (the definition `W_reg(ρ)(s) = p_k(s - Λ_{k-1})` for
`s ∈ [Λ_{k-1}, Λ_k)`), and the gluing of regenerated cyclic walk.

* `gluedWalk σ w` glues pieces `w k` at the times `σ k` (the last `σ k ≤ t` is used).
* `regRecWalk ρ` is `W_reg(ρ)`.
* `regRecWalk_cycFinal`: if the world-line `k` of the plan has length `τ k` and follows `w k` up to
  `τ k`, then `W_reg` of the final record is the gluing of the pieces `w k` at the partial sums
  of the `τ k`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

variable {d : ℕ}

/-- The number of pieces completed by time `t`: `max {k : σ k ≤ t}`. -/
noncomputable def gluedCount (σ : ℕ → ℝ≥0∞) (t : ℝ≥0) : ℕ := sSup {k : ℕ | σ k ≤ t}

/-- The gluing of the pieces `w k` at the times `σ k`: `W(t) = w N (t - σ N)`, `N = max {k : σ k ≤ t}`. -/
noncomputable def gluedWalk {V : Type*} (σ : ℕ → ℝ≥0∞) (w : ℕ → ℝ≥0 → V) (t : ℝ≥0) : V :=
  w (gluedCount σ t) (t - (σ (gluedCount σ t)).toNNReal)

/-- The partial sums `σ i = ∑_{k < i} τ k`. -/
noncomputable def partialSums (τ : ℕ → ℝ≥0∞) (i : ℕ) : ℝ≥0∞ := ∑ k ∈ Finset.range i, τ k

/-- `W_reg(ρ)(t) = p_N(t - Λ_N)`, `N = max {k : Λ_k ≤ t}`. -/
noncomputable def regRecWalk {I : Type*} (ρ : CycRec I d) (t : ℝ≥0) : Fin d → ℤ :=
  ((ρ.nth (gluedCount (fun k => ρ.cum k) t)).map fun e => e.path.fn).getD (fun _ => 0)
    (t - (ρ.cum (gluedCount (fun k => ρ.cum k) t)).toNNReal)

variable {I : Type*} [MeasurableSpace I] {β : ℝ} [Fact (0 < β)]

theorem partialSums_succ (τ : ℕ → ℝ≥0∞) (k : ℕ) :
    partialSums τ (k + 1) = partialSums τ k + τ k := by
  simp [partialSums, Finset.sum_range_succ]

theorem gluedCount_spec {σ : ℕ → ℝ≥0∞} {t : ℝ≥0} (h0 : σ 0 = 0)
    (hbdd : BddAbove {k : ℕ | σ k ≤ t}) :
    σ (gluedCount σ t) ≤ t ∧ t < σ (gluedCount σ t + 1) := by
  have hne : ({k : ℕ | σ k ≤ t}).Nonempty := ⟨0, by simp [h0]⟩
  refine ⟨Nat.sSup_mem hne hbdd, ?_⟩
  by_contra h
  rw [not_lt] at h
  have : gluedCount σ t + 1 ≤ gluedCount σ t := le_csSup hbdd h
  omega

theorem sum_ge_nsmul {τ : ℕ → ℝ≥0∞} {b : ℝ≥0∞} (hτ : ∀ k, b ≤ τ k) (k : ℕ) :
    (k : ℝ≥0∞) * b ≤ partialSums τ k := by
  unfold partialSums
  calc (k : ℝ≥0∞) * b = ∑ _i ∈ Finset.range k, b := by simp
    _ ≤ _ := Finset.sum_le_sum fun i _ => hτ i

namespace CycPlan

variable (P : CycPlan I d β) (path : PathRule I d)

omit [Fact (0 < β)] in
theorem partialSums_top_of_not_allFin (τ : ℕ → ℝ≥0∞)
    (hE : ∀ k, P.AllFin path k → (P.E path k).len = τ k) {k : ℕ} (hA : ¬ P.AllFin path k) :
    partialSums τ k = ⊤ := by
  classical
  unfold AllFin at hA
  push Not at hA
  have hex : ∃ i, ¬ (P.E path i).len < ⊤ := by
    obtain ⟨i, _, hi⟩ := hA
    exact ⟨i, not_lt.2 hi⟩
  set i0 := Nat.find hex with hi0
  have hi0k : i0 < k := by
    obtain ⟨i, hik, hi⟩ := hA
    exact lt_of_le_of_lt (Nat.find_min' hex (not_lt.2 hi)) hik
  have hall : P.AllFin path i0 := fun j hj => by
    have := Nat.find_min hex hj
    exact not_not.1 this
  have h1 : (P.E path i0).len = ⊤ := top_unique (not_lt.1 (Nat.find_spec hex))
  have h2 : τ i0 = ⊤ := by rw [← hE i0 hall]; exact h1
  refine top_unique ?_
  rw [← h2]
  exact Finset.single_le_sum (f := τ) (fun _ _ => zero_le) (Finset.mem_range.2 hi0k)

omit [Fact (0 < β)] in
/-- **`W_reg` of the final record is the gluing of the pieces.** -/
theorem regRecWalk_cycFinal (hK : P.K = ⊤) {b : ℝ≥0} (hb : 0 < b) (τ : ℕ → ℝ≥0∞)
    (w : ℕ → ℝ≥0 → Fin d → ℤ) (hτ : ∀ k, (b : ℝ≥0∞) ≤ τ k)
    (hE : ∀ k, P.AllFin path k → (P.E path k).len = τ k ∧
      ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ τ k → (P.E path k).path.fn s = w k s) (t : ℝ≥0) :
    regRecWalk (P.cycFinal path) t = gluedWalk (partialSums τ) w t := by
  classical
  set ρ := P.cycFinal path with hρ
  have hnth := P.cycFinal_nth path hK
  have hE1 : ∀ k, P.AllFin path k → (P.E path k).len = τ k := fun k hk => (hE k hk).1
  have hcum : ∀ k, ρ.cum k = partialSums τ k := by
    intro k
    induction k with
    | zero => simp [CycRec.cum, partialSums]
    | succ k ih =>
      rw [partialSums_succ, ← ih]
      unfold CycRec.cum
      rw [Finset.sum_range_succ]
      by_cases hA : P.AllFin path k
      · have hn : ρ.nth k = some (P.E path k) := by rw [hnth k, ite_eq_left hA]
        have : ρ.lenAt k = τ k := by
          show (ρ.nth k).elim 0 CycEntry.len = τ k
          rw [hn]; exact hE1 k hA
        rw [this]
      · have hT : partialSums τ k = ⊤ := P.partialSums_top_of_not_allFin path τ hE1 hA
        have h2 : ∑ i ∈ Finset.range k, ρ.lenAt i = ⊤ := by
          have := ih
          unfold CycRec.cum at this
          rw [this]; exact hT
        rw [h2]; simp
  have hfun : (fun k => ρ.cum k) = partialSums τ := funext hcum
  have h0 : partialSums τ 0 = 0 := by simp [partialSums]
  have hbdd : BddAbove {k : ℕ | partialSums τ k ≤ t} := by
    refine ⟨⌈(t : ℝ) / b⌉₊, fun k hk => ?_⟩
    have h1 : (k : ℝ≥0∞) * b ≤ t :=
      (sum_ge_nsmul hτ k).trans hk
    have h2 : (k : ℝ≥0) * b ≤ t := by exact_mod_cast h1
    have h3 : (k : ℝ) ≤ t / b := by
      rw [le_div_iff₀ (by exact_mod_cast hb)]
      exact_mod_cast h2
    exact (Nat.cast_le.1 (h3.trans (Nat.le_ceil _)))
  obtain ⟨hN1, hN2⟩ := gluedCount_spec h0 hbdd
  set N := gluedCount (partialSums τ) t with hN
  have hallN : P.AllFin path N := by
    by_contra hA
    have := P.partialSums_top_of_not_allFin path τ hE1 hA
    rw [this] at hN1
    exact absurd hN1 (by simp)
  have hnthN : ρ.nth N = some (P.E path N) := by rw [hnth N, ite_eq_left hallN]
  have hσN : partialSums τ N ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top hN1
  unfold regRecWalk gluedWalk
  rw [hfun, ← hN, hcum N, hnthN]
  simp only [Option.map_some, Option.getD_some]
  refine (hE N hallN).2 _ ?_
  rw [ENNReal.coe_sub, ENNReal.coe_toNNReal hσN, tsub_le_iff_left]
  have := hN2
  rw [partialSums_succ] at this
  exact this.le

end CycPlan

end ElboimSly.Cyclic

end
