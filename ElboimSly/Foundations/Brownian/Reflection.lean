/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Brownian.Markov
public import ElboimSly.Foundations.Brownian.Gauss1d
import Mathlib

/-!
# Reflection inequality on a finite grid

Reflection inequality on a finite grid.

For a coordinate `b = B^i` of a standard `d`-dimensional Brownian motion (which by
Invariances (d) is a standard `1`-dimensional Brownian motion; here the argument is run
directly in the filtration of `B`), `h > 0`, `N ≥ 1`, `u_k = k h / N`:
`P(max_{k ≤ N} b(u_k) ≥ a) ≤ 2 P(b(h) ≥ a)`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace ElboimSly.Brownian

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {d : ℕ}

/-- The grid point `u_k = k h / N`. -/
noncomputable def gridPt (h : ℝ≥0) (N k : ℕ) : ℝ≥0 := (k : ℝ≥0) * h / N

lemma gridPt_mono (h : ℝ≥0) (N : ℕ) : Monotone (gridPt h N) := fun j k hjk => by
  unfold gridPt
  gcongr

lemma gridPt_le (h : ℝ≥0) {N k : ℕ} (hN : N ≠ 0) (hk : k ≤ N) : gridPt h N k ≤ h := by
  unfold gridPt
  have hN' : (N : ℝ≥0) ≠ 0 := by exact_mod_cast hN
  rw [div_le_iff₀ (pos_iff_ne_zero.2 hN')]
  calc (k : ℝ≥0) * h ≤ N * h := by gcongr
    _ = h * N := mul_comm _ _

/-- Reflection inequality on a finite grid. -/
theorem _root_.ElboimSly.IsStandardBrownianMotion.reflection [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → (Fin d → ℝ)} (hB : IsStandardBrownianMotion d B P) (i : Fin d) {h : ℝ≥0}
    {N : ℕ} (hN : N ≠ 0) (a : ℝ) :
    P {ω | ∃ k ≤ N, a ≤ B (gridPt h N k) ω i} ≤ 2 * P {ω | a ≤ B h ω i} := by
  classical
  set u : ℕ → ℝ≥0 := gridPt h N with hu
  have hbm : ∀ t, Measurable (fun ω => B t ω i) := fun t =>
    (measurable_pi_apply i).comp (hB.measurable t)
  let A : ℕ → Set Ω := fun k => {ω | a ≤ B (u k) ω i ∧ ∀ j < k, B (u j) ω i < a}
  let G : ℕ → Set Ω := fun k => {ω | 0 ≤ B h ω i - B (u k) ω i}
  have hAF : ∀ k, MeasurableSet[bmFiltration B (u k)] (A k) := by
    intro k
    let _ : MeasurableSpace Ω := bmFiltration B (u k)
    have hmb : ∀ j ≤ k, Measurable (fun ω => B (u j) ω i) := fun j hj =>
      (measurable_pi_apply i).comp (measurable_bmFiltration (gridPt_mono h N hj))
    have e : A k = {ω | a ≤ B (u k) ω i} ∩ ⋂ j ∈ Finset.range k, {ω | B (u j) ω i < a} := by
      ext ω; simp [A]
    rw [e]
    refine (measurableSet_le measurable_const (hmb k le_rfl)).inter ?_
    exact Finset.measurableSet_biInter _ fun j hj =>
      measurableSet_lt (hmb j (Finset.mem_range.1 hj).le) measurable_const
  have hAm : ∀ k, MeasurableSet (A k) := fun k => bmFiltration_le hB.measurable _ _ (hAF k)
  have hGm : ∀ k, MeasurableSet (G k) := fun k =>
    measurableSet_le measurable_const ((hbm h).sub (hbm (u k)))
  have hAGm : ∀ k, MeasurableSet (A k ∩ G k) := fun k => (hAm k).inter (hGm k)
  -- independence: `P (A k ∩ G k) = P (A k) * P (G k)` for `k ≤ N`
  have hind : ∀ k ≤ N, P (A k ∩ G k) = P (A k) * P (G k) := by
    intro k hk
    have hI := hB.indep_increment (gridPt_le h hN hk)
    rw [Indep_iff] at hI
    have hG' : MeasurableSet[MeasurableSpace.comap (fun ω => B h ω - B (u k) ω) inferInstance]
        (G k) := ⟨{z : Fin d → ℝ | 0 ≤ z i}, measurableSet_le measurable_const
          (measurable_pi_apply i), by ext ω; simp [G]⟩
    rw [Set.inter_comm, hI _ _ hG' (hAF k), mul_comm]
  have hGhalf : ∀ k ≤ N, (1 / 2 : ℝ≥0∞) ≤ P (G k) := by
    intro k hk
    have hsh := (hB.isPreBrownianReal i).shift (u k)
    have hlaw := hsh.hasLaw_eval (h - u k)
    have e : u k + (h - u k) = h := add_tsub_cancel_of_le (gridPt_le h hN hk)
    simp only [e] at hlaw
    exact half_le_measure_nonneg_of_hasLaw ((hbm h).sub (hbm (u k))) hlaw
  -- the first-passage decomposition
  have hsub : {ω | ∃ k ≤ N, a ≤ B (u k) ω i} ⊆ ⋃ k ∈ Finset.range (N + 1), A k := by
    intro ω ⟨k, hk, hak⟩
    have hex : ∃ k, a ≤ B (u k) ω i := ⟨k, hak⟩
    let m := Nat.find hex
    have hm : a ≤ B (u m) ω i := Nat.find_spec hex
    have hmk : m ≤ k := Nat.find_min' hex hak
    simp only [Set.mem_iUnion, Finset.mem_range]
    exact ⟨m, by omega, hm, fun j hj => not_le.1 (Nat.find_min hex hj)⟩
  have hdisj : Pairwise (Function.onFun Disjoint fun k => A k ∩ G k) := by
    intro j k hjk
    wlog hlt : j < k generalizing j k
    · exact (this hjk.symm (lt_of_le_of_ne (not_lt.1 hlt) hjk.symm)).symm
    refine Set.disjoint_left.2 fun ω hj hk => ?_
    exact absurd (hk.1.2 j hlt) (not_lt.2 hj.1.1)
  have hGsub : ∀ k ≤ N, A k ∩ G k ⊆ {ω | a ≤ B h ω i} := by
    intro k _ ω ⟨⟨hak, _⟩, hG⟩
    simp only [G, Set.mem_ofPred_eq] at hG ⊢
    linarith
  calc P {ω | ∃ k ≤ N, a ≤ B (u k) ω i}
      ≤ P (⋃ k ∈ Finset.range (N + 1), A k) := measure_mono hsub
    _ ≤ ∑ k ∈ Finset.range (N + 1), P (A k) := measure_biUnion_finset_le _ _
    _ ≤ ∑ k ∈ Finset.range (N + 1), 2 * P (A k ∩ G k) := by
        refine Finset.sum_le_sum fun k hk => ?_
        have hk' : k ≤ N := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
        rw [hind k hk']
        calc P (A k) = 2 * ((1 / 2) * P (A k)) := by
              rw [← mul_assoc, show (2 : ℝ≥0∞) * (1 / 2) = 1 by
                rw [one_div, ENNReal.mul_inv_cancel (by norm_num) (by norm_num)], one_mul]
          _ ≤ 2 * (P (A k) * P (G k)) := by
              rw [mul_comm (1 / 2 : ℝ≥0∞)]
              gcongr
              exact hGhalf k hk'
    _ = 2 * ∑ k ∈ Finset.range (N + 1), P (A k ∩ G k) := by rw [Finset.mul_sum]
    _ = 2 * P (⋃ k ∈ Finset.range (N + 1), A k ∩ G k) := by
        rw [measure_biUnion_finset (fun j _ k _ hjk => hdisj hjk) fun k _ => hAGm k]
    _ ≤ 2 * P {ω | a ≤ B h ω i} := by
        gcongr
        exact Set.iUnion₂_subset fun k hk => hGsub k (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk))

end ElboimSly.Brownian
