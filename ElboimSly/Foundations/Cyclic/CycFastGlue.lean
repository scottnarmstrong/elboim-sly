/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycFarRc
public import ElboimSly.Foundations.Cyclic.CycThitDriven
public import Mathlib

/-!
# ES22 Claim 2.3, Step 3: windows of the glued walk lie in one piece

ES22 Claim 2.3, Step 3. For a glued walk (pieces `w i` glued at the partial sums `σ`
of closing times `τ i`, each a positive integer multiple of `b` or `⊤`, each piece returning to `0`
at its closing time), every window `[k b, (k+1) b]` lies in one piece `[σ_j, σ_{j+1}]` with
`σ_j = l b`, `j ≤ l ≤ k`, and there the glued walk is `w j (· - l b)` (`glued_window`). Then
`window_pairs` turns a pair of times at distance `≤ 1 ≤ b` with a large increment into a pair in a
single window of a single piece with an increment at least half as large.
-/

@[expose] public section

open Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

variable {V : Type*}

theorem partialSums_finite {τ : ℕ → ℝ≥0∞} {b : ℝ≥0}
    (hτ : ∀ i, τ i = ⊤ ∨ ∃ n : ℕ, 1 ≤ n ∧ τ i = ((n * b : ℝ≥0) : ℝ≥0∞)) :
    ∀ j : ℕ, partialSums τ j < ⊤ → ∃ l : ℕ, j ≤ l ∧ partialSums τ j = ((l * b : ℝ≥0) : ℝ≥0∞) := by
  intro j
  induction j with
  | zero => intro _; exact ⟨0, le_rfl, by simp [partialSums]⟩
  | succ j ih =>
    intro h
    rw [partialSums_succ] at h ⊢
    have h1 : partialSums τ j < ⊤ := lt_of_le_of_lt le_self_add h
    have h2 : τ j < ⊤ := lt_of_le_of_lt le_add_self h
    obtain ⟨l, hl, hl'⟩ := ih h1
    rcases hτ j with h3 | ⟨n, hn, h3⟩
    · exact absurd h3 h2.ne
    · refine ⟨l + n, by omega, ?_⟩
      rw [hl', h3, ← ENNReal.coe_add]
      congr 1
      push_cast
      ring

/-- Every window `[k b, (k+1) b]` lies in one piece of the glued walk. -/
theorem glued_window [Zero V] {τ : ℕ → ℝ≥0∞} {b : ℝ≥0} (hb : 0 < b)
    (hτ : ∀ i, τ i = ⊤ ∨ ∃ n : ℕ, 1 ≤ n ∧ τ i = ((n * b : ℝ≥0) : ℝ≥0∞))
    {w : ℕ → ℝ≥0 → V} (hw0 : ∀ i, w i 0 = 0)
    (hwτ : ∀ i (_h : τ i < ⊤), w i (τ i).toNNReal = 0) (k : ℕ) :
    ∃ j l : ℕ, j ≤ l ∧ l ≤ k ∧ ∀ u : ℝ≥0, (k : ℝ≥0) * b ≤ u → u ≤ ((k : ℝ≥0) + 1) * b →
      gluedWalk (partialSums τ) w u = w j (u - l * b) := by
  have hτb : ∀ i, (b : ℝ≥0∞) ≤ τ i := by
    intro i
    rcases hτ i with h | ⟨n, hn, h⟩
    · rw [h]; exact le_top
    · rw [h]
      exact_mod_cast le_mul_of_one_le_left zero_le (by exact_mod_cast hn : (1 : ℝ≥0) ≤ n)
  set σ := partialSums τ with hσ
  have hm : Monotone σ := monotone_nat_of_le_succ fun n => by
    rw [hσ, partialSums_succ]; exact le_self_add
  have h0 : σ 0 = 0 := by simp [hσ, partialSums]
  have hbdd := fun t : ℝ≥0 => bdd_partialSums hb hτb t
  set t0 : ℝ≥0 := k * b with ht0
  obtain ⟨hj1, hj2⟩ := gluedCount_spec h0 (hbdd t0)
  set j := gluedCount σ t0 with hj
  have hσjfin : σ j < ⊤ := lt_of_le_of_lt hj1 ENNReal.coe_lt_top
  obtain ⟨l, hjl, hl⟩ : ∃ l : ℕ, j ≤ l ∧ σ j = ((l * b : ℝ≥0) : ℝ≥0∞) :=
    partialSums_finite hτ j hσjfin
  have hlk : l ≤ k := by
    have : ((l * b : ℝ≥0) : ℝ≥0∞) ≤ ((k * b : ℝ≥0) : ℝ≥0∞) := hl ▸ hj1
    have := ENNReal.coe_le_coe.1 this
    exact_mod_cast le_of_mul_le_mul_right this hb
  refine ⟨j, l, hjl, hlk, fun u hu1 hu2 => ?_⟩
  have hσl : (σ j).toNNReal = l * b := by rw [hl]; simp
  by_cases hA : (u : ℝ≥0∞) < σ (j + 1)
  · have hcnt : gluedCount σ u = j := gluedCount_eq hm (hj1.trans (by exact_mod_cast hu1)) hA
    unfold gluedWalk
    rw [hcnt, hσl]
  · rw [not_lt] at hA
    have hfin : σ (j + 1) < ⊤ := lt_of_le_of_lt hA ENNReal.coe_lt_top
    have hτj : τ j < ⊤ := lt_of_le_of_lt (by rw [hσ, partialSums_succ]; exact le_add_self) hfin
    obtain ⟨n, hn, hτn⟩ := (hτ j).resolve_left hτj.ne
    have hs1 : σ (j + 1) = ((l + n : ℕ) * b : ℝ≥0) := by
      have h2 : σ (j + 1) = σ j + τ j := by rw [hσ]; exact partialSums_succ _ _
      rw [h2, hl, hτn, ← ENNReal.coe_add]
      congr 1
      push_cast
      ring
    have hkn : k < l + n := by
      have : (k : ℝ≥0) * b < ((l + n : ℕ) : ℝ≥0) * b := by
        have h3 : (t0 : ℝ≥0∞) < ((((l + n : ℕ) : ℝ≥0) * b : ℝ≥0) : ℝ≥0∞) := hs1 ▸ hj2
        exact_mod_cast h3
      exact_mod_cast lt_of_mul_lt_mul_right this zero_le
    have hu3 : u = ((l + n : ℕ) : ℝ≥0) * b := by
      apply le_antisymm
      · refine hu2.trans ?_
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hkn) zero_le
      · have : ((((l + n : ℕ) : ℝ≥0) * b : ℝ≥0) : ℝ≥0∞) ≤ (u : ℝ≥0∞) := hs1 ▸ hA
        exact_mod_cast this
    have hcnt : gluedCount σ u = j + 1 := by
      refine gluedCount_eq hm hA ?_
      have h2 : σ (j + 2) = σ (j + 1) + τ (j + 1) := by rw [hσ]; exact partialSums_succ _ _
      rw [h2]
      have : (u : ℝ≥0∞) = σ (j + 1) := by
        rw [hs1, hu3]
      rw [this]
      have hb' : (0 : ℝ≥0∞) < b := by exact_mod_cast hb
      calc σ (j + 1) < σ (j + 1) + b := ENNReal.lt_add_right hfin.ne hb'.ne'
        _ ≤ _ := add_le_add le_rfl (hτb _)
    have hσ1 : (σ (j + 1)).toNNReal = u := by rw [hs1, ENNReal.toNNReal_coe, hu3]
    have hτj' : (τ j).toNNReal = u - l * b := by
      rw [hτn, ENNReal.toNNReal_coe, hu3]
      push_cast
      rw [add_mul, add_tsub_cancel_left]
    unfold gluedWalk
    rw [hcnt, hσ1, tsub_self, hw0, ← hτj']
    exact (hwτ j hτj).symm

variable {d : ℕ}

/-- A pair of times at distance `≤ 1 ≤ b` with an increment `≥ L` yields a pair in one window of
one piece with an increment `≥ L/2`. -/
theorem window_pairs {b : ℝ≥0} (hb1 : 1 ≤ b) {W : ℝ≥0 → Fin d → ℤ} {w : ℕ → ℝ≥0 → Fin d → ℤ}
    (hwin : ∀ k : ℕ, ∃ j l : ℕ, j ≤ l ∧ l ≤ k ∧ ∀ u : ℝ≥0, (k : ℝ≥0) * b ≤ u →
      u ≤ ((k : ℝ≥0) + 1) * b → W u = w j (u - l * b))
    {T : ℝ≥0} {L : ℝ} (hL : 0 ≤ L) {s s' : ℝ≥0} (hss' : s ≤ s') (hsT : s' ≤ T)
    (h1 : s' - s ≤ 1) (hnorm : L ≤ ‖W s' - W s‖) :
    ∃ j m : ℕ, j < ⌊T / b⌋₊ + 1 ∧ m < ⌊T / b⌋₊ + 1 ∧ ∃ u u' : ℝ≥0, u ≤ u' ∧ u' - u ≤ 1 ∧
      (m : ℝ≥0) * b ≤ u ∧ u' ≤ ((m : ℝ≥0) + 1) * b ∧ u ≤ m * b + T ∧ L / 2 ≤ ‖w j u' - w j u‖ := by
  have hb0 : 0 < b := lt_of_lt_of_le one_pos hb1
  -- a pair inside one window
  have key : ∀ (k : ℕ) (x y : ℝ≥0), (k : ℝ≥0) * b ≤ x → x ≤ y → y ≤ ((k : ℝ≥0) + 1) * b →
      y - x ≤ 1 → y ≤ T → k ≤ ⌊T / b⌋₊ → L / 2 ≤ ‖W y - W x‖ →
      ∃ j m : ℕ, j < ⌊T / b⌋₊ + 1 ∧ m < ⌊T / b⌋₊ + 1 ∧ ∃ u u' : ℝ≥0, u ≤ u' ∧ u' - u ≤ 1 ∧
      (m : ℝ≥0) * b ≤ u ∧ u' ≤ ((m : ℝ≥0) + 1) * b ∧ u ≤ m * b + T ∧
        L / 2 ≤ ‖w j u' - w j u‖ := by
    intro k x y hkx hxy hyk hyx hyT hkT hnm
    obtain ⟨j, l, hjl, hlk, hW⟩ := hwin k
    have hx := hW x hkx (hxy.trans hyk)
    have hy := hW y (hkx.trans hxy) hyk
    have hkl : (k : ℝ≥0) = ((k - l : ℕ) : ℝ≥0) + l := by exact_mod_cast (Nat.sub_add_cancel hlk).symm
    have hlbx : (l : ℝ≥0) * b ≤ x := by
      refine le_trans ?_ hkx
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hlk) zero_le
    refine ⟨j, k - l, by omega, by omega, x - l * b, y - l * b, tsub_le_tsub_right hxy _, ?_, ?_,
      ?_, ?_, ?_⟩
    · rw [tsub_tsub_tsub_cancel_right hlbx]; exact hyx
    · rw [le_tsub_iff_right hlbx, ← add_mul, ← hkl]; exact hkx
    · rw [tsub_le_iff_right, ← add_mul, add_assoc, add_comm 1, ← add_assoc, ← hkl]; exact hyk
    · exact tsub_le_self.trans (hxy.trans (hyT.trans le_add_self))
    · rw [← hx, ← hy]; exact hnm
  set k : ℕ := ⌊(s : ℝ≥0) / b⌋₊ with hk
  have hkb : (k : ℝ≥0) * b ≤ s := by
    have := Nat.floor_le (zero_le : (0 : ℝ≥0) ≤ s / b)
    rw [le_div_iff₀ hb0] at this
    exact this
  have hsk : s < ((k : ℝ≥0) + 1) * b := by
    have := Nat.lt_floor_add_one ((s : ℝ≥0) / b)
    rw [div_lt_iff₀ hb0] at this
    exact this
  have hkT : k ≤ ⌊T / b⌋₊ := Nat.floor_le_floor (div_le_div_of_nonneg_right
    (hss'.trans hsT) hb0.le)
  have hs'le : s' ≤ s + 1 := tsub_le_iff_left.1 h1
  by_cases hcase : s' ≤ ((k : ℝ≥0) + 1) * b
  · exact key k s s' hkb hss' hcase h1 hsT hkT
      (by have := hL; linarith [hnorm])
  · rw [not_le] at hcase
    set p : ℝ≥0 := ((k : ℝ≥0) + 1) * b with hp
    have hsp : s ≤ p := hsk.le
    have hps' : p ≤ s' := hcase.le
    have htri : ‖W s' - W s‖ ≤ ‖W s' - W p‖ + ‖W p - W s‖ := by
      simpa using norm_add_le (W s' - W p) (W p - W s)
    by_cases hsplit : L / 2 ≤ ‖W p - W s‖
    · exact key k s p hkb hsp le_rfl
        (tsub_le_iff_left.2 (by calc p ≤ s' := hps'
              _ ≤ s + 1 := hs'le)) (hps'.trans hsT) hkT hsplit
    · have h2 : L / 2 ≤ ‖W s' - W p‖ := by
        rw [not_le] at hsplit; linarith
      refine key (k + 1) p s' (by rw [hp]; push_cast; exact le_rfl) hps' ?_
        (tsub_le_iff_left.2 (by calc s' ≤ s + 1 := hs'le
              _ ≤ p + 1 := add_le_add_left hsp 1)) hsT ?_ h2
      · push_cast
        calc s' ≤ s + 1 := hs'le
          _ ≤ p + b := add_le_add hsp hb1
          _ = _ := by rw [hp]; ring
      · have : ((k + 1 : ℕ) : ℝ≥0) * b ≤ T := by push_cast; exact hps'.trans hsT
        have : ((k + 1 : ℕ) : ℝ≥0) ≤ T / b := by rw [le_div_iff₀ hb0]; exact this
        exact Nat.le_floor this

end ElboimSly.Cyclic

end
