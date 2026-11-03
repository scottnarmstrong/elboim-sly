/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Foundations.Cyclic.CycFastInc
public import Mathlib

/-!
# ES22 Claim 2.3, Step 3: from `t_fast(L) ≤ t` to a unit window of one piece

ES22 Claim 2.3, Steps 0 and 3 (`tfast_mem_window`).
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ElboimSly.Cyclic

open ElboimSly.Interchange

variable {d : ℕ} {β : ℝ} [Fact (0 < β)]

/-- The closing times of a good slice are `⊤` or a positive integer multiple of `β`. -/
theorem cycTreg_cases {ν : Measure (RingSpace d β)} :
    ElboimSly.cycTreg ν = ⊤ ∨ ∃ n : ℕ, 1 ≤ n ∧ ElboimSly.cycWalk ν 0 0 ((n : ℝ) * β) = 0 ∧
      ElboimSly.cycTreg ν = (((n : ℝ≥0) * β.toNNReal : ℝ≥0) : ℝ≥0∞) := by
  by_cases h : ElboimSly.cycTreg ν = ⊤
  · exact Or.inl h
  · obtain ⟨n, hn, h0, he⟩ := exists_cycTreg_eq (lt_top_iff_ne_top.2 h)
    refine Or.inr ⟨n, hn, h0, ?_⟩
    rw [he]
    have hβ : 0 < β := Fact.out
    show ENNReal.ofReal _ = _
    rw [ENNReal.ofReal, Real.toNNReal_mul (by positivity), Real.toNNReal_natCast]

/-- **ES22 Claim 2.3, Steps 0 and 3.** For a good environment, `t_fast(L) ≤ t` forces a large
deviation in a unit window of one of the first `⌊t/β⌋ + 1` pieces. -/
theorem tfast_mem_window {ν : Measure (ℕ × RingSpace d β)} (hν : CycGood ν) (hβ : 1 ≤ β)
    {L t : ℝ} (hL : 1 ≤ L) (ht : 1 ≤ t)
    (h : ElboimSly.cycTfast (fun k => cycSlice k ν) L ≤ ENNReal.ofReal t) :
    ∃ j m i : ℕ, j < ⌊t.toNNReal / β.toNNReal⌋₊ + 1 ∧ m < ⌊t.toNNReal / β.toNNReal⌋₊ + 1 ∧
      i < min ⌊β.toNNReal⌋₊ ⌊t.toNNReal⌋₊ + 1 ∧
      shiftTraj ((m : ℝ≥0) * β.toNNReal + i) (cycSlice j ν) ∈ farSet (d := d) (L / 4) 2 := by
  have hβpos : 0 < β := Fact.out
  set b : ℝ≥0 := β.toNNReal with hb
  have hb0 : 0 < b := Real.toNNReal_pos.2 hβpos
  have hb1 : 1 ≤ b := by
    rw [hb, ← Real.toNNReal_one]; exact Real.toNNReal_le_toNNReal hβ
  set t' : ℝ≥0 := t.toNNReal with ht'
  have ht0 : 0 ≤ t := by linarith
  obtain ⟨s, s', hss', hs'T, h1, hnorm⟩ := tfast_pair (by linarith) ht0
    (regenWalk_rc hν) h
  have hs'T' : s' ≤ t' := by
    rw [← NNReal.coe_le_coe, ht', Real.coe_toNNReal _ ht0]; exact hs'T
  -- the glued description
  set τ : ℕ → ℝ≥0∞ := fun k => ElboimSly.cycTreg (cycSlice k ν) with hτdef
  set w : ℕ → ℝ≥0 → Fin d → ℤ := fun k u => ElboimSly.cycWalk (cycSlice k ν) 0 0 (u : ℝ) with hwdef
  have hτ : ∀ i, τ i = ⊤ ∨ ∃ n : ℕ, 1 ≤ n ∧ τ i = (((n : ℝ≥0) * b : ℝ≥0) : ℝ≥0∞) := by
    intro i
    rcases cycTreg_cases (ν := cycSlice i ν) with h | ⟨n, hn, -, h⟩
    · exact Or.inl h
    · exact Or.inr ⟨n, hn, h⟩
  have hw0 : ∀ i, w i 0 = 0 := fun i => by
    simp only [hwdef, NNReal.coe_zero]
    exact cycWalk_zero (hν i) 0 0
  have hwτ : ∀ i (h : τ i < ⊤), w i (τ i).toNNReal = 0 := by
    intro i hi
    rcases cycTreg_cases (ν := cycSlice i ν) with h | ⟨n, hn, h0, h⟩
    · exact absurd h hi.ne
    · simp only [hwdef, hτdef] at hi ⊢
      rw [h, ENNReal.toNNReal_coe]
      push_cast
      rw [show (b : ℝ) = β from Real.coe_toNNReal _ hβpos.le]
      exact h0
  have hWglue : ∀ u : ℝ≥0, ElboimSly.regenWalk (fun k => cycSlice k ν) (u : ℝ) =
      gluedWalk (partialSums τ) w u := fun u => (gluedWalk_eq_regenWalk _ u).symm
  have hwin := glued_window hb0 hτ hw0 hwτ
  have hwin' : ∀ k : ℕ, ∃ j l : ℕ, j ≤ l ∧ l ≤ k ∧ ∀ u : ℝ≥0, (k : ℝ≥0) * b ≤ u →
      u ≤ ((k : ℝ≥0) + 1) * b →
      ElboimSly.regenWalk (fun k => cycSlice k ν) (u : ℝ) = w j (u - l * b) := by
    intro k
    obtain ⟨j, l, hjl, hlk, hW⟩ := hwin k
    exact ⟨j, l, hjl, hlk, fun u h1 h2 => by rw [hWglue]; exact hW u h1 h2⟩
  obtain ⟨j, m, hj, hm, u, u', huu', hu'u, hmu, hu'm, huT, hnorm'⟩ :=
    window_pairs (W := fun u => ElboimSly.regenWalk (fun k => cycSlice k ν) (u : ℝ)) hb1 hwin'
      (T := t') (L := L) (by linarith) hss' hs'T' h1 hnorm
  obtain ⟨i, hiB, hiT, x, hx, hnx⟩ := cover_unit (w := w j) (a₀ := (m : ℝ≥0) * b) (B := b)
    (T := t') (L := L / 2) huu' hu'u hmu (by rw [add_mul, one_mul] at hu'm; exact hu'm) huT hnorm'
  refine ⟨j, m, i, hj, hm, by omega, ?_⟩
  -- the check time
  set a : ℝ≥0 := (m : ℝ≥0) * b + i with ha
  have hwj : ∀ y : ℝ≥0, w j y = trajProc (cycSlice j ν) 0 0 y := fun y =>
    cycWalk_eq_trajProc (hν j) 0 0 y
  have hrc : ∀ s : ℝ≥0, ∀ᶠ u : ℝ≥0 in 𝓝[≥] s,
      shiftTraj a (cycSlice j ν) u = shiftTraj a (cycSlice j ν) s := by
    intro s
    have h := (tendsto_add_nhdsGE a s).eventually (cycWalk_slice_rc hν j (a + s))
    filter_upwards [h] with u hu
    simp only [shiftTraj]
    rw [← cycWalk_eq_trajProc (hν j), ← cycWalk_eq_trajProc (hν j), ← cycWalk_eq_trajProc (hν j)]
    simp only [NNReal.coe_add] at hu ⊢
    rw [hu]
  have hP : L / 4 ≤ ‖shiftTraj a (cycSlice j ν) x‖ := by
    simp only [shiftTraj]
    rw [← hwj, ← hwj]
    have : L / 2 / 2 = L / 4 := by ring
    rw [← this]
    exact hnx
  obtain ⟨q, hq, hRq⟩ := exists_check_of_rc hrc hx (P := fun v => L / 4 ≤ ‖v‖) hP
  exact mem_iUnion₂.2 ⟨q, hq, hRq⟩

end ElboimSly.Cyclic

end
