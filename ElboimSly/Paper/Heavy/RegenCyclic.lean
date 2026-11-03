/-
Copyright (c) 2026 Scott Armstrong and Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Ahmed Bou-Rabee
-/
module

public import ElboimSly.Paper.Heavy.Pieces
public import ElboimSly.Paper.Heavy.PiecesRegen
public import ElboimSly.Paper.Heavy.JumpShift
public import ElboimSly.Paper.Induction.RelaxedMeasRegen
public import ElboimSly.Foundations.Concentration.GeometricDet
public import ElboimSly.Foundations.Cyclic.CycRegenEnvAe
public import Mathlib

/-!
# The regenerated walk is a cyclic path

Pathwise consequences of tfast and heavyJ (supplement, hypotheses for `W`) and the pieces are cyclic paths.

`isCyclicPath_regenWalk`: if every environment `ν k` is good, then `regenWalk ν` is a cyclic path
(`IsCyclicPath`): right-continuous (`regenWalk_rlc`), `W 0 = 0`, and every discontinuity of `W`
is a discontinuity of a piece (shifted by the regeneration time `σ_j`, including the closing time
of the piece, where `W` and the piece both vanish), hence of `ℓ¹`-size `1`, and there are finitely
many in bounded intervals because `σ_j ≥ jβ`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace ElboimSly.Paper.Heavy

open ElboimSly ElboimSly.Paper ElboimSly.Cyclic

variable {d : ℕ} {β : ℝ} [Fact (0 < β)] {ν : ℕ → Measure (RingSpace d β)}

/-- Transfer of left-eventual properties along the shift `u ↦ a + u`. -/
theorem eventually_left_shift_iff {α : Type*} {f g : ℝ → α} {a r : ℝ} (hr : 0 < r)
    (hloc : ∀ u ∈ Icc (0 : ℝ) r, f (a + u) = g u) (Q : α → α → Prop) :
    (∀ᶠ u in 𝓝[<] (a + r), Q (f (a + r)) (f u)) ↔ ∀ᶠ u in 𝓝[<] r, Q (g r) (g u) := by
  constructor
  · intro h
    have h1 := (tendsto_add_nhdsLT a r).eventually h
    filter_upwards [h1, Ioo_mem_nhdsLT hr] with u hu hu0
    rw [hloc r ⟨hr.le, le_rfl⟩, hloc u ⟨hu0.1.le, hu0.2.le⟩] at hu
    exact hu
  · intro h
    have h1 := (tendsto_sub_nhdsLT a r).eventually h
    filter_upwards [h1, Ioo_mem_nhdsLT (show a < a + r by linarith)] with v hv hv0
    have hv1 : 0 ≤ v - a := by linarith [hv0.1]
    have hv2 : v - a ≤ r := by linarith [hv0.2]
    have e := hloc (v - a) ⟨hv1, hv2⟩
    rw [add_sub_cancel] at e
    rw [hloc r ⟨hr.le, le_rfl⟩, e]
    exact hv

theorem exists_piece_index {r : ℝ} (hr : 0 < r) :
    ∃ j, regenSigma ν j < ENNReal.ofReal r ∧ ENNReal.ofReal r ≤ regenSigma ν (j + 1) := by
  obtain ⟨h1, h2⟩ := regenCount_spec ν hr.le
  set k := regenCount ν r with hk
  rcases Nat.eq_zero_or_pos k with h0 | hpos
  · refine ⟨0, ?_, ?_⟩
    · have : regenSigma ν 0 = 0 := by simp [regenSigma]
      rw [this]; exact ENNReal.ofReal_pos.2 hr
    · rw [h0] at h2; exact h2.le
  · rcases h1.lt_or_eq with hlt | heq
    · exact ⟨k, hlt, h2.le⟩
    · refine ⟨k - 1, ?_, ?_⟩
      · have hk' : regenSigma ν (k - 1) < ⊤ := by
          refine lt_of_le_of_lt ((regenSigma_mono ν (Nat.sub_le k 1)).trans h1) ENNReal.ofReal_lt_top
        have := regenSigma_lt_succ hk'
        rw [Nat.sub_add_cancel hpos] at this
        exact this.trans_le h1
      · rw [Nat.sub_add_cancel hpos]; exact heq.ge

/-- On the `j`-th interval `[σ_j, σ_{j+1}]`, `W` is the `j`-th piece shifted by `σ_j`. -/
theorem regenWalk_eq_piece (hν : ∀ k, Good (ν k)) {j : ℕ} (hj : regenSigma ν j < ⊤) {x : ℝ}
    (hx : (regenSigma ν j).toReal ≤ x) (hx2 : ENNReal.ofReal x ≤ regenSigma ν (j + 1)) :
    regenWalk ν x = cycWalk (ν j) 0 0 (x - (regenSigma ν j).toReal) := by
  set a := (regenSigma ν j).toReal with ha
  have hu : 0 ≤ x - a := by linarith
  have hσ : ENNReal.ofReal a = regenSigma ν j := ENNReal.ofReal_toReal hj.ne
  have hut : ENNReal.ofReal (x - a) ≤ cycTreg (ν j) := by
    have e : ENNReal.ofReal x = regenSigma ν j + ENNReal.ofReal (x - a) := by
      rw [← hσ, ← ENNReal.ofReal_add ENNReal.toReal_nonneg hu]; congr 1; ring
    rw [e, regenSigma_succ] at hx2
    exact (ENNReal.add_le_add_iff_left hj.ne).1 hx2
  have := es6_pieces_b_walk hν hj hu hut
  rw [show a + (x - a) = x by ring] at this
  exact this

/-- Left-eventual properties of `W` at `r ∈ (σ_j, σ_{j+1}]` and of the `j`-th piece at `r - σ_j`
agree. -/
theorem regenWalk_left_iff (hν : ∀ k, Good (ν k)) {r : ℝ} {j : ℕ}
    (hlt : regenSigma ν j < ENNReal.ofReal r) (hle : ENNReal.ofReal r ≤ regenSigma ν (j + 1))
    (Q : (Fin d → ℤ) → (Fin d → ℤ) → Prop) :
    (∀ᶠ u in 𝓝[<] r, Q (regenWalk ν r) (regenWalk ν u)) ↔
      ∀ᶠ u in 𝓝[<] (r - (regenSigma ν j).toReal),
        Q (cycWalk (ν j) 0 0 (r - (regenSigma ν j).toReal)) (cycWalk (ν j) 0 0 u) := by
  have hjfin : regenSigma ν j < ⊤ := hlt.trans ENNReal.ofReal_lt_top
  set a := (regenSigma ν j).toReal with ha
  have hσ : ENNReal.ofReal a = regenSigma ν j := ENNReal.ofReal_toReal hjfin.ne
  have har : a < r := by
    have := (ENNReal.ofReal_lt_ofReal_iff' ).1 (hσ ▸ hlt)
    exact this.1
  have hr' : 0 < r - a := by linarith
  have hl : ∀ u ∈ Icc (0 : ℝ) (r - a), regenWalk ν (a + u) = cycWalk (ν j) 0 0 u := by
    intro u hu
    have hu' : a + u ≤ r := by linarith [hu.2]
    have := regenWalk_eq_piece hν hjfin (x := a + u) (by linarith [hu.1])
      ((ENNReal.ofReal_le_ofReal hu').trans hle)
    rw [this, add_sub_cancel_left]
  have := eventually_left_shift_iff (f := regenWalk ν) (g := fun u => cycWalk (ν j) 0 0 u) hr' hl Q
  rwa [show a + (r - a) = r by ring] at this

theorem sigma_index_lt {j : ℕ} {r T : ℝ} (hlt : regenSigma ν j < ENNReal.ofReal r) (hrT : r ≤ T) :
    j < ⌈T / β⌉₊ := by
  have hβ : 0 < β := Fact.out
  have h1 := (Cyclic.regenSigma_ge ν j).trans_lt hlt
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg j),
    ENNReal.ofReal_lt_ofReal_iff'] at h1
  refine Nat.lt_ceil.2 ?_
  rw [lt_div_iff₀ hβ]
  linarith [h1.1]

/-- The pieces are cyclic paths; Pathwise consequences of tfast and heavyJ hypotheses for `W`.  For good
environments, the regenerated walk is a cyclic path. -/
theorem isCyclicPath_regenWalk (hν : ∀ k, Good (ν k)) : IsCyclicPath (regenWalk ν) where
  zero := by
    have h0 : regenSigma ν 0 = 0 := by simp [regenSigma]
    have := regenWalk_eq_piece hν (j := 0) (x := 0) (by rw [h0]; exact ENNReal.zero_lt_top)
      (by simp [h0]) (by simp)
    rw [this]
    simpa [h0] using cycWalk_zero (hν 0) 0 0
  rc s hs := by
    obtain ⟨ε, hε, h⟩ := regenWalk_rlc hν hs
    exact mem_nhdsGE_iff_exists_Ico_subset.2 ⟨s + ε, by simpa using hε, fun x hx => h x hx⟩
  fin T := by
    classical
    have hsub : cycJumpSet (regenWalk ν) ∩ Iic T ⊆ ⋃ j ∈ Finset.range ⌈T / β⌉₊,
        (fun u => (regenSigma ν j).toReal + u) ''
          (cycJumpSet (fun s : ℝ => cycWalk (ν j) 0 0 s) ∩ Iic T) := by
      rintro r ⟨⟨hr0, hrn⟩, hrT⟩
      have hrT' : r ≤ T := hrT
      obtain ⟨j, hlt, hle⟩ := exists_piece_index (ν := ν) hr0
      have hjfin : regenSigma ν j < ⊤ := hlt.trans ENNReal.ofReal_lt_top
      have hj := sigma_index_lt hlt hrT'
      have hσ0 : 0 ≤ (regenSigma ν j).toReal := ENNReal.toReal_nonneg
      have hlt' : (regenSigma ν j).toReal < r := by
        have := (ENNReal.ofReal_lt_ofReal_iff' ).1
          ((ENNReal.ofReal_toReal hjfin.ne).symm ▸ hlt)
        exact this.1
      refine mem_iUnion₂.2 ⟨j, Finset.mem_range.2 hj, r - (regenSigma ν j).toReal, ⟨?_, ?_⟩, by ring⟩
      · refine ⟨by linarith, fun hev => hrn ?_⟩
        exact (regenWalk_left_iff hν hlt hle (fun x y => y = x)).2 hev
      · show r - (regenSigma ν j).toReal ≤ T
        linarith
    refine Set.Finite.subset ?_ hsub
    exact Set.Finite.biUnion (Finset.finite_toSet _) fun j _ =>
      ((isCyclicPath_cycWalk (hν j)).fin T).image _
  jump_size r hr := by
    obtain ⟨hr0, hrn⟩ := hr
    obtain ⟨j, hlt, hle⟩ := exists_piece_index (ν := ν) hr0
    have hjfin : regenSigma ν j < ⊤ := hlt.trans ENNReal.ofReal_lt_top
    have hlt' : (regenSigma ν j).toReal < r := by
      have := (ENNReal.ofReal_lt_ofReal_iff' ).1
        ((ENNReal.ofReal_toReal hjfin.ne).symm ▸ hlt)
      exact this.1
    have hmem : r - (regenSigma ν j).toReal ∈
        cycJumpSet (fun s : ℝ => cycWalk (ν j) 0 0 s) := by
      refine ⟨by linarith, fun hev => hrn ?_⟩
      exact (regenWalk_left_iff hν hlt hle (fun x y => y = x)).2 hev
    have := (isCyclicPath_cycWalk (hν j)).jump_size _ hmem
    exact (regenWalk_left_iff hν hlt hle (fun x y => ∑ i, |x i - y i| = 1)).2 this

end ElboimSly.Paper.Heavy
